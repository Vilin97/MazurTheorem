#!/usr/bin/env python3
"""Synchronize the Verso roadmap chapters and public programme projection."""

from __future__ import annotations

import argparse
import difflib
import json
import sys
import textwrap
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
PROGRAM_PATH = REPOSITORY_ROOT / "coordination" / "program.json"
GENERATED_PROGRAM_PATH = REPOSITORY_ROOT / "site" / "generated" / "program.json"
CHAPTER_ROOT = REPOSITORY_ROOT / "blueprint" / "MazurBlueprint" / "Chapters"

CHAPTER_NAMES = {
    "integrated_baseline": "IntegratedBaseline.lean",
    "finite_endpoints": "FiniteEndpoints.lean",
    "shared_geometry": "SharedGeometry.lean",
    "prime_infrastructure": "PrimeInfrastructure.lean",
    "prime_argument": "PrimeArgument.lean",
    "integration": "Integration.lean",
}

LEAN_PREAMBLE = """import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal
"""

STAGE_OPTIONS = {
    "shared_geometry": ("set_option maxRecDepth 10000",),
}

WRAPPER = textwrap.TextWrapper(
    width=88,
    break_long_words=False,
    break_on_hyphens=False,
)


class SyncError(ValueError):
    """The canonical programme cannot be rendered safely."""


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Decode JSON objects while rejecting ambiguous duplicate keys."""
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SyncError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def require_object(value: object, location: str) -> dict[str, Any]:
    """Return ``value`` as an object or raise a contextual error."""
    if not isinstance(value, dict):
        raise SyncError(f"{location} must be an object")
    return value


def require_list(value: object, location: str) -> list[Any]:
    """Return ``value`` as a list or raise a contextual error."""
    if not isinstance(value, list):
        raise SyncError(f"{location} must be a list")
    return value


def require_string(mapping: dict[str, Any], key: str, location: str) -> str:
    """Read a required, nonempty string field."""
    value = mapping.get(key)
    if not isinstance(value, str) or not value.strip():
        raise SyncError(f"{location}.{key} must be a nonempty string")
    return value


def require_positive_int(mapping: dict[str, Any], key: str, location: str) -> int:
    """Read a required positive integer field, excluding booleans."""
    value = mapping.get(key)
    if type(value) is not int or value <= 0:
        raise SyncError(f"{location}.{key} must be a positive integer")
    return value


def load_program() -> tuple[dict[str, Any], bytes]:
    """Load the canonical ledger once, preserving its original bytes for copying."""
    try:
        raw = PROGRAM_PATH.read_bytes()
        decoded = raw.decode("utf-8")
        value = json.loads(decoded, object_pairs_hook=reject_duplicate_keys)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, SyncError) as error:
        raise SyncError(f"cannot read {PROGRAM_PATH.relative_to(REPOSITORY_ROOT)}: {error}") from error
    return require_object(value, "program.json"), raw


def normalized_prose(value: str) -> str:
    """Normalize JSON prose to one deterministic stream of words."""
    return " ".join(value.split())


def concise_summary(value: str) -> str:
    """Use the first complete sentence of the canonical node summary."""
    summary = normalized_prose(value)
    first, separator, _remainder = summary.partition(". ")
    return f"{first}." if separator else summary


def escaped_prose(value: str) -> str:
    """Escape Verso Markdown punctuation outside existing inline-code spans."""
    chunks = normalized_prose(value).split("`")
    if len(chunks) % 2 == 0:
        raise SyncError("roadmap prose contains an unmatched inline-code delimiter")
    special = frozenset("\\_*[]{}<>")
    for index in range(0, len(chunks), 2):
        chunks[index] = "".join(
            f"\\{character}" if character in special else character
            for character in chunks[index]
        )
    return "`".join(chunks)


def wrapped(value: str, *, initial: str = "", subsequent: str = "") -> list[str]:
    """Wrap prose without splitting long Lean names or hyphenated identifiers."""
    wrapper = WRAPPER.__class__(
        width=WRAPPER.width,
        initial_indent=initial,
        subsequent_indent=subsequent,
        break_long_words=WRAPPER.break_long_words,
        break_on_hyphens=WRAPPER.break_on_hyphens,
    )
    return wrapper.wrap(normalized_prose(value))


def lean_string(value: str) -> str:
    """Render an ordinary JSON string as a Lean string literal."""
    return json.dumps(value, ensure_ascii=False)


def metadata_tag(value: str) -> str:
    """Match the Blueprint's established human-readable tag spelling."""
    if value == "tauceti":
        return "tau-ceti"
    return value.replace("_", "-")


def render_artifacts(node: dict[str, Any], node_id: str) -> list[str]:
    """Render every canonical artifact field required by the roadmap."""
    raw_artifacts = node.get("artifacts", [])
    artifacts = require_list(raw_artifacts, f"node {node_id}.artifacts")
    if not artifacts:
        return []

    lines = ["*Canonical artifacts:*", ""]
    for index, raw_artifact in enumerate(artifacts, start=1):
        location = f"node {node_id}.artifacts[{index}]"
        artifact = require_object(raw_artifact, location)
        kind = require_string(artifact, "kind", location)
        state = require_string(artifact, "state", location)
        name = require_string(artifact, "name", location)
        description = require_string(artifact, "description", location)
        lines.extend(
            wrapped(
                f"`{kind}` (`{state}`): `{name}`",
                initial="* ",
                subsequent="  ",
            )
        )
        lines.extend(wrapped(escaped_prose(description), initial="  ", subsequent="  "))
    lines.append("")
    return lines


def render_node(node: dict[str, Any]) -> list[str]:
    """Render exactly one Verso theorem block for one programme node."""
    node_id = require_string(node, "id", "node")
    location = f"node {node_id}"
    title = require_string(node, "title", location)
    stage = require_string(node, "stage", location)
    kind = require_string(node, "kind", location)
    status = require_string(node, "status", location)
    readiness = require_string(node, "readiness", location)
    risk = require_string(node, "risk", location)
    backend = require_string(node, "backend", location)
    summary = require_string(node, "summary", location)
    weight = require_positive_int(node, "weight_points", location)

    raw_dependencies = require_list(node.get("depends_on"), f"{location}.depends_on")
    dependencies: list[str] = []
    for index, dependency in enumerate(raw_dependencies, start=1):
        if not isinstance(dependency, str) or not dependency:
            raise SyncError(f"{location}.depends_on[{index}] must be a nonempty string")
        dependencies.append(dependency)

    tags = ", ".join(
        metadata_tag(value) for value in (kind, status, readiness, backend)
    )
    metadata = [f"(parent := {lean_string(stage)})"]
    if dependencies:
        metadata.append(f"(uses := {lean_string(', '.join(dependencies))})")
    metadata.append(f"(tags := {lean_string(tags)})")

    lines = [f":::theorem {lean_string(node_id)} {' '.join(metadata)}"]
    lines.extend(wrapped(f"*{escaped_prose(title)}.*"))
    lines.append("")
    lines.extend(
        wrapped(
            f"*Status:* `{status}`; *readiness:* `{readiness}`; *kind:* `{kind}`; "
            f"*backend:* `{backend}`; *risk:* `{risk}`; *weight:* {weight} points."
        )
    )
    lines.append("")
    lines.extend(wrapped(f"*Summary:* {escaped_prose(concise_summary(summary))}"))
    lines.append("")
    lines.extend(render_artifacts(node, node_id))
    lines.append(":::")
    lines.append("")
    return lines


def validate_program(
    program: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    """Validate the fields used by generation and group nodes by canonical stage order."""
    raw_stages = require_list(program.get("stages"), "program.stages")
    raw_nodes = require_list(program.get("nodes"), "program.nodes")
    if len(raw_stages) != len(CHAPTER_NAMES):
        raise SyncError(
            f"program.stages has {len(raw_stages)} entries; expected {len(CHAPTER_NAMES)}"
        )

    stages: list[dict[str, Any]] = []
    stage_ids: set[str] = set()
    for index, raw_stage in enumerate(raw_stages, start=1):
        location = f"program.stages[{index}]"
        stage = require_object(raw_stage, location)
        stage_id = require_string(stage, "id", location)
        require_string(stage, "title", location)
        require_string(stage, "summary", location)
        require_positive_int(stage, "weight_points", location)
        if stage_id in stage_ids:
            raise SyncError(f"duplicate stage id {stage_id!r}")
        if stage_id not in CHAPTER_NAMES:
            raise SyncError(f"stage {stage_id!r} has no canonical chapter filename")
        stage_ids.add(stage_id)
        stages.append(stage)
    if stage_ids != set(CHAPTER_NAMES):
        missing = ", ".join(sorted(set(CHAPTER_NAMES) - stage_ids))
        raise SyncError(f"program.stages omits canonical stages: {missing}")

    nodes_by_stage = {stage_id: [] for stage_id in stage_ids}
    node_ids: set[str] = set()
    nodes: list[dict[str, Any]] = []
    for index, raw_node in enumerate(raw_nodes, start=1):
        location = f"program.nodes[{index}]"
        node = require_object(raw_node, location)
        node_id = require_string(node, "id", location)
        stage_id = require_string(node, "stage", f"node {node_id}")
        if node_id in node_ids:
            raise SyncError(f"duplicate node id {node_id!r}")
        if stage_id not in nodes_by_stage:
            raise SyncError(f"node {node_id} has unknown stage {stage_id!r}")
        node_ids.add(node_id)
        nodes.append(node)
        nodes_by_stage[stage_id].append(node)

    for node in nodes:
        node_id = require_string(node, "id", "node")
        dependencies = require_list(node.get("depends_on"), f"node {node_id}.depends_on")
        unknown = [dependency for dependency in dependencies if dependency not in node_ids]
        if unknown:
            raise SyncError(f"node {node_id} has unknown dependencies: {', '.join(unknown)}")
    return stages, nodes_by_stage


def render_chapter(
    stage: dict[str, Any],
    nodes: list[dict[str, Any]],
    chapter_number: int,
) -> bytes:
    """Render one complete Lean/Verso chapter."""
    stage_id = require_string(stage, "id", "stage")
    title = require_string(stage, "title", f"stage {stage_id}")
    summary = require_string(stage, "summary", f"stage {stage_id}")
    weight = require_positive_int(stage, "weight_points", f"stage {stage_id}")

    lines = LEAN_PREAMBLE.rstrip().splitlines()
    options = STAGE_OPTIONS.get(stage_id, ())
    if options:
        lines.extend(("", *options))
    lines.extend(("", f'#doc (Manual) {lean_string(f"{chapter_number:02d} — {title}")} =>', ""))
    lines.append(f":::group {lean_string(stage_id)}")
    lines.extend(wrapped(f"{escaped_prose(summary)} Stage weight: {weight} points."))
    lines.extend((":::", ""))
    for node in nodes:
        lines.extend(render_node(node))
    return ("\n".join(lines).rstrip() + "\n").encode("utf-8")


def expected_outputs(program: dict[str, Any], raw_program: bytes) -> dict[Path, bytes]:
    """Compute every generated file without consulting its current contents."""
    stages, nodes_by_stage = validate_program(program)
    outputs: dict[Path, bytes] = {}
    for chapter_number, stage in enumerate(stages, start=1):
        stage_id = require_string(stage, "id", "stage")
        path = CHAPTER_ROOT / CHAPTER_NAMES[stage_id]
        outputs[path] = render_chapter(stage, nodes_by_stage[stage_id], chapter_number)
    outputs[GENERATED_PROGRAM_PATH] = raw_program
    return outputs


def display_path(path: Path) -> str:
    """Return a stable repository-relative path for diagnostics."""
    return path.relative_to(REPOSITORY_ROOT).as_posix()


def print_diff(path: Path, current: bytes, expected: bytes) -> None:
    """Print a unified UTF-8 diff for one stale generated file."""
    relative = display_path(path)
    current_text = current.decode("utf-8", errors="replace").splitlines(keepends=True)
    expected_text = expected.decode("utf-8", errors="replace").splitlines(keepends=True)
    sys.stderr.writelines(
        difflib.unified_diff(
            current_text,
            expected_text,
            fromfile=f"{relative} (current)",
            tofile=f"{relative} (generated)",
        )
    )


def unexpected_chapters(expected: set[Path]) -> list[Path]:
    """Find chapter files not represented by one canonical programme stage."""
    actual = set(CHAPTER_ROOT.glob("*.lean")) if CHAPTER_ROOT.is_dir() else set()
    expected_chapters = {path for path in expected if path.parent == CHAPTER_ROOT}
    return sorted(actual - expected_chapters)


def check(outputs: dict[Path, bytes]) -> int:
    """Fail with diffs when any generated output is stale or missing."""
    stale: list[Path] = []
    for path, expected in outputs.items():
        try:
            current = path.read_bytes()
        except FileNotFoundError:
            current = b""
        except OSError as error:
            raise SyncError(f"cannot read {display_path(path)}: {error}") from error
        if current != expected:
            stale.append(path)
            print_diff(path, current, expected)

    extras = unexpected_chapters(set(outputs))
    if stale or extras:
        print("Roadmap documentation is stale.", file=sys.stderr)
        for path in stale:
            print(f"  regenerate {display_path(path)}", file=sys.stderr)
        for path in extras:
            print(f"  unexpected chapter {display_path(path)}", file=sys.stderr)
        print("Run: python3 scripts/sync_roadmap_docs.py", file=sys.stderr)
        return 1

    print(
        "Roadmap documentation is synchronized: six Verso chapters and the "
        "byte-identical site programme."
    )
    return 0


def write(outputs: dict[Path, bytes]) -> int:
    """Write stale outputs and leave already-current files untouched."""
    extras = unexpected_chapters(set(outputs))
    if extras:
        rendered = ", ".join(display_path(path) for path in extras)
        raise SyncError(f"refusing to overwrite around unexpected chapter files: {rendered}")

    changed: list[Path] = []
    for path, expected in outputs.items():
        current = path.read_bytes() if path.is_file() else None
        if current == expected:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(expected)
        changed.append(path)

    if changed:
        print("Updated roadmap documentation:")
        for path in changed:
            print(f"  {display_path(path)}")
    else:
        print("Roadmap documentation was already synchronized.")
    return 0


def parse_arguments() -> argparse.Namespace:
    """Parse command-line options."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="report generated-file diffs without writing",
    )
    return parser.parse_args()


def main() -> int:
    """Synchronize or check every canonical roadmap projection."""
    arguments = parse_arguments()
    try:
        program, raw_program = load_program()
        outputs = expected_outputs(program, raw_program)
        return check(outputs) if arguments.check else write(outputs)
    except SyncError as error:
        print(f"Roadmap synchronization failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
