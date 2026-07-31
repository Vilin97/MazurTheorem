#!/usr/bin/env python3
"""Reject changes to challenge contracts that were published in a base revision."""

from __future__ import annotations

import argparse
import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
PROGRAM_RELATIVE_PATH = Path("coordination/program.json")
PROGRAM_PATH = REPOSITORY_ROOT / PROGRAM_RELATIVE_PATH
IMMUTABLE_CHALLENGE_FIELDS = (
    "module",
    "file",
    "declaration",
    "signature",
    "imports",
    "informal",
    "destination_module",
    "destination_declaration",
)


def git(*arguments: str) -> subprocess.CompletedProcess[str]:
    """Run Git in the repository without invoking a shell."""
    return subprocess.run(
        ("git", *arguments),
        cwd=REPOSITORY_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def load_json_object(raw: str, source: str) -> dict[str, Any]:
    """Decode one program ledger and require a top-level object."""
    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"{source} has duplicate JSON key {key!r}")
            result[key] = value
        return result

    try:
        value = json.loads(raw, object_pairs_hook=reject_duplicates)
    except (json.JSONDecodeError, ValueError) as error:
        raise ValueError(f"{source} is not valid JSON: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"{source} must contain a JSON object")
    return value


def load_base_program(base: str) -> dict[str, Any] | None:
    """Read the base ledger, returning ``None`` when that revision predates it."""
    revision = git("rev-parse", "--verify", f"{base}^{{commit}}")
    if revision.returncode != 0:
        detail = revision.stderr.strip() or "revision not found"
        raise ValueError(f"cannot resolve base revision {base!r}: {detail}")
    object_name = f"{base}:{PROGRAM_RELATIVE_PATH.as_posix()}"
    if git("cat-file", "-e", object_name).returncode != 0:
        return None
    result = git("show", object_name)
    if result.returncode != 0:
        detail = result.stderr.strip() or "git show failed"
        raise ValueError(f"cannot read {object_name}: {detail}")
    return load_json_object(result.stdout, object_name)


def challenge_nodes(program: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Index challenge objects by their durable DAG node IDs."""
    nodes = program.get("nodes", [])
    if not isinstance(nodes, list):
        raise ValueError("program.nodes must be a list")
    indexed: dict[str, dict[str, Any]] = {}
    for node in nodes:
        if not isinstance(node, dict) or not isinstance(node.get("challenge"), dict):
            continue
        node_id = node.get("id")
        if not isinstance(node_id, str) or not node_id:
            raise ValueError("every challenge node must have a nonempty string id")
        if node_id in indexed:
            raise ValueError(f"duplicate challenge node id {node_id}")
        indexed[node_id] = node["challenge"]
    return indexed


def node_ids(program: dict[str, Any]) -> set[str]:
    """Return every durable DAG node ID, rejecting malformed node entries."""
    nodes = program.get("nodes", [])
    if not isinstance(nodes, list):
        raise ValueError("program.nodes must be a list")
    identifiers: set[str] = set()
    for node in nodes:
        if not isinstance(node, dict):
            raise ValueError("every program node must be an object")
        node_id = node.get("id")
        if not isinstance(node_id, str) or not node_id:
            raise ValueError("every program node must have a nonempty string id")
        if node_id in identifiers:
            raise ValueError(f"duplicate program node id {node_id}")
        identifiers.add(node_id)
    return identifiers


def rendered(value: object) -> str:
    """Render an immutable value deterministically for diagnostics."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def compare_programs(
    base_program: dict[str, Any], current_program: dict[str, Any]
) -> list[str]:
    """Return deterministic diagnostics for removed or mutated base contracts."""
    base_challenges = challenge_nodes(base_program)
    current_challenges = challenge_nodes(current_program)
    base_node_ids = node_ids(base_program)
    current_node_ids = node_ids(current_program)
    current_ids_by_declaration = {
        challenge.get("declaration"): node_id
        for node_id, challenge in current_challenges.items()
        if isinstance(challenge.get("declaration"), str)
    }
    errors: list[str] = []
    for node_id in sorted(base_node_ids - current_node_ids):
        errors.append(f"{node_id}: immutable DAG node id was removed or renamed")
    for node_id in sorted(base_challenges):
        base_challenge = base_challenges[node_id]
        current_challenge = current_challenges.get(node_id)
        if current_challenge is None:
            moved_to = current_ids_by_declaration.get(base_challenge.get("declaration"))
            if moved_to is None:
                errors.append(f"{node_id}: immutable challenge node was removed")
            else:
                errors.append(
                    f"{node_id}: immutable challenge node id changed to {moved_to}"
                )
            continue
        for field in IMMUTABLE_CHALLENGE_FIELDS:
            before = base_challenge.get(field)
            after = current_challenge.get(field)
            if before != after:
                errors.append(
                    f"{node_id}: immutable challenge.{field} changed "
                    f"from {rendered(before)} to {rendered(after)}"
                )
        base_consumers = base_challenge.get("consumer_declarations", [])
        current_consumers = current_challenge.get("consumer_declarations", [])
        if isinstance(base_consumers, list) and isinstance(current_consumers, list):
            if current_consumers[: len(base_consumers)] != base_consumers:
                errors.append(
                    f"{node_id}: consumer_declarations must retain the published "
                    "list as an exact prefix"
                )
    return errors


def run_self_test() -> bool:
    """Exercise every immutable field, node removal, ID changes, and lifecycle edits."""
    challenge = {
        "claimable": True,
        "module": "Challenge.Example",
        "file": "Challenge/Example.lean",
        "declaration": "MazurTheorem.Challenge.example",
        "signature": "theorem example : True := sorry",
        "imports": ["Mathlib"],
        "informal": "A stable example.",
        "destination_module": "MazurTorsion.Example",
        "destination_declaration": "MazurTorsion.example",
        "consumer_declarations": ["MazurTorsion.useExample"],
    }
    base = {"nodes": [{"id": "MT-EXAMPLE", "challenge": challenge}]}
    failures: list[str] = []
    for field in IMMUTABLE_CHALLENGE_FIELDS:
        current = copy.deepcopy(base)
        current["nodes"][0]["challenge"][field] = f"changed-{field}"
        if not compare_programs(base, current):
            failures.append(f"mutation of {field} was accepted")
    if not compare_programs(base, {"nodes": []}):
        failures.append("challenge removal was accepted")
    moved = copy.deepcopy(base)
    moved["nodes"][0]["id"] = "MT-MOVED"
    if not compare_programs(base, moved):
        failures.append("challenge node ID change was accepted")
    lifecycle = copy.deepcopy(base)
    lifecycle["nodes"][0]["challenge"]["claimable"] = False
    lifecycle["nodes"][0]["challenge"]["consumer_declarations"].append(
        "MazurTorsion.useExampleAgain"
    )
    if compare_programs(base, lifecycle):
        failures.append("allowed lifecycle/consumer metadata edits were rejected")
    removed_consumer = copy.deepcopy(base)
    removed_consumer["nodes"][0]["challenge"]["consumer_declarations"] = []
    if not compare_programs(base, removed_consumer):
        failures.append("published consumer removal was accepted")
    reordered_consumers = copy.deepcopy(base)
    reordered_consumers["nodes"][0]["challenge"]["consumer_declarations"] = [
        "MazurTorsion.useExampleAgain",
        "MazurTorsion.useExample",
    ]
    if not compare_programs(base, reordered_consumers):
        failures.append("published consumer prefix mutation was accepted")
    base_with_plain_node = copy.deepcopy(base)
    base_with_plain_node["nodes"].append({"id": "MT-PLAIN"})
    if not compare_programs(base_with_plain_node, base):
        failures.append("non-challenge DAG node removal was accepted")
    for failure in failures:
        print(f"self-test failed: {failure}", file=sys.stderr)
    if failures:
        return False
    print("Challenge immutability self-test passed.")
    return True


def parse_arguments() -> argparse.Namespace:
    """Parse command-line options."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--base",
        default="origin/main",
        help="Git revision whose published challenge contracts are immutable",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run deterministic in-memory mutation checks",
    )
    return parser.parse_args()


def main() -> int:
    """Compare the working ledger with its published base contracts."""
    arguments = parse_arguments()
    if arguments.self_test:
        return 0 if run_self_test() else 1
    try:
        base_program = load_base_program(arguments.base)
        current_program = load_json_object(
            PROGRAM_PATH.read_text(encoding="utf-8"),
            PROGRAM_RELATIVE_PATH.as_posix(),
        )
        if base_program is None:
            print(
                f"Challenge immutability passed: {arguments.base} has no "
                f"{PROGRAM_RELATIVE_PATH}; nothing to compare."
            )
            return 0
        errors = compare_programs(base_program, current_program)
    except (OSError, ValueError) as error:
        print(f"Challenge immutability check failed: {error}", file=sys.stderr)
        return 2
    if errors:
        print("Challenge immutability check failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    print(
        f"Challenge immutability passed: {len(challenge_nodes(base_program))} "
        f"published contract(s) unchanged from {arguments.base}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
