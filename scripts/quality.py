#!/usr/bin/env python3
"""Validate the Mazur crowdsourcing ledger and Lean source boundaries."""

from __future__ import annotations

import json
import re
import sys
import tomllib
from collections import defaultdict
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
PROGRAM_PATH = REPOSITORY_ROOT / "coordination" / "program.json"
CHALLENGE_ROOTS = (
    REPOSITORY_ROOT / "Challenge",
    REPOSITORY_ROOT / "upstream" / "tauceti" / "MazurTauCetiChallenge",
)
CHALLENGE_AGGREGATORS = (
    REPOSITORY_ROOT / "Challenge.lean",
    REPOSITORY_ROOT / "upstream" / "tauceti" / "MazurTauCetiChallenge.lean",
)
TAUCETI_CONTRACT_ROOT = REPOSITORY_ROOT / "upstream" / "tauceti"
TRUSTED_AUDIT_SOURCES = {
    REPOSITORY_ROOT / "scripts" / "ContractAxioms.lean",
    TAUCETI_CONTRACT_ROOT / "scripts" / "ContractAxioms.lean",
}
AUDITED_SOURCE_ROOTS = (
    REPOSITORY_ROOT / "MazurTorsion",
    REPOSITORY_ROOT / "EllipticCurves",
)
AUDITED_SOURCE_FILES = (
    REPOSITORY_ROOT / "MazurTorsion.lean",
    REPOSITORY_ROOT / "EllipticCurves.lean",
)
ARCHIVED_DRAFT_ROOT = REPOSITORY_ROOT / "archive" / "drafts"
BLUEPRINT_CHAPTER_ROOT = REPOSITORY_ROOT / "blueprint" / "MazurBlueprint" / "Chapters"
BLUEPRINT_TOP_LEVEL = (
    REPOSITORY_ROOT / "blueprint" / "MazurBlueprint" / "Blueprint.lean"
)

IDENTIFIER_PATTERN = re.compile(r"^MT-[A-Z0-9]+(?:-[A-Z0-9]+)*$")
IMPORT_PATTERN = re.compile(
    r"^[ \t]*(?:public[ \t]+)?import[ \t]+([A-Za-z0-9_'.]+)[ \t]*$",
    re.MULTILINE,
)
DECLARATION_PATTERN = re.compile(
    r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)"
)
LOCAL_DECLARATION_PATTERN = re.compile(
    r"^[ \t]*(?:(?:noncomputable|private|protected|public)[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|instance)[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
    re.MULTILINE,
)
NAMESPACE_PATTERN = re.compile(
    r"^[ \t]*namespace[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$"
)
SECTION_PATTERN = re.compile(
    r"^[ \t]*(?:(?:public|private)[ \t]+)?section(?:[ \t]+[A-Za-z0-9_']+)?[ \t]*$"
)
END_PATTERN = re.compile(r"^[ \t]*end(?:[ \t]+[A-Za-z0-9_'.]+)?[ \t]*$")
QUALIFIED_NAME_PATTERN = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
SORRY_PATTERN = re.compile(r"\bsorry\b")
SOURCE_PROHIBITIONS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "axiom declaration": re.compile(
        r"^[ \t]*(?:(?:private|protected|public)[ \t]+)*(?:axiom|axioms)\b",
        re.MULTILINE,
    ),
    "constant declaration": re.compile(
        r"^[ \t]*(?:(?:private|protected|public)[ \t]+)*"
        r"(?:constant|constants)\b",
        re.MULTILINE,
    ),
    "unsafe declaration": re.compile(r"\bunsafe\b"),
    "partial declaration": re.compile(r"\bpartial\b"),
    "source-level set_option": re.compile(
        r"^[ \t]*set_option\b", re.MULTILINE
    ),
    "nolint attribute": re.compile(r"@\[\s*nolint\b|@nolint\b"),
}
ALLOWED_STATUSES = {"blocked", "done", "open", "planned", "research_open"}
ALLOWED_READINESS = {"compiled", "integrated", "nouns_missing", "statement_only"}
ALLOWED_KINDS = {"infrastructure", "integration", "milestone", "proof", "upstream"}
ALLOWED_RISKS = {"extreme", "high", "low", "medium"}
ALLOWED_BACKENDS = {"mathlib", "mazur", "mixed", "tauceti"}
ALLOWED_DELIVERABLE_KINDS = {
    "audit",
    "definition",
    "integration",
    "structure",
    "theorem",
}
ALLOWED_DELIVERABLE_STATES = {"contract", "integrated", "proposed"}
COMMIT_PATTERN = re.compile(r"^[0-9a-f]{40}$")
BLUEPRINT_BLOCK_PATTERN = re.compile(
    r'^:::(?P<kind>definition|lemma|proposition|theorem|group)\s+'
    r'"(?P<label>[^"]+)"(?P<metadata>[^\n]*)\n'
    r'(?P<body>.*?)'
    r'^:::[ \t]*$',
    re.MULTILINE | re.DOTALL,
)
BLUEPRINT_PARENT_PATTERN = re.compile(r'\(parent\s*:=\s*"([^"]+)"\)')
BLUEPRINT_USES_PATTERN = re.compile(r'\(uses\s*:=\s*"([^"]*)"\)')


class Validator:
    """Collect validation failures so contributors can fix them in one pass."""

    def __init__(self) -> None:
        self.errors: list[str] = []

    def require(self, condition: bool, message: str) -> None:
        """Record ``message`` when ``condition`` is false."""
        if not condition:
            self.errors.append(message)

    def finish(self, summary: str) -> None:
        """Print all failures or the successful validation summary."""
        if self.errors:
            print("Quality checks failed:", file=sys.stderr)
            for error in self.errors:
                print(f"  - {error}", file=sys.stderr)
            raise SystemExit(1)
        print(summary)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Build a JSON object while rejecting ambiguous duplicate keys."""
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def read_json_object(path: Path) -> dict[str, Any]:
    """Read one strict JSON object from ``path``."""
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=reject_duplicate_keys,
    )
    if not isinstance(value, dict):
        raise ValueError("top-level value must be an object")
    return value


def read_program(validator: Validator) -> dict[str, Any]:
    """Read the canonical crowdsourcing ledger."""
    try:
        program = read_json_object(PROGRAM_PATH)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        validator.errors.append(
            f"cannot read {PROGRAM_PATH.relative_to(REPOSITORY_ROOT)}: {error}"
        )
        validator.finish("")
        raise AssertionError("unreachable")
    validator.require(isinstance(program, dict), "program.json must contain a JSON object")
    return program


def validate_pins(validator: Validator, program: dict[str, Any]) -> None:
    """Cross-check the public provenance ledger against every executable pin."""
    baseline = program.get("baseline")
    sources = program.get("sources")
    validator.require(isinstance(baseline, dict), "baseline must be an object")
    validator.require(isinstance(sources, list), "sources must be a list")
    if not isinstance(baseline, dict) or not isinstance(sources, list):
        return
    source_by_id: dict[str, dict[str, Any]] = {}
    for source in sources:
        if not isinstance(source, dict) or not isinstance(source.get("id"), str):
            validator.errors.append("every source needs a string id")
            continue
        source_id = source["id"]
        validator.require(source_id not in source_by_id, f"duplicate source id {source_id}")
        source_by_id[source_id] = source
        commit = source.get("commit")
        validator.require(
            isinstance(commit, str) and bool(COMMIT_PATTERN.fullmatch(commit)),
            f"source {source_id}: commit must be a full lowercase Git SHA",
        )

    required_sources = {"mathlib", "clawristotle", "tauceti"}
    validator.require(
        required_sources <= source_by_id.keys(),
        "sources must register mathlib, clawristotle, and tauceti",
    )
    root_toolchain = (REPOSITORY_ROOT / "lean-toolchain").read_text(
        encoding="utf-8"
    ).strip()
    validator.require(
        baseline.get("lean_toolchain") == root_toolchain,
        "baseline.lean_toolchain must match lean-toolchain",
    )
    validator.require(
        (REPOSITORY_ROOT / "docbuild" / "lean-toolchain")
        .read_text(encoding="utf-8")
        .strip()
        == root_toolchain,
        "docbuild/lean-toolchain must match the root toolchain",
    )

    try:
        root_manifest = read_json_object(REPOSITORY_ROOT / "lake-manifest.json")
        doc_manifest = read_json_object(
            REPOSITORY_ROOT / "docbuild" / "lake-manifest.json"
        )
        root_configuration = tomllib.loads(
            (REPOSITORY_ROOT / "lakefile.toml").read_text(encoding="utf-8")
        )
    except (OSError, ValueError, json.JSONDecodeError, tomllib.TOMLDecodeError) as error:
        validator.errors.append(f"cannot validate root Lake pins: {error}")
        return
    root_packages = {
        package.get("name"): package
        for package in root_manifest.get("packages", [])
        if isinstance(package, dict)
    }
    root_requirements = {
        requirement.get("name"): requirement
        for requirement in root_configuration.get("require", [])
        if isinstance(requirement, dict)
    }
    root_mathlib = root_packages.get("mathlib", {})
    root_tau = root_packages.get("TauCeti", {})
    doc_packages = {
        package.get("name"): package
        for package in doc_manifest.get("packages", [])
        if isinstance(package, dict)
    }
    doc_mathlib = doc_packages.get("mathlib", {})
    root_mathlib_requirement = root_requirements.get("mathlib", {})
    root_tau_requirement = root_requirements.get("TauCeti", {})
    mathlib_source = source_by_id.get("mathlib", {})
    clawristotle_source = source_by_id.get("clawristotle", {})
    validator.require(
        baseline.get("mathlib_commit") == root_mathlib.get("rev"),
        "baseline.mathlib_commit must match lake-manifest.json",
    )
    validator.require(
        baseline.get("mathlib_commit") == mathlib_source.get("commit"),
        "baseline.mathlib_commit must match the mathlib source pin",
    )
    validator.require(
        baseline.get("mathlib_commit") == doc_mathlib.get("rev"),
        "baseline.mathlib_commit must match docbuild/lake-manifest.json",
    )
    validator.require(
        root_mathlib_requirement.get("rev") == root_mathlib.get("inputRev"),
        "lakefile.toml Mathlib revision must match the manifest input revision",
    )
    validator.require(
        root_mathlib_requirement.get("rev") == root_toolchain.rsplit(":", 1)[-1],
        "root Mathlib tag must match the Lean toolchain tag",
    )
    validator.require(
        baseline.get("source_commit") == clawristotle_source.get("commit"),
        "baseline.source_commit must match the Clawristotle source pin",
    )
    tau_source = source_by_id.get("tauceti", {})
    validator.require(
        tau_source.get("commit")
        == root_tau_requirement.get("rev")
        == root_tau.get("rev"),
        "Tau Ceti source, root Lake requirement, and root manifest commits must match",
    )
    validator.require(
        root_tau_requirement.get("rev") == root_tau.get("inputRev"),
        "root Tau Ceti requirement must match the manifest input revision",
    )
    validator.require(
        tau_source.get("mathlib_commit") == root_mathlib.get("rev"),
        "root Mathlib revision must match the Tau Ceti compatibility pin",
    )

    tau_root = TAUCETI_CONTRACT_ROOT
    try:
        tau_manifest = read_json_object(tau_root / "lake-manifest.json")
        tau_configuration = tomllib.loads(
            (tau_root / "lakefile.toml").read_text(encoding="utf-8")
        )
        tau_toolchain = (tau_root / "lean-toolchain").read_text(
            encoding="utf-8"
        ).strip()
    except (OSError, ValueError, json.JSONDecodeError, tomllib.TOMLDecodeError) as error:
        validator.errors.append(f"cannot validate Tau Ceti pins: {error}")
        return
    tau_packages = {
        package.get("name"): package
        for package in tau_manifest.get("packages", [])
        if isinstance(package, dict)
    }
    tau_requirements = {
        requirement.get("name"): requirement
        for requirement in tau_configuration.get("require", [])
        if isinstance(requirement, dict)
    }
    tau_package = tau_packages.get("TauCeti", {})
    tau_mathlib = tau_packages.get("mathlib", {})
    tau_requirement = tau_requirements.get("TauCeti", {})
    validator.require(
        tau_source.get("commit")
        == tau_requirement.get("rev")
        == tau_package.get("rev"),
        "Tau Ceti source, Lake requirement, and manifest commits must match",
    )
    validator.require(
        tau_source.get("lean_toolchain") == tau_toolchain,
        "Tau Ceti source lean_toolchain must match upstream/tauceti/lean-toolchain",
    )
    validator.require(
        tau_source.get("mathlib_commit") == tau_mathlib.get("rev"),
        "Tau Ceti source mathlib_commit must match its manifest",
    )


def strip_lean_comments_and_strings(source: str) -> str:
    """Replace Lean comments and string contents while preserving newlines."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        current = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""
        if block_depth:
            if current == "/" and following == "-":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
            elif current == "-" and following == "/":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
            else:
                output.append("\n" if current == "\n" else " ")
                index += 1
        elif in_string:
            if current == "\\" and following:
                output.extend((" ", " "))
                index += 2
            elif current == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if current == "\n" else " ")
                index += 1
        elif current == "/" and following == "-":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
        elif current == "-" and following == "-":
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
        elif current == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(current)
            index += 1
    return "".join(output)


def normalized_lean(source: str) -> str:
    """Normalize layout for exact challenge-signature comparison."""
    return re.sub(r"\s+", "", strip_lean_comments_and_strings(source))


def expected_credit(node: dict[str, Any]) -> int:
    """Return the credit percentage dictated by the public progress method."""
    completion = node.get("completion", {})
    if completion.get("integrated") is True:
        return 100
    if node.get("kind") in {"infrastructure", "upstream"}:
        if completion.get("api") is True:
            return 70
        if completion.get("proof") is True:
            return 40
        return 0
    if completion.get("api") is True:
        return 85
    if completion.get("proof") is True:
        return 70
    return 0


def validate_program_shape(
    validator: Validator, program: dict[str, Any]
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    """Validate node fields, weights, progress, and dependency topology."""
    validator.require(program.get("schema_version") == 3, "schema_version must be 3")
    stages = program.get("stages")
    nodes = program.get("nodes")
    validator.require(isinstance(stages, list), "stages must be a list")
    validator.require(isinstance(nodes, list), "nodes must be a list")
    if not isinstance(stages, list) or not isinstance(nodes, list):
        return {}, {}

    stage_by_id: dict[str, dict[str, Any]] = {}
    for stage in stages:
        if not isinstance(stage, dict):
            validator.errors.append("every stage must be an object")
            continue
        stage_id = stage.get("id")
        validator.require(
            isinstance(stage_id, str) and bool(stage_id),
            "every stage needs a nonempty string id",
        )
        if not isinstance(stage_id, str):
            continue
        validator.require(stage_id not in stage_by_id, f"duplicate stage id {stage_id}")
        stage_by_id[stage_id] = stage
        validator.require(
            isinstance(stage.get("weight_points"), int)
            and stage["weight_points"] > 0,
            f"{stage_id}: weight_points must be a positive integer",
        )
        deliverables = stage.get("deliverables")
        validator.require(
            isinstance(deliverables, list) and bool(deliverables),
            f"{stage_id}: deliverables must be a nonempty list",
        )
        deliverable_names: set[str] = set()
        if isinstance(deliverables, list):
            for index, deliverable in enumerate(deliverables, start=1):
                prefix = f"{stage_id}: deliverable {index}"
                validator.require(
                    isinstance(deliverable, dict),
                    f"{prefix} must be an object",
                )
                if not isinstance(deliverable, dict):
                    continue
                name = deliverable.get("name")
                validator.require(
                    isinstance(name, str) and bool(name.strip()),
                    f"{prefix} needs a nonempty name",
                )
                if isinstance(name, str):
                    validator.require(
                        name not in deliverable_names,
                        f"{stage_id}: duplicate deliverable name {name!r}",
                    )
                    deliverable_names.add(name)
                validator.require(
                    deliverable.get("kind") in ALLOWED_DELIVERABLE_KINDS,
                    f"{prefix} has invalid kind {deliverable.get('kind')!r}",
                )
                validator.require(
                    deliverable.get("state") in ALLOWED_DELIVERABLE_STATES,
                    f"{prefix} has invalid state {deliverable.get('state')!r}",
                )
                description = deliverable.get("description")
                validator.require(
                    isinstance(description, str) and len(description.strip()) >= 24,
                    f"{prefix} needs a concrete description",
                )

    node_by_id: dict[str, dict[str, Any]] = {}
    stage_totals: defaultdict[str, int] = defaultdict(int)
    earned_points = 0.0
    claimable_points = 0
    ordinary_claimable_points = 0
    research_open_points = 0
    for node in nodes:
        if not isinstance(node, dict):
            validator.errors.append("every node must be an object")
            continue
        node_id = node.get("id")
        validator.require(
            isinstance(node_id, str) and bool(IDENTIFIER_PATTERN.fullmatch(node_id)),
            f"invalid node id {node_id!r}",
        )
        if not isinstance(node_id, str):
            continue
        validator.require(node_id not in node_by_id, f"duplicate node id {node_id}")
        node_by_id[node_id] = node
        validator.require(
            node.get("stage") in stage_by_id,
            f"{node_id}: unknown stage {node.get('stage')!r}",
        )
        validator.require(
            node.get("status") in ALLOWED_STATUSES,
            f"{node_id}: invalid status {node.get('status')!r}",
        )
        validator.require(
            node.get("readiness") in ALLOWED_READINESS,
            f"{node_id}: invalid readiness {node.get('readiness')!r}",
        )
        validator.require(
            node.get("kind") in ALLOWED_KINDS,
            f"{node_id}: invalid kind {node.get('kind')!r}",
        )
        validator.require(
            node.get("risk") in ALLOWED_RISKS,
            f"{node_id}: invalid risk {node.get('risk')!r}",
        )
        validator.require(
            node.get("backend") in ALLOWED_BACKENDS,
            f"{node_id}: invalid backend {node.get('backend')!r}",
        )
        weight = node.get("weight_points")
        validator.require(
            isinstance(weight, int) and weight > 0,
            f"{node_id}: weight_points must be a positive integer",
        )
        if isinstance(weight, int):
            stage_totals[str(node.get("stage"))] += weight
        for relation in ("depends_on", "unlocks"):
            related = node.get(relation)
            validator.require(
                isinstance(related, list)
                and all(isinstance(item, str) for item in related),
                f"{node_id}: {relation} must be a list of node ids",
            )
            if isinstance(related, list):
                validator.require(
                    len(related) == len(set(related)),
                    f"{node_id}: {relation} contains duplicates",
                )
                validator.require(
                    node_id not in related, f"{node_id}: cannot {relation} itself"
                )
        completion = node.get("completion")
        validator.require(
            isinstance(completion, dict),
            f"{node_id}: completion must be an object",
        )
        if isinstance(completion, dict):
            for flag in ("statement", "proof", "api", "integrated"):
                validator.require(
                    isinstance(completion.get(flag), bool),
                    f"{node_id}: completion.{flag} must be boolean",
                )
            validator.require(
                completion.get("proof") is not True
                or completion.get("statement") is True,
                f"{node_id}: a proof requires a completed statement",
            )
            validator.require(
                completion.get("api") is not True
                or completion.get("proof") is True,
                f"{node_id}: API completion requires a proof",
            )
            validator.require(
                completion.get("integrated") is not True
                or completion.get("api") is True,
                f"{node_id}: integration requires API completion",
            )
            validator.require(
                completion.get("integrated") is not True
                or node.get("status") == "done",
                f"{node_id}: integrated work must have done status",
            )
            expected = expected_credit(node)
            validator.require(
                completion.get("credit_percent") == expected,
                f"{node_id}: credit_percent must be {expected}",
            )
            if isinstance(weight, int):
                earned_points += weight * expected / 100
        challenge = node.get("challenge")
        if "challenge" in node:
            validator.require(
                isinstance(challenge, dict),
                f"{node_id}: challenge must be an object",
            )
        if isinstance(challenge, dict):
            claimable = challenge.get("claimable")
            validator.require(
                isinstance(claimable, bool),
                f"{node_id}: challenge.claimable must be boolean",
            )
            validator.require(
                node.get("status") in {"done", "open", "research_open"},
                f"{node_id}: a challenge node must be done, open, or research_open",
            )
            if node.get("status") == "done":
                validator.require(
                    claimable is False,
                    f"{node_id}: a completed challenge must not remain claimable",
                )
                validator.require(
                    all(
                        completion.get(flag) is True
                        for flag in ("statement", "proof", "api", "integrated")
                    ),
                    f"{node_id}: a completed challenge needs all completion flags",
                )
        if node.get("status") in {"open", "research_open"}:
            validator.require(
                node.get("readiness") == "compiled",
                f"{node_id}: open work must have compiled readiness",
            )
            validator.require(
                isinstance(challenge, dict) and challenge.get("claimable") is True,
                f"{node_id}: open work must have a claimable challenge",
            )
            if isinstance(challenge, dict):
                validator.require(
                    completion
                    == {
                        "statement": True,
                        "proof": False,
                        "api": False,
                        "integrated": False,
                        "credit_percent": 0,
                    },
                    f"{node_id}: an active challenge must earn statement-only credit",
                )
        if isinstance(challenge, dict) and challenge.get("claimable") is True:
            validator.require(
                node.get("status") in {"open", "research_open"},
                f"{node_id}: claimable challenges must have open or research_open status",
            )
            if isinstance(weight, int) and node.get("status") in {"open", "research_open"}:
                claimable_points += weight
                if node.get("status") == "open":
                    ordinary_claimable_points += weight
                else:
                    research_open_points += weight
        if node.get("status") == "done":
            validator.require(
                completion.get("integrated") is True,
                f"{node_id}: done work must be integrated",
            )
            validator.require(
                node.get("readiness") == "integrated",
                f"{node_id}: done work must have integrated readiness",
            )

    for stage_id, stage in stage_by_id.items():
        validator.require(
            stage_totals[stage_id] == stage.get("weight_points"),
            f"{stage_id}: node weights total {stage_totals[stage_id]}, "
            f"not declared {stage.get('weight_points')}",
        )

    total_points = sum(
        node.get("weight_points", 0)
        for node in nodes
        if isinstance(node, dict) and isinstance(node.get("weight_points"), int)
    )
    progress = program.get("progress")
    validator.require(isinstance(progress, dict), "progress must be an object")
    if isinstance(progress, dict):
        validator.require(total_points == 1000, f"node weights total {total_points}, not 1000")
        validator.require(
            progress.get("total_points") == total_points,
            "progress.total_points does not match node weights",
        )
        validator.require(
            abs(float(progress.get("earned_points", -1)) - earned_points) < 1e-9,
            f"progress.earned_points must be {earned_points:g}",
        )
        expected_percent = round(100 * earned_points / total_points, 1)
        validator.require(
            abs(float(progress.get("percent", -1)) - expected_percent) < 1e-9,
            f"progress.percent must be {expected_percent:.1f}",
        )
        ecosystem_ready = progress.get("ecosystem_ready_estimate_percent")
        validator.require(
            isinstance(ecosystem_ready, int)
            and expected_percent <= ecosystem_ready <= 100,
            "progress.ecosystem_ready_estimate_percent must be an integer "
            "between integrated progress and 100",
        )
        validator.require(
            progress.get("claimable_open_points") == claimable_points,
            f"progress.claimable_open_points must be {claimable_points}",
        )
        validator.require(
            progress.get("ordinary_claimable_points") == ordinary_claimable_points,
            "progress.ordinary_claimable_points must be "
            f"{ordinary_claimable_points}",
        )
        validator.require(
            progress.get("research_open_points") == research_open_points,
            f"progress.research_open_points must be {research_open_points}",
        )
        validator.require(
            ordinary_claimable_points + research_open_points == claimable_points,
            "ordinary and research claimable points must partition "
            "claimable_open_points",
        )

    validate_dependencies(validator, node_by_id)
    return stage_by_id, node_by_id


def validate_blueprint_topology(
    validator: Validator,
    stage_by_id: dict[str, dict[str, Any]],
    node_by_id: dict[str, dict[str, Any]],
) -> None:
    """Keep the Verso labels, groups, and mathematical edges equal to the DAG."""
    chapter_files = sorted(BLUEPRINT_CHAPTER_ROOT.glob("*.lean"))
    validator.require(
        len(chapter_files) == len(stage_by_id),
        "the Verso blueprint must have exactly one chapter per programme stage",
    )
    entries: dict[str, tuple[str | None, set[str], str]] = {}
    groups: set[str] = set()
    for path in chapter_files:
        source = path.read_text(encoding="utf-8")
        for match in BLUEPRINT_BLOCK_PATTERN.finditer(source):
            kind = match.group("kind")
            label = match.group("label")
            metadata = match.group("metadata")
            if kind == "group":
                validator.require(label not in groups, f"duplicate Blueprint group {label}")
                groups.add(label)
                continue
            validator.require(label not in entries, f"duplicate Blueprint node {label}")
            parent_match = BLUEPRINT_PARENT_PATTERN.search(metadata)
            uses_match = BLUEPRINT_USES_PATTERN.search(metadata)
            dependencies = {
                dependency.strip()
                for dependency in (uses_match.group(1).split(",") if uses_match else [])
                if dependency.strip()
            }
            entries[label] = (
                parent_match.group(1) if parent_match else None,
                dependencies,
                match.group("body"),
            )

    validator.require(
        groups == set(stage_by_id),
        "Verso Blueprint groups must exactly match the six programme stages",
    )
    validator.require(
        set(entries) == set(node_by_id),
        "Verso Blueprint labels must exactly match the 48 programme node ids",
    )
    for node_id, node in node_by_id.items():
        if node_id not in entries:
            continue
        parent, dependencies, body = entries[node_id]
        validator.require(
            parent == node.get("stage"),
            f"{node_id}: Blueprint parent {parent!r} differs from its programme stage",
        )
        expected_dependencies = set(node.get("depends_on", []))
        validator.require(
            dependencies == expected_dependencies,
            f"{node_id}: Blueprint uses differ from programme dependencies "
            f"(expected {sorted(expected_dependencies)}, actual {sorted(dependencies)})",
        )
        artifacts = node.get("artifacts")
        if not isinstance(artifacts, list):
            continue
        for artifact in artifacts:
            if not isinstance(artifact, dict) or not isinstance(
                artifact.get("name"), str
            ):
                continue
            artifact_name = artifact["name"]
            validator.require(
                f"`{artifact_name}`" in body,
                f"{node_id}: Blueprint block omits canonical artifact "
                f"{artifact_name}",
            )

    if not BLUEPRINT_TOP_LEVEL.is_file():
        validator.errors.append("missing Verso Blueprint top-level module")
        return
    top_level = BLUEPRINT_TOP_LEVEL.read_text(encoding="utf-8")
    validator.require(
        "{blueprint_graph" in top_level,
        "Verso Blueprint top level must render the interactive dependency graph",
    )
    validator.require(
        "{blueprint_summary}" in top_level,
        "Verso Blueprint top level must render the progress summary",
    )


def validate_dependencies(
    validator: Validator, node_by_id: dict[str, dict[str, Any]]
) -> None:
    """Check graph references, reciprocal edges, and acyclicity."""
    for node_id, node in node_by_id.items():
        for dependency in node.get("depends_on", []):
            validator.require(
                dependency in node_by_id,
                f"{node_id}: unknown dependency {dependency}",
            )
            if dependency in node_by_id:
                validator.require(
                    node_id in node_by_id[dependency].get("unlocks", []),
                    f"{dependency} -> {node_id}: missing reciprocal unlock",
                )
        for unlocked in node.get("unlocks", []):
            validator.require(
                unlocked in node_by_id,
                f"{node_id}: unknown unlocked node {unlocked}",
            )
            if unlocked in node_by_id:
                validator.require(
                    node_id in node_by_id[unlocked].get("depends_on", []),
                    f"{node_id} -> {unlocked}: missing reciprocal dependency",
                )

    colors: dict[str, int] = {}

    def visit(node_id: str, path: list[str]) -> None:
        color = colors.get(node_id, 0)
        if color == 2:
            return
        if color == 1:
            cycle_start = path.index(node_id)
            cycle = " -> ".join(path[cycle_start:] + [node_id])
            validator.errors.append(f"dependency graph contains a cycle: {cycle}")
            return
        colors[node_id] = 1
        for dependency in node_by_id[node_id].get("depends_on", []):
            if dependency in node_by_id:
                visit(dependency, path + [node_id])
        colors[node_id] = 2

    for node_id in node_by_id:
        if colors.get(node_id, 0) == 0:
            visit(node_id, [])


def challenge_module_for(path: Path) -> str:
    """Derive a Lean module name from a registered challenge path."""
    relative = path.relative_to(REPOSITORY_ROOT)
    if relative.parts[:2] == ("upstream", "tauceti"):
        relative = Path(*relative.parts[2:])
    return ".".join(relative.with_suffix("").parts)


def safe_repository_path(
    validator: Validator, node_id: str, relative_path: object
) -> Path | None:
    """Resolve a ledger path while rejecting absolute paths and traversal."""
    if not isinstance(relative_path, str) or not relative_path:
        validator.errors.append(f"{node_id}: challenge.file must be a nonempty string")
        return None
    candidate = (REPOSITORY_ROOT / relative_path).resolve()
    try:
        candidate.relative_to(REPOSITORY_ROOT)
    except ValueError:
        validator.errors.append(f"{node_id}: challenge.file escapes the repository")
        return None
    return candidate


def contract_source_files() -> set[Path]:
    """Return every contract, aggregator, and narrowly trusted audit source."""
    source_files = {
        path.resolve()
        for root in CHALLENGE_ROOTS
        if root.is_dir()
        for path in root.rglob("*.lean")
    }
    tauceti_harness_root = TAUCETI_CONTRACT_ROOT / "scripts"
    if tauceti_harness_root.is_dir():
        source_files.update(
            path.resolve() for path in tauceti_harness_root.rglob("*.lean")
        )
    source_files.update(
        path.resolve() for path in CHALLENGE_AGGREGATORS if path.is_file()
    )
    source_files.update(
        path.resolve() for path in TRUSTED_AUDIT_SOURCES if path.is_file()
    )
    return source_files


def declarations_in_source(code: str) -> set[str]:
    """Recover qualified local declaration names from ordinary namespace scopes."""
    declarations: set[str] = set()
    namespace: list[str] = []
    scope_stack: list[list[str]] = []
    for line in code.splitlines():
        namespace_match = NAMESPACE_PATTERN.fullmatch(line)
        if namespace_match:
            scope_stack.append(namespace.copy())
            namespace.extend(namespace_match.group(1).split("."))
            continue
        if SECTION_PATTERN.fullmatch(line):
            scope_stack.append(namespace.copy())
            continue
        if END_PATTERN.fullmatch(line):
            if scope_stack:
                namespace = scope_stack.pop()
            continue
        declaration_match = LOCAL_DECLARATION_PATTERN.match(line)
        if declaration_match:
            declared_name = declaration_match.group(1).split(".")
            declarations.add(".".join(namespace + declared_name))
    return declarations


def local_declaration_sources() -> dict[str, Path]:
    """Map locally defined declarations to their source files."""
    source_files = contract_source_files()
    for root in AUDITED_SOURCE_ROOTS:
        if root.is_dir():
            source_files.update(path.resolve() for path in root.rglob("*.lean"))
    source_files.update(
        path.resolve() for path in AUDITED_SOURCE_FILES if path.is_file()
    )
    declarations: dict[str, Path] = {}
    for path in sorted(source_files):
        code = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        for declaration in declarations_in_source(code):
            declarations[declaration] = path
    return declarations


def validate_node_artifacts(
    validator: Validator, node_by_id: dict[str, dict[str, Any]]
) -> None:
    """Require a concrete artifact list or an exact registered challenge."""
    local_sources: dict[str, Path] | None = None
    for node_id, node in node_by_id.items():
        artifacts = node.get("artifacts")
        challenge = node.get("challenge")
        has_artifacts = isinstance(artifacts, list) and bool(artifacts)
        validator.require(
            has_artifacts or isinstance(challenge, dict),
            f"{node_id}: needs nonempty artifacts or an exact challenge contract",
        )
        if artifacts is None:
            continue
        validator.require(
            has_artifacts,
            f"{node_id}: artifacts must be a nonempty list when present",
        )
        if not isinstance(artifacts, list):
            continue

        artifact_names: set[str] = set()
        for index, artifact in enumerate(artifacts, start=1):
            prefix = f"{node_id}: artifact {index}"
            validator.require(isinstance(artifact, dict), f"{prefix} must be an object")
            if not isinstance(artifact, dict):
                continue
            name = artifact.get("name")
            valid_name = isinstance(name, str) and bool(
                QUALIFIED_NAME_PATTERN.fullmatch(name)
            )
            validator.require(
                valid_name,
                f"{prefix} name must be a qualified Lean-style identifier",
            )
            if isinstance(name, str):
                validator.require(
                    name not in artifact_names,
                    f"{node_id}: duplicate artifact name {name!r}",
                )
                artifact_names.add(name)
            validator.require(
                artifact.get("kind") in ALLOWED_DELIVERABLE_KINDS,
                f"{prefix} has invalid kind {artifact.get('kind')!r}",
            )
            state = artifact.get("state")
            validator.require(
                state in ALLOWED_DELIVERABLE_STATES,
                f"{prefix} has invalid state {state!r}",
            )
            description = artifact.get("description")
            validator.require(
                isinstance(description, str) and len(description.strip()) >= 24,
                f"{prefix} needs a concrete description",
            )
            module = artifact.get("module")
            if module is not None:
                validator.require(
                    isinstance(module, str)
                    and bool(QUALIFIED_NAME_PATTERN.fullmatch(module)),
                    f"{prefix} module must be a qualified Lean module name",
                )
            if state == "integrated" and isinstance(name, str):
                if local_sources is None:
                    local_sources = local_declaration_sources()
                validator.require(
                    name in local_sources,
                    f"{prefix} claims missing integrated declaration {name}",
                )
                completion = node.get("completion")
                validator.require(
                    isinstance(completion, dict)
                    and completion.get("integrated") is True,
                    f"{prefix} may be integrated only on an integrated node",
                )


def validate_challenge_metadata(
    validator: Validator,
    node_id: str,
    challenge: dict[str, Any],
    local_sources: dict[str, Path],
) -> Path | None:
    """Validate one challenge's durable registry metadata."""
    required_fields = (
        "claimable",
        "module",
        "file",
        "declaration",
        "destination_module",
        "destination_declaration",
        "signature",
        "imports",
        "informal",
        "recommended_route",
        "consumer_declarations",
        "estimated_lines",
        "skills",
    )
    for field in required_fields:
        validator.require(field in challenge, f"{node_id}: missing challenge.{field}")
    string_fields = (
        "module",
        "file",
        "declaration",
        "destination_module",
        "destination_declaration",
        "signature",
        "informal",
        "recommended_route",
    )
    for field in string_fields:
        validator.require(
            isinstance(challenge.get(field), str) and bool(challenge.get(field)),
            f"{node_id}: challenge.{field} must be a nonempty string",
        )
    for field in (
        "module",
        "declaration",
        "destination_module",
        "destination_declaration",
    ):
        value = challenge.get(field)
        validator.require(
            isinstance(value, str) and bool(QUALIFIED_NAME_PATTERN.fullmatch(value)),
            f"{node_id}: challenge.{field} must be a qualified Lean name",
        )
    destination_module = challenge.get("destination_module")
    destination_declaration = challenge.get("destination_declaration")
    for field, value in (
        ("destination_module", destination_module),
        ("destination_declaration", destination_declaration),
    ):
        validator.require(
            isinstance(value, str)
            and not value.startswith(
                (
                    "Challenge.",
                    "MazurTheorem.Challenge.",
                    "MazurTauCetiChallenge.",
                )
            ),
            f"{node_id}: challenge.{field} must name the permanent library API",
        )
    validator.require(
        destination_declaration != challenge.get("declaration"),
        f"{node_id}: destination declaration must differ from the challenge declaration",
    )
    validate_challenge_lists(
        validator, node_id, challenge, set(local_sources)
    )
    imports = challenge.get("imports")
    validator.require(
        isinstance(imports, list)
        and challenge.get("destination_module") in imports,
        f"{node_id}: the immutable imports must include destination_module",
    )
    destination_module = challenge.get("destination_module")
    if isinstance(destination_module, str) and destination_module.startswith(
        ("MazurTorsion.", "EllipticCurves.")
    ):
        destination_path = REPOSITORY_ROOT / (
            destination_module.replace(".", "/") + ".lean"
        )
        validator.require(
            destination_path.is_file(),
            f"{node_id}: missing permanent destination module "
            f"{destination_path.relative_to(REPOSITORY_ROOT)}",
        )
    estimates = challenge.get("estimated_lines")
    validator.require(
        isinstance(estimates, dict)
        and isinstance(estimates.get("min"), int)
        and isinstance(estimates.get("max"), int)
        and 0 < estimates["min"] <= estimates["max"],
        f"{node_id}: estimated_lines must have positive min <= max",
    )
    return safe_repository_path(validator, node_id, challenge.get("file"))


def validate_challenge_lists(
    validator: Validator,
    node_id: str,
    challenge: dict[str, Any],
    local_consumer_declarations: set[str],
) -> None:
    """Validate imports, skills, and concrete downstream consumers."""
    imports = challenge.get("imports")
    validator.require(
        isinstance(imports, list)
        and bool(imports)
        and all(
            isinstance(item, str) and bool(QUALIFIED_NAME_PATTERN.fullmatch(item))
            for item in imports
        ),
        f"{node_id}: challenge.imports must be qualified Lean module names",
    )
    skills = challenge.get("skills")
    validator.require(
        isinstance(skills, list)
        and bool(skills)
        and all(isinstance(item, str) and bool(item.strip()) for item in skills),
        f"{node_id}: challenge.skills must be nonempty strings",
    )
    consumers = challenge.get("consumer_declarations")
    validator.require(
        isinstance(consumers, list) and bool(consumers),
        f"{node_id}: challenge.consumer_declarations must be a nonempty list",
    )
    list_fields = (
        ("imports", imports),
        ("skills", skills),
        ("consumer_declarations", consumers),
    )
    for field, values in list_fields:
        if isinstance(values, list):
            validator.require(
                len(values) == len(set(map(str, values))),
                f"{node_id}: challenge.{field} contains duplicates",
            )
    if not isinstance(consumers, list):
        return
    for consumer in consumers:
        valid_name = isinstance(consumer, str) and bool(
            QUALIFIED_NAME_PATTERN.fullmatch(consumer)
        )
        validator.require(
            valid_name,
            f"{node_id}: consumer {consumer!r} must be a qualified Lean declaration",
        )
        if not valid_name:
            continue
        validator.require(
            consumer not in {
                challenge.get("declaration"),
                challenge.get("destination_declaration"),
            },
            f"{node_id}: consumer {consumer} must be downstream of the contract",
        )
        validator.require(
            consumer in local_consumer_declarations,
            f"{node_id}: consumer {consumer} has no matching local declaration",
        )


def validate_challenge_source(
    validator: Validator,
    node_id: str,
    node: dict[str, Any],
    challenge: dict[str, Any],
    path: Path,
    local_sources: dict[str, Path],
) -> None:
    """Validate one durable contract source against its lifecycle."""
    validator.require(path.suffix == ".lean", f"{node_id}: challenge file must end in .lean")
    validator.require(path.is_file(), f"{node_id}: missing {path.relative_to(REPOSITORY_ROOT)}")
    if not path.is_file():
        return
    expected_module = challenge_module_for(path)
    validator.require(
        challenge.get("module") == expected_module,
        f"{node_id}: module must be {expected_module}",
    )
    source = path.read_text(encoding="utf-8")
    code = strip_lean_comments_and_strings(source)
    signature = challenge.get("signature")
    normalized_signature = normalized_lean(signature) if isinstance(signature, str) else ""
    validator.require(
        len(SORRY_PATTERN.findall(strip_lean_comments_and_strings(str(signature)))) == 1
        and normalized_signature.endswith(":=sorry"),
        f"{node_id}: signature must end in exactly the whole proof body ':= sorry'",
    )
    match = DECLARATION_PATTERN.search(signature) if isinstance(signature, str) else None
    declaration_tail = str(challenge.get("declaration", "")).rsplit(".", 1)[-1]
    validator.require(
        match is not None and match.group(1) == declaration_tail,
        f"{node_id}: signature theorem name does not match challenge.declaration",
    )
    active = node.get("status") in {"open", "research_open"}
    expected_source = (
        normalized_signature
        if active
        else normalized_signature.removesuffix(":=sorry") + ":="
    )
    normalized_source = normalized_lean(source)
    validator.require(
        bool(expected_source) and expected_source in normalized_source,
        f"{node_id}: registered statement is not exact source text modulo layout",
    )
    declared_names = declarations_in_source(code)
    registered_declaration = challenge.get("declaration")
    validator.require(
        registered_declaration in declared_names,
        f"{node_id}: source does not define {challenge.get('declaration')}",
    )
    same_tail_declarations = {
        declaration
        for declaration in declared_names
        if declaration.rsplit(".", 1)[-1] == declaration_tail
    }
    validator.require(
        same_tail_declarations == {registered_declaration},
        f"{node_id}: theorem tail {declaration_tail} must identify only "
        f"{registered_declaration}, found {sorted(same_tail_declarations)}",
    )
    actual_imports = IMPORT_PATTERN.findall(code)
    declared_imports = challenge.get("imports")
    if isinstance(declared_imports, list):
        validator.require(
            declared_imports == actual_imports,
            f"{node_id}: ordered imports differ "
            f"(declared {list(map(str, declared_imports))}, actual {actual_imports})",
        )
    validator.require(
        not any(imported.startswith("Challenge.") for imported in actual_imports),
        f"{node_id}: a challenge may not import another challenge",
    )
    if not active:
        destination_declaration = challenge.get("destination_declaration")
        validator.require(
            isinstance(destination_declaration, str)
            and destination_declaration in code,
            f"{node_id}: completed contract must be a thin bridge to "
            f"{destination_declaration}",
        )
        if isinstance(destination_declaration, str) and destination_declaration.startswith(
            ("MazurTorsion.", "EllipticCurves.")
        ):
            validator.require(
                destination_declaration in local_sources,
                f"{node_id}: completed destination {destination_declaration} "
                "has no local declaration",
            )
        for consumer in challenge.get("consumer_declarations", []):
            consumer_path = local_sources.get(consumer)
            if consumer_path is None or not isinstance(destination_declaration, str):
                continue
            consumer_code = strip_lean_comments_and_strings(
                consumer_path.read_text(encoding="utf-8")
            )
            validator.require(
                destination_declaration in consumer_code,
                f"{node_id}: completed consumer {consumer} is not wired to "
                f"{destination_declaration}",
            )
    validator.require(
        len(SORRY_PATTERN.findall(code)) == (1 if active else 0),
        f"{node_id}: {'open' if active else 'completed'} contract must contain "
        f"{'exactly one whole-body sorry' if active else 'no sorry'}",
    )
    validate_source_prohibitions(validator, path, code, allow_single_sorry=active)


def validate_challenges(
    validator: Validator, node_by_id: dict[str, dict[str, Any]]
) -> int:
    """Check every challenge contract, including completed immutable records."""
    registered_files: set[Path] = set()
    active_files: set[Path] = set()
    registered_count = 0
    local_sources = local_declaration_sources()
    for node_id, node in node_by_id.items():
        challenge = node.get("challenge")
        if not isinstance(challenge, dict):
            continue
        registered_count += 1
        path = validate_challenge_metadata(
            validator, node_id, challenge, local_sources
        )
        if path is None:
            continue
        validator.require(
            path not in registered_files,
            f"{node_id}: challenge file is registered by more than one node",
        )
        registered_files.add(path)
        if node.get("status") in {"open", "research_open"}:
            active_files.add(path)
        validate_challenge_source(
            validator, node_id, node, challenge, path, local_sources
        )

    all_contract_files = contract_source_files()
    discovered_files = {
        path
        for path in all_contract_files
        if SORRY_PATTERN.search(
            strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        )
    }
    for path in sorted(discovered_files - active_files):
        validator.errors.append(
            f"sorry is allowed only in an active registered contract: "
            f"{path.relative_to(REPOSITORY_ROOT)}"
        )
    for path in sorted(active_files - discovered_files):
        validator.errors.append(
            f"active registered contract has no sorry: "
            f"{path.relative_to(REPOSITORY_ROOT)}"
        )
    for path in sorted(all_contract_files - registered_files):
        code = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        validate_source_prohibitions(validator, path, code)
    return registered_count


def validate_aggregator_coverage(
    validator: Validator, node_by_id: dict[str, dict[str, Any]]
) -> None:
    """Require each contract root to import every and only registered modules."""
    groups = (
        (
            REPOSITORY_ROOT / "Challenge.lean",
            lambda file_name: file_name.startswith("Challenge/"),
        ),
        (
            REPOSITORY_ROOT / "upstream" / "tauceti" / "MazurTauCetiChallenge.lean",
            lambda file_name: file_name.startswith("upstream/tauceti/"),
        ),
    )
    for aggregator, belongs in groups:
        expected = {
            challenge["module"]
            for node in node_by_id.values()
            if isinstance((challenge := node.get("challenge")), dict)
            and isinstance(challenge.get("file"), str)
            and belongs(challenge["file"])
        }
        if not aggregator.is_file():
            validator.errors.append(
                f"missing contract aggregator {aggregator.relative_to(REPOSITORY_ROOT)}"
            )
            continue
        code = strip_lean_comments_and_strings(
            aggregator.read_text(encoding="utf-8")
        )
        actual_list = IMPORT_PATTERN.findall(code)
        validator.require(
            len(actual_list) == len(set(actual_list)),
            f"{aggregator.relative_to(REPOSITORY_ROOT)} contains duplicate imports",
        )
        actual = set(actual_list)
        validator.require(
            actual == expected,
            f"{aggregator.relative_to(REPOSITORY_ROOT)} coverage differs "
            f"(expected {sorted(expected)}, actual {sorted(actual)})",
        )


def validate_source_prohibitions(
    validator: Validator,
    path: Path,
    code: str,
    *,
    allow_single_sorry: bool = False,
) -> None:
    """Apply the repository's syntax-level safety gates to Lean source."""
    for label, pattern in SOURCE_PROHIBITIONS.items():
        checked_code = code
        if label == "unsafe declaration" and path.resolve() in {
            trusted.resolve() for trusted in TRUSTED_AUDIT_SOURCES
        }:
            checked_code = re.sub(
                r"\bunsafe\s+Lean\.withImportModules\b",
                "Lean.withImportModules",
                checked_code,
            )
        matches = pattern.findall(checked_code)
        if label == "sorry" and allow_single_sorry and len(matches) == 1:
            continue
        validator.require(
            not matches,
            f"{path.relative_to(REPOSITORY_ROOT)}: prohibited {label}",
        )


def validate_integrated_sources(validator: Validator) -> tuple[int, int]:
    """Scan integrated Lean sources, deliberately excluding archived drafts."""
    source_files: set[Path] = set()
    for root in AUDITED_SOURCE_ROOTS:
        if root.is_dir():
            source_files.update(root.rglob("*.lean"))
    source_files.update(path for path in AUDITED_SOURCE_FILES if path.is_file())
    line_count = 0
    for path in sorted(source_files):
        validator.require(
            ARCHIVED_DRAFT_ROOT not in path.parents,
            f"internal error: archived draft entered source scan: {path}",
        )
        source = path.read_text(encoding="utf-8")
        line_count += len(source.splitlines())
        code = strip_lean_comments_and_strings(source)
        validate_source_prohibitions(validator, path, code)
    return len(source_files), line_count


def main() -> None:
    """Run all quality checks."""
    validator = Validator()
    program = read_program(validator)
    validate_pins(validator, program)
    stage_by_id, node_by_id = validate_program_shape(validator, program)
    validate_node_artifacts(validator, node_by_id)
    validate_blueprint_topology(validator, stage_by_id, node_by_id)
    challenge_count = validate_challenges(validator, node_by_id)
    validate_aggregator_coverage(validator, node_by_id)
    source_count, line_count = validate_integrated_sources(validator)
    baseline = program.get("baseline", {})
    validator.require(
        baseline.get("integrated_lean_modules") == source_count,
        f"baseline.integrated_lean_modules must be {source_count}",
    )
    validator.require(
        baseline.get("integrated_lean_lines") == line_count,
        f"baseline.integrated_lean_lines must be {line_count}",
    )
    progress = program.get("progress", {})
    validator.finish(
        "Quality checks passed: "
        f"{len(node_by_id)} DAG nodes / {progress.get('total_points')} points; "
        f"{challenge_count} registered challenge contracts; "
        f"{source_count} integrated Lean sources / {line_count} lines; "
        "archive/drafts excluded."
    )


if __name__ == "__main__":
    main()
