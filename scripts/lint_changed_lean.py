#!/usr/bin/env python3
"""Ratchet Batteries linter findings in the integrated MazurTorsion corpus.

The generated/integrated corpus currently has linter debt.  A fixed cutoff
grandfathers findings only in files that remain untouched after that commit.
This gate keeps all default Batteries linters enabled, rejects declaration
waiver files, and requires every subsequently touched Lean source to have no
reported findings.

Batteries attributes each finding to the declaration's source file.  This is
therefore a touched-source ratchet: a dependency change whose only reported
effect is in an untouched downstream file remains in the grandfathered set.
"""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path

import lean_audit_cache as audit_cache
import lean_regular_cache as regular_cache


SOURCE_CUTOFF = "7a79b4ae01d964b38370ecafde388aefc281dbbe"
# Pin migrations update this reference only after the new linter environment
# has been reviewed.  They must never reset the cumulative source cutoff.
LINTER_ENVIRONMENT_REFERENCE = "7a79b4ae01d964b38370ecafde388aefc281dbbe"
RATCHET_SCHEMA = 1
EXPECTED_LINTER_COUNT = 14
EXPECTED_LINTERS = frozenset(
    {
        "checkType",
        "defsWithUnderscore",
        "deprecatedNoSince",
        "docBlame",
        "impossibleInstance",
        "nonClassInstance",
        "simpComm",
        "simpNF",
        "structureInType",
        "subsetDotNotationLinter",
        "synTaut",
        "tacticDocs",
        "unusedArguments",
        "unusedHavesSuffices",
    }
)
ROOT_MODULE = "MazurTorsion"
ROOT_FILE = Path("MazurTorsion.lean")
ROOT_DIRECTORY = Path("MazurTorsion")
NOLINTS_FILE = Path("scripts/nolints.json")
LINTER_ENVIRONMENT = (
    Path("lean-toolchain"),
    Path("lakefile.toml"),
    Path("lake-manifest.json"),
)

SUMMARY_RE = re.compile(
    r"^-- Found (?P<count>[0-9]+) errors? in .* in "
    r"(?P<module>MazurTorsion(?:\.[A-Za-z0-9_']+)*) with "
    r"(?P<linters>[0-9]+) linters$",
    re.MULTILINE,
)
DIAGNOSTIC_RE = re.compile(
    r"^(?P<path>.+?\.lean):(?P<line>[0-9]+):(?P<column>[0-9]+): error: "
    r"(?P<message>.*)$",
    re.MULTILINE,
)
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


class GateError(RuntimeError):
    """The linter output or source cutoff could not be validated safely."""


@dataclass(frozen=True)
class Finding:
    path: Path
    line: int
    column: int
    message: str


def git(root: Path, *args: str) -> bytes:
    try:
        return subprocess.run(
            ["git", *args],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
        ).stdout
    except subprocess.CalledProcessError as error:
        raise GateError(f"git {' '.join(args)} failed") from error


def require_commit(root: Path, commit: str, description: str) -> None:
    try:
        subprocess.run(
            ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
            cwd=root,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError as error:
        raise GateError(
            f"{description} {commit} is unavailable; fetch that commit first"
        ) from error


def require_no_waiver_file(root: Path) -> None:
    if (root / NOLINTS_FILE).exists():
        raise GateError(
            f"{NOLINTS_FILE} is a Batteries declaration-level linter waiver"
        )


def validate_cutoff(root: Path) -> None:
    references = (
        (SOURCE_CUTOFF, "source cutoff"),
        (LINTER_ENVIRONMENT_REFERENCE, "linter-environment reference"),
    )
    for commit, description in references:
        require_commit(root, commit, description)
        ancestor = subprocess.run(
            ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
            cwd=root,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if ancestor.returncode != 0:
            raise GateError(f"{description} {commit} is not an ancestor of HEAD")

    drift = git(
        root,
        "diff",
        "--name-only",
        "-z",
        LINTER_ENVIRONMENT_REFERENCE,
        "HEAD",
        "--",
        *(path.as_posix() for path in LINTER_ENVIRONMENT),
    )
    changed_environment = [
        path for path in drift.decode("utf-8").split("\0") if path
    ]
    if changed_environment:
        raise GateError(
            "linter environment differs from the fixed cutoff: "
            + ", ".join(changed_environment)
            + "; review it and advance LINTER_ENVIRONMENT_REFERENCE explicitly"
        )


def touched_sources(root: Path) -> set[Path]:
    validate_cutoff(root)
    output = git(
        root,
        "log",
        "--first-parent",
        "--diff-merges=first-parent",
        "--format=",
        "--name-only",
        "--no-renames",
        "-z",
        f"{SOURCE_CUTOFF}..HEAD",
        "--",
        ROOT_FILE.as_posix(),
        ROOT_DIRECTORY.as_posix(),
    )
    changed: set[Path] = set()
    for raw_path in output.decode("utf-8").split("\0"):
        if not raw_path:
            continue
        path = Path(raw_path)
        if path.suffix != ".lean" or not (root / path).is_file():
            continue
        if path != ROOT_FILE and ROOT_DIRECTORY not in path.parents:
            raise GateError(f"unexpected MazurTorsion source path from git: {path}")
        changed.add(path)
    return changed


def source_path(root: Path, raw_path: str) -> Path:
    path = Path(raw_path)
    absolute = path if path.is_absolute() else root / path
    try:
        relative = absolute.resolve().relative_to(root.resolve())
    except ValueError as error:
        raise GateError(f"linter reported a path outside the repository: {raw_path}") from error
    if relative.suffix != ".lean":
        raise GateError(f"linter reported a non-Lean source: {relative}")
    if relative != ROOT_FILE and ROOT_DIRECTORY not in relative.parents:
        raise GateError(f"linter reported an unknown package source: {relative}")
    if not (root / relative).is_file():
        raise GateError(f"linter reported a missing source: {relative}")
    return relative


def parse_failed_run(root: Path, module: str, output: str) -> list[Finding]:
    output = ANSI_RE.sub("", output)
    if "LINTER FAILED" in output:
        raise GateError("a Batteries linter crashed")

    summaries = list(SUMMARY_RE.finditer(output))
    if len(summaries) != 1:
        raise GateError(f"expected one {module} linter summary, found {len(summaries)}")
    if summaries[0].group("module") != module:
        raise GateError(
            f"expected linter summary for {module}, found one for "
            f"{summaries[0].group('module')}"
        )
    linter_count = int(summaries[0].group("linters"))
    if linter_count != EXPECTED_LINTER_COUNT:
        raise GateError(
            f"expected {EXPECTED_LINTER_COUNT} linters for {module}, found {linter_count}"
        )
    expected = int(summaries[0].group("count"))
    matches = list(DIAGNOSTIC_RE.finditer(output))
    if expected == 0 or len(matches) != expected:
        raise GateError(
            f"linter summary reported {expected} findings but {len(matches)} were parsed"
        )

    return [
        Finding(
            path=source_path(root, match.group("path")),
            line=int(match.group("line")),
            column=int(match.group("column")),
            message=match.group("message"),
        )
        for match in matches
    ]


def validate_linter_inventory(module: str, output: str) -> None:
    lines = ANSI_RE.sub("", output).splitlines()
    marker = f"[{module}] Running linters:"
    marker_indices = [index for index, line in enumerate(lines) if line == marker]
    if len(marker_indices) != 1:
        raise GateError(
            f"expected one traced linter inventory for {module}, "
            f"found {len(marker_indices)}"
        )
    names: list[str] = []
    for line in lines[marker_indices[0] + 1 :]:
        match = re.fullmatch(r"  ([A-Za-z0-9_']+)", line)
        if match is None:
            break
        names.append(match.group(1))
    actual = frozenset(names)
    if len(names) != len(actual) or actual != EXPECTED_LINTERS:
        missing = ", ".join(sorted(EXPECTED_LINTERS - actual))
        extra = ", ".join(sorted(actual - EXPECTED_LINTERS))
        raise GateError(
            f"linter inventory changed for {module}; missing={missing}; extra={extra}"
        )


def run_linter(root: Path, module: str) -> list[Finding]:
    result = subprocess.run(
        ["lake", "exe", "runLinter", "--trace", "--no-build", module],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    output = result.stdout
    validate_linter_inventory(module, output)
    if result.returncode == 0:
        if (
            "LINTER FAILED" in output
            or DIAGNOSTIC_RE.search(ANSI_RE.sub("", output))
            or SUMMARY_RE.search(ANSI_RE.sub("", output))
            or f"-- Linting passed for {module}." not in output
        ):
            raise GateError("successful linter run had an unexpected output contract")
        return []
    if result.returncode != 1:
        raise GateError(f"{module} linter exited unexpectedly with {result.returncode}")
    return parse_failed_run(root, module, output)


def self_check(root: Path) -> None:
    require_no_waiver_file(root)
    validate_cutoff(root)
    source = (root / ROOT_FILE).resolve()
    sample = (
        "Running linter on specified modules: [MazurTorsion]\n"
        "[MazurTorsion] Running linters:\n"
        + "".join(f"  {name}\n" for name in sorted(EXPECTED_LINTERS))
        + "[MazurTorsion] - checkType: (0/2) Starting...\n"
        "-- Found 1 error in 1 declarations (plus 0 automatically generated ones) "
        "in MazurTorsion with 14 linters\n"
        f"{source}:1:1: error: MazurTorsion sample finding\n"
    )
    validate_linter_inventory(ROOT_MODULE, sample)
    findings = parse_failed_run(root, ROOT_MODULE, sample)
    if findings != [Finding(ROOT_FILE, 1, 1, "MazurTorsion sample finding")]:
        raise GateError("linter parser self-check produced the wrong finding")
    try:
        parse_failed_run(
            root,
            ROOT_MODULE,
            sample.replace("Found 1 error", "Found 2 errors"),
        )
    except GateError:
        pass
    else:
        raise GateError("linter parser accepted a mismatched finding count")
    try:
        validate_linter_inventory(
            ROOT_MODULE,
            sample.replace("  tacticDocs\n", ""),
        )
    except GateError:
        pass
    else:
        raise GateError("linter parser accepted an incomplete linter inventory")
    print("MazurTorsion linter ratchet parser passed its self-check")


def enforce(root: Path) -> None:
    require_no_waiver_file(root)
    touched = touched_sources(root)
    if not touched:
        print(f"No MazurTorsion Lean sources were touched after cutoff {SOURCE_CUTOFF}")
        return

    if root.resolve() != regular_cache.ROOT.resolve():
        raise GateError("regular-cache source graph belongs to a different checkout")
    try:
        regular_cache.check()
        audit_cache.check()
    except (OSError, RecursionError, ValueError) as error:
        raise GateError(f"integrated source graph is invalid: {error}") from error
    integrated = {
        path.relative_to(root)
        for path in regular_cache.SOURCES.values()
    }
    if touched - integrated:
        unknown = ", ".join(str(path) for path in sorted(touched - integrated))
        raise GateError(f"touched sources are absent from the integrated graph: {unknown}")

    public_modules = regular_cache.local_closure(ROOT_MODULE)
    public_paths = {
        regular_cache.SOURCES[module].relative_to(root)
        for module in public_modules
    }
    lint_targets: set[str] = set()
    if touched & public_paths:
        lint_targets.add(ROOT_MODULE)

    audit_modules = audit_cache.audit_modules()
    audit_paths = {
        regular_cache.SOURCES[module].relative_to(root): module
        for module in audit_modules
    }
    audit_targets = audit_cache.audit_targets()
    for path in touched - public_paths:
        module = audit_paths.get(path)
        if module is None:
            raise GateError(f"touched source has no public or audit owner: {path}")
        covering_targets = [
            target
            for target in audit_targets
            if module in regular_cache.local_closure(target)
        ]
        if not covering_targets:
            raise GateError(f"no linter target imports touched audit module {module}")
        # A declaration can acquire an environment-sensitive finding (notably
        # simpNF) in one maximal consumer but not another. Lint every maximal
        # audit environment that imports the touched module.
        lint_targets.update(covering_targets)

    findings = {
        finding
        for target in sorted(lint_targets)
        for finding in run_linter(root, target)
    }
    regressions = sorted(
        (finding for finding in findings if finding.path in touched),
        key=lambda finding: (
            finding.path.as_posix(),
            finding.line,
            finding.column,
            finding.message,
        ),
    )
    if regressions:
        for finding in regressions:
            print(
                f"{finding.path}:{finding.line}:{finding.column}: error: "
                f"{finding.message}"
            )
        raise GateError(
            f"{len(regressions)} linter finding(s) occur in MazurTorsion sources "
            f"touched after cutoff {SOURCE_CUTOFF}"
        )
    print(
        f"MazurTorsion linter ratchet passed for {len(touched)} touched source file(s); "
        f"{len(findings)} existing findings are confined to unchanged files"
    )


def ratchet_digest(root: Path) -> str:
    require_no_waiver_file(root)
    touched = touched_sources(root)
    digest = sha256()
    digest.update(f"mazur-linter-ratchet-v{RATCHET_SCHEMA}\0".encode())
    for value in (SOURCE_CUTOFF, LINTER_ENVIRONMENT_REFERENCE):
        digest.update(value.encode())
        digest.update(b"\0")
    for path in sorted(touched):
        digest.update(path.as_posix().encode())
        digest.update(b"\0")
    return digest.hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    command = sys.argv[1:] or ["enforce"]
    if command == ["cutoff"]:
        print(SOURCE_CUTOFF)
    elif command == ["check"]:
        self_check(root)
    elif command == ["digest"]:
        print(ratchet_digest(root))
    elif command == ["enforce"]:
        enforce(root)
    else:
        raise GateError("usage: lint_changed_lean.py [check|cutoff|digest|enforce]")


if __name__ == "__main__":
    try:
        main()
    except GateError as error:
        raise SystemExit(f"MazurTorsion linter ratchet failed: {error}") from error
