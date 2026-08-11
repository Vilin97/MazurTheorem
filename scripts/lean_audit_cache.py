#!/usr/bin/env python3
"""Describe compiled modules loaded only by the exhaustive axiom audit."""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

import lean_regular_cache as regular


ROOT = regular.ROOT
CACHE_FORMAT_VERSION = 1
CONFIG_INPUTS = (
    *regular.CONFIG_INPUTS,
    Path("scripts/lean_regular_cache.py"),
    Path("scripts/lean_audit_cache.py"),
)


def audit_modules() -> set[str]:
    """Modules enumerated by ``axioms`` but unreachable from public roots."""

    return set(regular.SOURCES) - regular.root_closure()


def audit_targets() -> set[str]:
    """Maximal audit-only modules whose builds cover every owned module."""

    modules = audit_modules()
    imported_by_audit = set().union(
        *(regular.IMPORTS[module] & modules for module in modules)
    )
    return modules - imported_by_audit


def audit_closure() -> set[str]:
    return set().union(
        *(regular.local_closure(target) for target in audit_targets())
    )


def digest() -> str:
    result = hashlib.sha256(
        f"lean-audit-modules-v{CACHE_FORMAT_VERSION}\0".encode()
    )
    inputs = set(CONFIG_INPUTS)
    inputs.update(
        regular.SOURCES[module].relative_to(ROOT) for module in audit_closure()
    )
    for path in sorted(inputs):
        data = (ROOT / path).read_bytes()
        encoded = path.as_posix().encode()
        result.update(len(encoded).to_bytes(4, "big"))
        result.update(encoded)
        result.update(len(data).to_bytes(8, "big"))
        result.update(data)
    return result.hexdigest()


def check() -> None:
    public = regular.root_closure()
    owned = audit_modules()
    integrated = set(regular.SOURCES)
    if public & owned or public | owned != integrated:
        raise ValueError("public and audit-only modules do not partition all sources")
    if not owned:
        raise ValueError("the audit-only cache unexpectedly owns no modules")

    closure = audit_closure()
    if not owned <= closure:
        missing = ", ".join(sorted(owned - closure))
        raise ValueError(f"audit targets do not cover owned modules: {missing}")
    heavy = {
        module
        for module in closure
        if module.startswith(regular.HEAVY_PREFIXES)
    }
    if heavy:
        rendered = ", ".join(sorted(heavy))
        raise ValueError(f"audit-only closure reaches generated modules: {rendered}")
    duplicated_seed = closure & regular.ORDER_SEVEN_SEED_OWNED
    if duplicated_seed:
        rendered = ", ".join(sorted(duplicated_seed))
        raise ValueError(f"audit-only closure reaches Order Seven seed modules: {rendered}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=("check", "digest", "paths", "schema", "targets"),
    )
    args = parser.parse_args()
    try:
        if args.command == "check":
            check()
        elif args.command == "digest":
            print(digest())
        elif args.command == "paths":
            print("\n".join(regular.artifact_patterns(audit_modules())))
        elif args.command == "schema":
            print(CACHE_FORMAT_VERSION)
        elif args.command == "targets":
            print("\n".join(sorted(audit_targets())))
    except (OSError, RecursionError, ValueError) as error:
        print(f"Lean audit cache error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
