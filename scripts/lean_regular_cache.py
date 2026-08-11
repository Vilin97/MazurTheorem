#!/usr/bin/env python3
"""Describe the regular Lean cache that can build beside generated proofs."""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from functools import cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CACHE_FORMAT_VERSION = 2
ROOT_MODULES = ("MazurTorsion", "EllipticCurves")
HEAVY_PREFIXES = (
    "MazurTorsion.Kubert.OrderSeven",
    "MazurTorsion.Kubert.OrderTwentyFive",
    "MazurTorsion.Kubert.OrderTwentySeven",
)
IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import(?:\s+all)?\s+([A-Za-z0-9_'.]+)\s*$",
    re.MULTILINE,
)
CONFIG_INPUTS = (
    Path("lean-toolchain"),
    Path("lake-manifest.json"),
    Path("lakefile.toml"),
    Path("upstream/tauceti/lean-toolchain"),
    Path("upstream/tauceti/lake-manifest.json"),
)

# These five small, shared prerequisites travel with the Order Seven seed so
# every generated-proof lane can build after restoring only that seed.  Keep
# them out of the Actions base archive to avoid storing and downloading the
# same artifacts from both Actions cache and GHCR.
ORDER_SEVEN_SEED_OWNED = {
    "MazurTorsion.EllipticCurve.DoublingCoordinates",
    "MazurTorsion.EllipticCurve.VariableChange",
    "MazurTorsion.EllipticCurve.VeluPair",
    "MazurTorsion.Kubert.TateNormalForm",
    "MazurTorsion.Kubert.TateNormalFormMultiples",
}

# These modules depend on generated families, or belong to Order Twenty Seven
# but are not transported by its three specialized caches. They stay in the
# tiny downstream cache completed by the authoritative full-library build.
EXPECTED_DOWNSTREAM = {
    "MazurTorsion",
    "MazurTorsion.Arithmetic.PointOrder",
    "MazurTorsion.Kubert.OrderTwentyOne",
    "MazurTorsion.Kubert.OrderTwentyOneExceptionalJ",
    "MazurTorsion.Kubert.OrderTwentyOneReduction",
    "MazurTorsion.Kubert.OrderTwentySevenEndpoint",
    "MazurTorsion.Kubert.OrderTwentySevenLegs",
    "MazurTorsion.Kubert.OrderTwentySevenReduction",
    "MazurTorsion.Kubert.OrderTwentySevenTrisection",
    "MazurTorsion.NumberTheory.XZeroFortyNineEllipticQuotient",
    "MazurTorsion.NumberTheory.XZeroFortyNineTransfer",
    "MazurTorsion.NumberTheory.XZeroTwentySevenClassification",
}


def source_map() -> dict[str, Path]:
    paths = [
        *ROOT.glob("MazurTorsion/**/*.lean"),
        *ROOT.glob("EllipticCurves/**/*.lean"),
        ROOT / "MazurTorsion.lean",
        ROOT / "EllipticCurves.lean",
    ]
    return {
        path.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): path
        for path in paths
        if path.is_file()
    }


SOURCES = source_map()
IMPORTS = {
    module: {
        imported
        for imported in IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        if imported in SOURCES
    }
    for module, path in SOURCES.items()
}


@cache
def local_closure(module: str) -> frozenset[str]:
    closure = {module}
    for imported in IMPORTS[module]:
        closure.update(local_closure(imported))
    return frozenset(closure)


def root_closure() -> set[str]:
    return set().union(*(local_closure(module) for module in ROOT_MODULES))


def heavy_modules() -> set[str]:
    return {
        module
        for module in root_closure()
        if module.startswith(HEAVY_PREFIXES)
    }


def base_modules() -> set[str]:
    heavy = heavy_modules()
    return {
        module
        for module in root_closure()
        if local_closure(module).isdisjoint(heavy)
    }


def base_targets() -> set[str]:
    base = base_modules()
    imported_by_base = set().union(*(IMPORTS[module] & base for module in base))
    return base - imported_by_base


def downstream_modules() -> set[str]:
    reachable = root_closure()
    heavy = heavy_modules()
    dependent_nonheavy = {
        module
        for module in reachable - heavy
        if not local_closure(module).isdisjoint(heavy)
    }
    uncovered_order_twenty_seven = {
        module
        for module in heavy
        if module in EXPECTED_DOWNSTREAM
    }
    return dependent_nonheavy | uncovered_order_twenty_seven


def digest() -> str:
    result = hashlib.sha256(
        f"lean-regular-base-v{CACHE_FORMAT_VERSION}\0".encode()
    )
    inputs = set(CONFIG_INPUTS)
    inputs.update(SOURCES[module].relative_to(ROOT) for module in base_modules())
    for path in sorted(inputs):
        data = (ROOT / path).read_bytes()
        encoded = path.as_posix().encode()
        result.update(len(encoded).to_bytes(4, "big"))
        result.update(encoded)
        result.update(len(data).to_bytes(8, "big"))
        result.update(data)
    return result.hexdigest()


def artifact_patterns(modules: set[str]) -> list[str]:
    patterns = []
    for module in sorted(modules):
        stem = module.replace(".", "/")
        patterns.extend(
            (
                f".lake/build/lib/lean/{stem}.*",
                f".lake/build/ir/{stem}.*",
            )
        )
    return patterns


def check() -> None:
    reachable = root_closure()
    heavy = heavy_modules()
    base = base_modules()
    downstream = downstream_modules()
    if downstream != EXPECTED_DOWNSTREAM:
        missing = ", ".join(sorted(EXPECTED_DOWNSTREAM - downstream))
        extra = ", ".join(sorted(downstream - EXPECTED_DOWNSTREAM))
        raise ValueError(
            f"regular downstream cache changed; missing={missing}; extra={extra}"
        )
    specialized_heavy = heavy - downstream
    if base & downstream or base & specialized_heavy or downstream & specialized_heavy:
        raise ValueError("regular cache partitions overlap")
    if base | downstream | specialized_heavy != reachable:
        raise ValueError("regular cache partitions do not cover the root closure")
    if not ORDER_SEVEN_SEED_OWNED <= base:
        missing = ", ".join(sorted(ORDER_SEVEN_SEED_OWNED - base))
        raise ValueError(f"Order Seven seed prerequisites left the base: {missing}")
    covered_by_targets = set().union(*(local_closure(target) for target in base_targets()))
    if covered_by_targets & base != base:
        raise ValueError("regular base targets do not cover every base module")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=(
            "check",
            "digest",
            "downstream",
            "downstream-paths",
            "paths",
            "schema",
            "targets",
        ),
    )
    args = parser.parse_args()
    try:
        if args.command == "check":
            check()
        elif args.command == "digest":
            print(digest())
        elif args.command == "downstream":
            print("\n".join(sorted(downstream_modules())))
        elif args.command == "downstream-paths":
            print("\n".join(artifact_patterns(downstream_modules())))
        elif args.command == "paths":
            print(
                "\n".join(
                    artifact_patterns(base_modules() - ORDER_SEVEN_SEED_OWNED)
                )
            )
        elif args.command == "schema":
            print(CACHE_FORMAT_VERSION)
        elif args.command == "targets":
            print("\n".join(sorted(base_targets())))
    except (OSError, RecursionError, ValueError) as error:
        print(f"regular Lean cache error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
