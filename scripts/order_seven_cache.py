#!/usr/bin/env python3
"""Describe and key the sharded Order Seven Lean build cache.

The generated Order Seven certificate is much larger than GitHub Actions'
repository cache allowance.  CI stores disjoint build-artifact shards in an
OCI registry instead.  This file is the single source of truth for the shard
targets, their artifact ownership, and their content keys.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOTS = (
    Path(".lake/build/lib/lean"),
    Path(".lake/build/ir"),
)
LAYER_MEDIA_TYPE = "application/vnd.mazurtheorem.lean-cache.layer.v1+zstd"
ARTIFACT_MEDIA_TYPE = "application/vnd.mazurtheorem.lean-cache.v1"
MAX_LAYER_BYTES = 512 * 1024 * 1024
MAX_LAYER_COUNT = 64
MAX_TOTAL_LAYER_BYTES = 16 * 1024 * 1024 * 1024
CACHE_FORMAT_VERSION = 1
IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import(?:\s+all)?\s+([A-Za-z0-9_'.]+)\s*$",
    re.MULTILINE,
)


@dataclass(frozen=True)
class Shard:
    targets: tuple[str, ...]
    artifacts: tuple[str, ...]


SHARDS = {
    "seed": Shard(
        targets=(
            "MazurTorsion.Kubert."
            "OrderSevenBacktrackingResultantCertificateData6",
        ),
        artifacts=(
            "MazurTorsion/EllipticCurve/DoublingCoordinates",
            "MazurTorsion/EllipticCurve/VariableChange",
            "MazurTorsion/EllipticCurve/VeluPair",
            "MazurTorsion/Kubert/TateNormalForm",
            "MazurTorsion/Kubert/TateNormalFormMultiples",
            "MazurTorsion/Kubert/OrderSevenParametrization",
            "MazurTorsion/Kubert/OrderSevenCorrespondence",
            "MazurTorsion/Kubert/OrderSevenHauptmodul",
            "MazurTorsion/Kubert/OrderSevenHauptmodulClearing",
            "MazurTorsion/Kubert/OrderSevenIsogeny",
            "MazurTorsion/Kubert/OrderSevenBacktrackingSelection",
            "MazurTorsion/Kubert/OrderSevenBacktrackingCertificateData",
            "MazurTorsion/Kubert/OrderSevenDualKernel",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantCertificateData*",
        ),
    ),
    "factor": Shard(
        targets=("MazurTorsion.Kubert.OrderSevenBacktrackingFactorCertificate",),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingDivisionCertificateEval*",
            "MazurTorsion/Kubert/OrderSevenBacktrackingSelectionCertificateEval*",
            "MazurTorsion/Kubert/OrderSevenBacktrackingFactorCertificate",
        ),
    ),
    "auxiliary": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenIsogenyDoubling",
            "MazurTorsion.Kubert.OrderSevenDualKernelPullback",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenIsogenyDoubling*",
            "MazurTorsion/Kubert/OrderSevenIsogenyPolynomialData",
            "MazurTorsion/Kubert/OrderSevenDualKernelCertificate*",
            "MazurTorsion/Kubert/OrderSevenDualKernelPullback",
        ),
    ),
    "r0": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence0*",
        ),
    ),
    "r1": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence1*",
        ),
    ),
    "r2": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2Lookup",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence2*",
        ),
    ),
    "r4": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4Lookup",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence4*",
        ),
    ),
    "r5": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5Lookup",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence5*",
        ),
    ),
    "r6": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence6*",
        ),
    ),
    "bridge": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantObstruction",
        ),
        artifacts=(
            "MazurTorsion/Foundations/DivisionPolynomialRootCriterion",
            "MazurTorsion/Foundations/OddPrimeFullTorsion",
            "MazurTorsion/Foundations/Polynomial/BoundedResultant",
            "MazurTorsion/Foundations/ThreeTorsion",
            "MazurTorsion/Kubert/OrderSevenBacktrackingObstruction",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantCertificate",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantFactors",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantObstruction",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantSymmetry",
            "MazurTorsion/Kubert/OrderSevenBacktrackingSymmetry",
        ),
    ),
}


def source_path(module: str) -> Path | None:
    path = Path(*module.split(".")).with_suffix(".lean")
    return path if (ROOT / path).is_file() else None


def local_closure(targets: tuple[str, ...]) -> set[Path]:
    pending = list(targets)
    visited: set[str] = set()
    sources: set[Path] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        path = source_path(module)
        if path is None:
            continue
        sources.add(path)
        text = (ROOT / path).read_text(encoding="utf-8")
        pending.extend(IMPORT_RE.findall(text))
    return sources


def artifact_sources(shard: Shard) -> set[Path]:
    paths: set[Path] = set()
    for pattern in shard.artifacts:
        matches = set(ROOT.glob(f"{pattern}.lean"))
        if not matches:
            raise ValueError(f"artifact pattern has no source: {pattern}")
        paths.update(path.relative_to(ROOT) for path in matches)
    return paths


def digest(shard_name: str) -> str:
    inputs = local_closure(SHARDS[shard_name].targets)
    inputs.update(
        {
            Path("lean-toolchain"),
            Path("lake-manifest.json"),
            Path("lakefile.toml"),
        }
    )
    result = hashlib.sha256()
    result.update(f"order-seven-cache-v{CACHE_FORMAT_VERSION}\0".encode())
    # Artifact ownership is part of the cache contract. Operational changes
    # to the transport scripts do not force a multi-hour proof rebuild, while
    # moving or adding a module to a shard always changes its key.
    for path in sorted(artifact_sources(SHARDS[shard_name])):
        result.update(b"artifact\0")
        result.update(path.as_posix().encode())
        result.update(b"\0")
    for path in sorted(inputs):
        data = (ROOT / path).read_bytes()
        encoded_path = path.as_posix().encode()
        result.update(len(encoded_path).to_bytes(4, "big"))
        result.update(encoded_path)
        result.update(len(data).to_bytes(8, "big"))
        result.update(data)
    return result.hexdigest()


def artifact_paths(shard_name: str) -> list[Path]:
    paths: set[Path] = set()
    missing: list[str] = []
    for source in sorted(artifact_sources(SHARDS[shard_name])):
        stem = source.with_suffix("")
        found_olean = False
        found_trace = False
        for build_root in BUILD_ROOTS:
            for path in (ROOT / build_root).glob(f"{stem}.*"):
                relative = path.relative_to(ROOT)
                if path.is_file():
                    paths.add(relative)
                    if build_root == BUILD_ROOTS[0] and path.suffix == ".olean":
                        found_olean = True
                    if build_root == BUILD_ROOTS[0] and path.suffix == ".trace":
                        found_trace = True
        if not found_olean or not found_trace:
            missing.append(source.as_posix())
    if missing:
        raise ValueError("missing .olean/.trace artifacts for: " + ", ".join(missing))
    return sorted(paths)


def layer_digests(shard_name: str, manifest_path: Path) -> list[str]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("schemaVersion") != 2:
        raise ValueError("OCI manifest does not use schema version 2")
    if manifest.get("artifactType") != ARTIFACT_MEDIA_TYPE:
        raise ValueError("unexpected OCI artifact type")
    layers = manifest.get("layers")
    if not isinstance(layers, list) or not layers:
        raise ValueError("OCI manifest has no layers")
    if len(layers) > MAX_LAYER_COUNT:
        raise ValueError(f"OCI manifest has too many layers: {len(layers)}")
    digests: list[str] = []
    total_size = 0
    for index, layer in enumerate(layers):
        if not isinstance(layer, dict):
            raise ValueError("OCI layer descriptor is not an object")
        expected_title = f"{shard_name}.tar.zst.part-{index:04d}"
        annotations = layer.get("annotations")
        title = annotations.get("org.opencontainers.image.title") \
            if isinstance(annotations, dict) else None
        if title != expected_title:
            raise ValueError(
                f"unexpected OCI layer title {title!r}; expected {expected_title!r}"
            )
        if layer.get("mediaType") != LAYER_MEDIA_TYPE:
            raise ValueError(f"unexpected OCI layer media type for {expected_title}")
        size = layer.get("size")
        if not isinstance(size, int) or not 0 < size <= MAX_LAYER_BYTES:
            raise ValueError(f"invalid OCI layer size for {expected_title}: {size!r}")
        total_size += size
        digest_value = layer.get("digest")
        if not isinstance(digest_value, str) or not re.fullmatch(
            r"sha256:[0-9a-f]{64}", digest_value
        ):
            raise ValueError(f"invalid OCI layer digest for {expected_title}")
        digests.append(digest_value)
    if total_size > MAX_TOTAL_LAYER_BYTES:
        raise ValueError(f"OCI artifact is too large: {total_size} bytes")
    return digests


def check() -> None:
    owned: dict[Path, str] = {}
    for name, shard in SHARDS.items():
        closure = local_closure(shard.targets)
        sources = artifact_sources(shard)
        outside = sources - closure
        if outside:
            rendered = ", ".join(path.as_posix() for path in sorted(outside))
            raise ValueError(f"{name} owns sources outside its target closure: {rendered}")
        for path in sources:
            if path.name.startswith("OrderSeven"):
                previous = owned.setdefault(path, name)
                if previous != name:
                    raise ValueError(f"{path} is owned by both {previous} and {name}")

    expected = {
        path.relative_to(ROOT)
        for path in ROOT.glob("MazurTorsion/Kubert/OrderSeven*.lean")
    }
    actual = set(owned)
    if expected != actual:
        missing = ", ".join(path.as_posix() for path in sorted(expected - actual))
        extra = ", ".join(path.as_posix() for path in sorted(actual - expected))
        raise ValueError(f"Order Seven shard coverage mismatch; missing={missing}; extra={extra}")


def reference(shard_name: str) -> str:
    owner = os.environ.get("GITHUB_REPOSITORY_OWNER")
    runner_os = os.environ.get("RUNNER_OS")
    runner_arch = os.environ.get("RUNNER_ARCH")
    if not owner or not runner_os or not runner_arch:
        raise ValueError(
            "GITHUB_REPOSITORY_OWNER, RUNNER_OS, and RUNNER_ARCH are required"
        )
    tag = (
        f"order-seven-{shard_name}-v{CACHE_FORMAT_VERSION}-{runner_os.lower()}-"
        f"{runner_arch.lower()}-{digest(shard_name)}"
    )
    return f"ghcr.io/{owner.lower()}/mazurtheorem-lean-cache:{tag}"


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("digest", "targets", "paths", "reference"):
        child = subparsers.add_parser(command)
        child.add_argument("shard", choices=SHARDS)
    layers_parser = subparsers.add_parser("layers")
    layers_parser.add_argument("shard", choices=SHARDS)
    layers_parser.add_argument("manifest", type=Path)
    subparsers.add_parser("lanes")
    subparsers.add_parser("check")
    args = parser.parse_args()

    try:
        if args.command == "lanes":
            # The small final bridge lives in GitHub Actions' branch-scoped
            # cache. Only the nine enormous generated lanes need OCI storage.
            print("\n".join(name for name in SHARDS if name != "bridge"))
        elif args.command == "check":
            check()
        elif args.command == "digest":
            print(digest(args.shard))
        elif args.command == "targets":
            print("\n".join(SHARDS[args.shard].targets))
        elif args.command == "paths":
            print("\n".join(path.as_posix() for path in artifact_paths(args.shard)))
        elif args.command == "reference":
            print(reference(args.shard))
        elif args.command == "layers":
            print("\n".join(layer_digests(args.shard, args.manifest)))
    except (json.JSONDecodeError, OSError, ValueError) as error:
        print(f"order-seven cache error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
