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
import stat
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
CACHE_FORMAT_VERSION = 2
IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import(?:\s+all)?\s+([A-Za-z0-9_'.]+)\s*$",
    re.MULTILINE,
)


@dataclass(frozen=True)
class Shard:
    targets: tuple[str, ...]
    artifacts: tuple[str, ...]
    predecessors: tuple[str, ...] = ()


def recurrence_shard(
    recurrence: int,
    *,
    targets: tuple[str, ...],
    artifacts: tuple[str, ...],
    predecessors: tuple[str, ...],
) -> Shard:
    """Build a shard below one generated recurrence lookup prefix."""
    module_prefix = (
        "MazurTorsion.Kubert."
        f"OrderSevenBacktrackingResultantRecurrence{recurrence}Lookup"
    )
    artifact_prefix = (
        "MazurTorsion/Kubert/"
        f"OrderSevenBacktrackingResultantRecurrence{recurrence}Lookup"
    )
    return Shard(
        targets=tuple(f"{module_prefix}{suffix}" for suffix in targets),
        artifacts=tuple(f"{artifact_prefix}{suffix}" for suffix in artifacts),
        predecessors=predecessors,
    )


SHARDS: dict[str, Shard] = {
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
        predecessors=("seed",),
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
        predecessors=("seed",),
    ),
    "r0": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence0*",
        ),
        predecessors=("seed",),
    ),
    "r1": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence1*",
        ),
        predecessors=("seed",),
    ),
    "r6": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantRecurrence6*",
        ),
        predecessors=("seed",),
    ),
    "bridge": Shard(
        targets=(
            "MazurTorsion.Kubert.OrderSevenBacktrackingResultantObstruction",
        ),
        artifacts=(
            "MazurTorsion/Kubert/OrderSevenBacktrackingObstruction",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantCertificate",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantFactors",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantObstruction",
            "MazurTorsion/Kubert/OrderSevenBacktrackingResultantSymmetry",
            "MazurTorsion/Kubert/OrderSevenBacktrackingSymmetry",
        ),
    ),
}


# The three largest recurrences contain ample module-level parallelism, but a
# single two-worker runner left most of that DAG idle and took up to four
# hours.  These disjoint shards expose the existing base -> product -> scalar
# -> final waves to separate runners.  `check` below proves that the manifest
# owns every generated source exactly once and that each target closure is
# supplied by its declared predecessors.
SHARDS.update(
    {
        "r2-base-a": recurrence_shard(
            2,
            targets=("Definitions", "A0", "A1", "A2", "A3", "A4", "A5", "A6"),
            artifacts=("Definitions", "A[0-5]*", "A6", "A6High", "A6Low"),
            predecessors=("seed",),
        ),
        "r2-base-b": recurrence_shard(
            2,
            targets=("B0", "B1", "B2", "B3", "B4", "B5"),
            artifacts=("B[0-3]*", "B4", "B4High", "B4Low", "B5", "B5High", "B5Low"),
            predecessors=("seed",),
        ),
        "r2-base-c": recurrence_shard(
            2,
            targets=("C0", "C1", "C2", "C3", "C4"),
            artifacts=("C*",),
            predecessors=("seed",),
        ),
        "r4-base-a": recurrence_shard(
            4,
            targets=("Definitions", "A0", "A1", "A2", "A3", "A4"),
            artifacts=("Definitions", "A[0-3]*", "A4", "A4High", "A4Low"),
            predecessors=("seed",),
        ),
        "r4-base-b": recurrence_shard(
            4,
            targets=("B0", "B1", "B2", "B3"),
            artifacts=("B[0-1]*", "B2", "B2High", "B2Low", "B3", "B3High", "B3Low"),
            predecessors=("seed",),
        ),
        "r4-base-c": recurrence_shard(
            4,
            targets=("C0", "C1", "C2"),
            artifacts=("C*",),
            predecessors=("seed",),
        ),
        "r5-base-a": recurrence_shard(
            5,
            targets=("Definitions", "A0", "A1", "A2", "A3"),
            artifacts=("Definitions", "A[0-2]*", "A3", "A3High", "A3Low"),
            predecessors=("seed",),
        ),
        "r5-base-b": recurrence_shard(
            5,
            targets=("B0", "B1", "B2"),
            artifacts=("B0*", "B1", "B1High", "B1Low", "B2", "B2High", "B2Low"),
            predecessors=("seed",),
        ),
        "r5-base-c": recurrence_shard(
            5,
            targets=("C0", "C1"),
            artifacts=("C*",),
            predecessors=("seed",),
        ),
        "r2-products-a": recurrence_shard(
            2,
            targets=("LeadingSquare", "B5A5", "B5A6", "B4A6", "QuotientConstant"),
            artifacts=("LeadingSquare*", "B5A5*", "B5A6*", "B4A6*", "QuotientConstant"),
            predecessors=("r2-base-a", "r2-base-b"),
        ),
        "r2-products-b": recurrence_shard(
            2,
            targets=("A6Square", "ExceptionalProduct"),
            artifacts=("A6Square*", "Exceptional", "ExceptionalProduct*"),
            predecessors=("r2-base-a",),
        ),
        "r4-products-a": recurrence_shard(
            4,
            targets=("LeadingSquare", "B3A3", "B2A4", "B3A4", "QuotientConstant"),
            artifacts=("LeadingSquare*", "B3A3*", "B2A4*", "B3A4*", "QuotientConstant"),
            predecessors=("r4-base-a", "r4-base-b"),
        ),
        "r4-products-b": recurrence_shard(
            4,
            targets=("A4Square", "ExceptionalProduct"),
            artifacts=("A4Square*", "ExceptionalData", "Exceptional", "ExceptionalProduct*"),
            predecessors=("r4-base-a",),
        ),
        "r5-products-a": recurrence_shard(
            5,
            targets=("LeadingSquare", "B2A2", "B1A3", "QuotientConstant"),
            artifacts=("LeadingSquare*", "B2A2*", "B1A3*", "QuotientConstant"),
            predecessors=("r5-base-a", "r5-base-b"),
        ),
        "r5-products-b": recurrence_shard(
            5,
            targets=("B2A3", "A3Square", "ExceptionalProduct"),
            artifacts=("B2A3*", "A3Square*", "ExceptionalData", "Exceptional", "ExceptionalProduct*"),
            predecessors=("r5-base-a", "r5-base-b"),
        ),
        "r2-scalars-0": recurrence_shard(
            2,
            targets=("Scalar0Exceptional", "Scalar1Left"),
            artifacts=("Scalar0Exceptional*", "Scalar1Left*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r2-scalars-1": recurrence_shard(
            2,
            targets=("Scalar0Main", "Scalar4Exceptional", "Scalar4Left"),
            artifacts=("Scalar0Main*", "Scalar4Exceptional*", "Scalar4Left*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r2-scalars-2": recurrence_shard(
            2,
            targets=("Scalar1Exceptional", "Scalar3Shift"),
            artifacts=("Scalar1Exceptional*", "Scalar3Shift*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r2-scalars-3": recurrence_shard(
            2,
            targets=("Scalar1Main", "Scalar3Main", "Scalar4Shift"),
            artifacts=("Scalar1Main*", "Scalar3Main*", "Scalar4Shift*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r2-scalars-4": recurrence_shard(
            2,
            targets=("Scalar1Shift", "Scalar0Left", "Scalar3Left"),
            artifacts=("Scalar1Shift*", "Scalar0Left*", "Scalar3Left*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r2-scalars-5": recurrence_shard(
            2,
            targets=("Scalar2Exceptional", "Scalar3Exceptional", "Scalar2Left"),
            artifacts=("Scalar2Exceptional*", "Scalar3Exceptional*", "Scalar2Left*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r2-scalars-6": recurrence_shard(
            2,
            targets=("Scalar2Main", "Scalar2Shift", "Scalar4Main"),
            artifacts=("Scalar2Main*", "Scalar2Shift*", "Scalar4Main*"),
            predecessors=("r2-base-a", "r2-base-b", "r2-base-c", "r2-products-a", "r2-products-b"),
        ),
        "r4-scalars-0": recurrence_shard(
            4,
            targets=("Scalar2Left", "Scalar2Exceptional"),
            artifacts=("Scalar2Left*", "Scalar2Exceptional*"),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-1": recurrence_shard(
            4,
            targets=("Scalar0Left",),
            artifacts=("Scalar0Left*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-2": recurrence_shard(
            4,
            targets=("Scalar1Left",),
            artifacts=("Scalar1Left*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-3": recurrence_shard(
            4,
            targets=("Scalar0Exceptional",),
            artifacts=("Scalar0Exceptional*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-4": recurrence_shard(
            4,
            targets=("Scalar0Main",),
            artifacts=("Scalar0Main*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-5": recurrence_shard(
            4,
            targets=("Scalar1Exceptional",),
            artifacts=("Scalar1Exceptional*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-6": recurrence_shard(
            4,
            targets=("Scalar1Second",),
            artifacts=("Scalar1Second*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-7": recurrence_shard(
            4,
            targets=("Scalar1First",),
            artifacts=("Scalar1First*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-8": recurrence_shard(
            4,
            targets=("Scalar2First",),
            artifacts=("Scalar2First*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r4-scalars-9": recurrence_shard(
            4,
            targets=("Scalar2Second",),
            artifacts=("Scalar2Second*",),
            predecessors=("r4-base-a", "r4-base-b", "r4-base-c", "r4-products-a", "r4-products-b"),
        ),
        "r5-scalars-0": recurrence_shard(
            5,
            targets=("Scalar0Main", "Scalar1Exceptional"),
            artifacts=("Scalar0Main*", "Scalar1Exceptional*"),
            predecessors=("r5-base-a", "r5-base-b", "r5-base-c", "r5-products-a", "r5-products-b"),
        ),
        "r5-scalars-1": recurrence_shard(
            5,
            targets=("Scalar1Left", "Scalar1Second"),
            artifacts=("Scalar1Left*", "Scalar1Second*"),
            predecessors=("r5-base-a", "r5-base-b", "r5-base-c", "r5-products-a", "r5-products-b"),
        ),
        "r5-scalars-2": recurrence_shard(
            5,
            targets=("Scalar0Left", "Scalar0Exceptional"),
            artifacts=("Scalar0Left*", "Scalar0Exceptional*"),
            predecessors=("r5-base-a", "r5-base-b", "r5-base-c", "r5-products-a", "r5-products-b"),
        ),
        "r5-scalars-3": recurrence_shard(
            5,
            targets=("Scalar1First",),
            artifacts=("Scalar1First*",),
            predecessors=("r5-base-a", "r5-base-b", "r5-base-c", "r5-products-a", "r5-products-b"),
        ),
        "r2-final": recurrence_shard(
            2,
            targets=("",),
            artifacts=("ScalarResidual*", ""),
            predecessors=tuple(f"r2-scalars-{index}" for index in range(7)),
        ),
        "r4-final": recurrence_shard(
            4,
            targets=("",),
            artifacts=("Scalar", ""),
            predecessors=tuple(f"r4-scalars-{index}" for index in range(10)),
        ),
        "r5-final": recurrence_shard(
            5,
            targets=("",),
            artifacts=("Scalar", ""),
            predecessors=tuple(f"r5-scalars-{index}" for index in range(4)),
        ),
    }
)


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


def dependency_order(shard_name: str) -> list[str]:
    """Return every predecessor once, in restore-before-dependent order."""
    ordered: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in visiting:
            raise ValueError(f"Order Seven shard dependency cycle at {name}")
        if name not in SHARDS:
            raise ValueError(f"unknown Order Seven shard predecessor: {name}")
        visiting.add(name)
        for predecessor in SHARDS[name].predecessors:
            visit(predecessor)
        visiting.remove(name)
        visited.add(name)
        if name != shard_name:
            ordered.append(name)

    visit(shard_name)
    return ordered


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


def archive_paths(shard_name: str, staging_root: Path) -> list[Path]:
    """Validate a staged archive and return its exact regular-file members."""
    staging_root = staging_root.resolve()
    if not staging_root.is_dir():
        raise ValueError(f"archive staging directory does not exist: {staging_root}")

    allowed_stems = {
        build_root / source.with_suffix("")
        for source in artifact_sources(SHARDS[shard_name])
        for build_root in BUILD_ROOTS
    }
    paths: list[Path] = []
    required_olean = {
        BUILD_ROOTS[0] / source.with_suffix("").with_suffix(".olean")
        for source in artifact_sources(SHARDS[shard_name])
    }
    required_trace = {
        BUILD_ROOTS[0] / source.with_suffix("").with_suffix(".trace")
        for source in artifact_sources(SHARDS[shard_name])
    }

    for directory, directory_names, file_names in os.walk(
        staging_root, followlinks=False
    ):
        directory_path = Path(directory)
        for name in directory_names:
            child = directory_path / name
            if child.is_symlink():
                raise ValueError(f"archive contains a symbolic link: {child}")
        for name in file_names:
            child = directory_path / name
            metadata = child.lstat()
            if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
                raise ValueError(f"archive member is not an independent file: {child}")
            relative = child.relative_to(staging_root)
            if not any(
                relative.parent == stem.parent
                and relative.name.startswith(f"{stem.name}.")
                for stem in allowed_stems
            ):
                raise ValueError(f"unexpected archive member: {relative}")
            paths.append(relative)

    found = set(paths)
    missing = sorted((required_olean | required_trace) - found)
    if missing:
        raise ValueError(
            "archive is missing required artifacts: "
            + ", ".join(path.as_posix() for path in missing)
        )
    return sorted(paths)


def install_archive(shard_name: str, staging_root: Path) -> None:
    """Move a validated shard from isolated staging into the Lake build tree."""
    staging_root = staging_root.resolve()
    for relative in archive_paths(shard_name, staging_root):
        destination = ROOT / relative
        current = ROOT
        for part in relative.parent.parts:
            current /= part
            if current.exists():
                if current.is_symlink() or not current.is_dir():
                    raise ValueError(f"unsafe archive destination parent: {current}")
            else:
                try:
                    current.mkdir()
                except FileExistsError:
                    # Parallel disjoint shard restores may create the same
                    # trusted build-tree parent between the check and mkdir.
                    if current.is_symlink() or not current.is_dir():
                        raise ValueError(
                            f"unsafe archive destination parent: {current}"
                        )
        if destination.exists() and (
            destination.is_symlink() or not destination.is_file()
        ):
            raise ValueError(f"unsafe archive destination: {destination}")
        os.replace(staging_root / relative, destination)


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
        dependencies = dependency_order(name)
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

        # The bridge is assembled by the complete library consumer after it
        # restores every OCI lane. All OCI producer shards, however, must
        # declare enough predecessors that Lake cannot silently rebuild an
        # artifact owned by a different lane.
        if name != "bridge":
            available = set(sources)
            for dependency in dependencies:
                available.update(artifact_sources(SHARDS[dependency]))
            required = {
                path
                for path in closure
                if path.name.startswith("OrderSeven")
            }
            missing_dependencies = required - available
            if missing_dependencies:
                rendered = ", ".join(
                    path.as_posix() for path in sorted(missing_dependencies)
                )
                raise ValueError(
                    f"{name} has undeclared Order Seven dependencies: {rendered}"
                )

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
    for command in ("dependencies", "digest", "targets", "paths", "reference"):
        child = subparsers.add_parser(command)
        child.add_argument("shard", choices=SHARDS)
    layers_parser = subparsers.add_parser("layers")
    layers_parser.add_argument("shard", choices=SHARDS)
    layers_parser.add_argument("manifest", type=Path)
    install_parser = subparsers.add_parser("install")
    install_parser.add_argument("shard", choices=SHARDS)
    install_parser.add_argument("staging_root", type=Path)
    subparsers.add_parser("lanes")
    subparsers.add_parser("check")
    args = parser.parse_args()

    try:
        if args.command == "lanes":
            # The small final bridge lives in GitHub Actions' branch-scoped
            # cache. Only the generated lanes need OCI storage.
            print("\n".join(name for name in SHARDS if name != "bridge"))
        elif args.command == "check":
            check()
        elif args.command == "digest":
            print(digest(args.shard))
        elif args.command == "dependencies":
            print("\n".join(dependency_order(args.shard)))
        elif args.command == "targets":
            print("\n".join(SHARDS[args.shard].targets))
        elif args.command == "paths":
            print("\n".join(path.as_posix() for path in artifact_paths(args.shard)))
        elif args.command == "reference":
            print(reference(args.shard))
        elif args.command == "layers":
            print("\n".join(layer_digests(args.shard, args.manifest)))
        elif args.command == "install":
            install_archive(args.shard, args.staging_root)
    except (json.JSONDecodeError, OSError, ValueError) as error:
        print(f"order-seven cache error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
