# Mazur Theorem

**A public Lean 4 formalization of the classification of rational torsion on elliptic curves.**

[![Lean CI](https://github.com/Vilin97/MazurTheorem/actions/workflows/ci.yml/badge.svg)](https://github.com/Vilin97/MazurTheorem/actions/workflows/ci.yml)
[![Coordination site](https://img.shields.io/badge/roadmap-live-0d6b57)](https://mazur-theorem-formalization.vilin402100.chatgpt.site/)
[![License](https://img.shields.io/github/license/Vilin97/MazurTheorem)](LICENSE)

## The theorem this project is proving

The canonical target is the group-structure statement of Mazur's theorem:

```lean
theorem rationalTorsion_hasMazurClassification
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    HasMazurClassification E
```

Here `HasMazurClassification E` says that the rational torsion subgroup is
isomorphic to one of the eleven cyclic groups or four bicyclic groups in
Mazur's list.

The repository also owns the immutable Lean Pool contract

```lean
theorem torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

That numerical theorem is an important release endpoint, but it is not a
definition of the full classification: `Set.ncard` is zero on an infinite
set, so the literal inequality alone proves neither finiteness nor group
structure. The roadmap therefore records the full classification and the
challenge corollary separately.

## Current strategy

The project uses Mazur's degree-one formal-immersion argument at the auxiliary
prime `5`. The public prime-order proof will consume one route-neutral witness:
a cusp-normalized modular map, formal immersion at infinity modulo `5`, and
torsion of the particular image under consideration. The modular Jacobian,
Hecke action, Eisenstein quotient, and its finite Mordell–Weil proof are the
private constructor of that witness.

This separation keeps the critical theorem interface small without hiding its
mathematical cost. Modern winding-quotient and modular-symbol expositions do
not shorten the formalization cone in degree one; they add analytic-rank,
homology, or Hecke-independence infrastructure. The detailed comparison and
sources are in [the route audit](docs/ROUTE_AUDIT.md).

Three foundation lanes are active, with one current work package in each:

1. coherent cohomology → relative Picard → represented Jacobian and Abel–Jacobi;
2. honest finite-flat cyclic subgroups → represented `X₀(N)` → an order-49 vertical slice;
3. genuine Néron specialization → the private Eisenstein witness constructor.

Conditional order-specific explorations are paused while these foundations are
unfinished. Their Challenge statements remain immutable and compiled, but are
not currently claimable. This is an execution pause, not a mathematical claim
that the endpoints are unnecessary.

## Progress and roadmap

[`coordination/program.json`](coordination/program.json) is the canonical
ledger. It contains the fixed 48-node, 1,000-point theorem DAG, the three-lane
execution plan, nested work packages, paused contracts, and the two release
endpoints. Node weights and the conservative integrated-progress rules are
unchanged by the architecture refactor. Work packages partition a parent
node's planning allocation and earn no independent credit.

The current integrated score is **15.7%**; the ecosystem-readiness estimate is
**16%**. These values count only checked work connected to the acceptance API
defined by the ledger. Generated code volume, drafted interfaces, and isolated
proofs do not inflate the headline.

Use the [live roadmap](https://mazur-theorem-formalization.vilin402100.chatgpt.site/)
for the execution view and the [Verso blueprint](https://vilin97.github.io/MazurTheorem/blueprint/)
for the theorem dependency graph. Both are projections of the same ledger.

## Repository map

- [`MazurTorsion/`](MazurTorsion/) — checked theorem development;
- [`EllipticCurves/`](EllipticCurves/) — attributed exact-pin reduction infrastructure;
- [`MazurTorsion/Upstream/`](MazurTorsion/Upstream/) — reviewed upstream geometry ports and adapters;
- [`Challenge/`](Challenge/) — immutable contracts and checked solved bridges;
- [`coordination/program.json`](coordination/program.json) — canonical roadmap and execution data;
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — canonical/provisional object boundaries;
- [`docs/TECHNICAL_BLUEPRINT.md`](docs/TECHNICAL_BLUEPRINT.md) — compact declaration-level design;
- [`docs/INFORMAL_PROOF.md`](docs/INFORMAL_PROOF.md) — mathematical proof spine;
- [`blueprint/`](blueprint/) — generated theorem-first Verso view;
- [`site/`](site/) — generated public coordination view;
- [`upstream/tauceti/`](upstream/tauceti/) — separate exact-pin upstream contract package;
- [`archive/drafts/`](archive/drafts/) — unverified historical scratch, excluded from proof and progress.

The project began as the `mazur-torsion` branch of
[Vilin97/Clawristotle](https://github.com/Vilin97/Clawristotle).
[`ORIGIN.md`](ORIGIN.md) records the exact source commit, subtree hash, and
history-preserving split.

## Contributing

Start with [`CONTRIBUTING.md`](CONTRIBUTING.md) and
[`docs/CLAIMING.md`](docs/CLAIMING.md). Claim only a contract marked `open` or
`research_open` in the current ledger. A `paused` contract is intentionally
not available for new proof volume.

New foundational interfaces require design review and a named downstream
consumer. In particular:

- point-level rational cyclic-subgroup data are not a represented modular curve;
- an abstract Picard group is not a Jacobian scheme;
- a supplied group object is not a construction of the Weierstrass group law;
- a Néron-model mapping property does not prove existence of a Néron model.

Contributions should cross one of these boundaries honestly, not add another
conditional wrapper around it.

## Build and verification

The package is pinned to Lean `v4.33.0-rc1` and a matching exact Mathlib
revision. Fetch the compiled cache before building:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build MazurTorsion.Path.To.SmallestTouchedModule
python3 scripts/quality.py
```

The canonical roadmap projections are synchronized with:

```sh
python3 scripts/sync_roadmap_docs.py
python3 scripts/sync_roadmap_docs.py --check
```

Full cold-library, Blueprint, site, and documentation builds run in CI.
Contributors should build the smallest touched module locally unless a broader
build is explicitly requested.

Checked implementation must remain placeholder-free, warning-free, and free
of custom axioms, `unsafe`, and `partial`. Open declarations are permitted only
as registered whole-body `:= sorry` contracts under `Challenge/`. The only
foundational axioms accepted by the release audit are `propext`, `Quot.sound`,
and `Classical.choice`.

Licensing and provenance are recorded in [`LICENSE`](LICENSE),
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md), [`PORTING.md`](PORTING.md),
and [`docs/PRIOR_ART.md`](docs/PRIOR_ART.md).
