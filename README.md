# Mazur Theorem

**A public, dependency-driven Lean 4 formalization of Mazur's torsion theorem.**

[![Lean CI](https://github.com/Vilin97/MazurTheorem/actions/workflows/ci.yml/badge.svg)](https://github.com/Vilin97/MazurTheorem/actions/workflows/ci.yml)
[![Coordination site](https://img.shields.io/badge/roadmap-live-0d6b57)](https://mazur-theorem-formalization.vilin402100.chatgpt.site/)
[![License](https://img.shields.io/github/license/Vilin97/MazurTheorem)](LICENSE)

Mazur's theorem classifies the possible rational torsion subgroups of an
elliptic curve over `ℚ`. This repository targets the exact Lean statement

```lean
theorem torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point :
      Set (E⁄ℚ).Point).ncard ≤ 16
```

The project began as the `mazur-torsion` branch of
[Vilin97/Clawristotle](https://github.com/Vilin97/Clawristotle). Its proof
history was preserved when it moved here; [`ORIGIN.md`](ORIGIN.md) records the
exact source commit, subtree hash, and split.

## Where the project stands

The strict weighted estimate is **10.2% integrated**. Approximately **12% is
ecosystem-ready** when compatible work already available in Mathlib, Lean
Pool, Tau Ceti, FLT, and related repositories is counted as reusable rather
than as completed here. Those are deliberately different numbers:
publishing a statement, finding prior art, or drafting an interface earns no
theorem-completion credit.

The integrated development contains 696 checked Lean sources and 1,446,855
lines. It closes the group-theoretic cardinality endpoint and many
finite torsion orders, including `14`, `15`, `16`, `20`, `21`, `24`, and
`27`; it also completes the exact-pin migration, Tau Ceti's finite-support
order system and abelian-variety product-dimension theorem, and the ten-point
enumeration for every elliptic curve over `F₅`. The current frontier is:

- the genus-two closures for orders `13` and `18` and the explicit order-25
  endpoint;
- order `35` through the shared squarefree formal-immersion engine at `11`,
  and order `49` through the direct cyclic-subgroup map to `X₀(49)`;
- the uniform prime-order theorem via Mazur's degree-one formal immersion at
  `5`, whose main path requires substantial modular-curve, Jacobian,
  Néron-model, Hecke, and focused finite-flat infrastructure; and
- the X₁(11) five-coset and cyclotomic reciprocity Challenges, which remain
  mandatory release obligations but are not premises of the prime theorem.

The shared formal-immersion lane now has a checked canonical map on stalk
cotangent spaces, its surjectivity criterion, a surjective-stalk consumer,
the canonical residue-field-semilinear map, and a residue-honest degree-one
certificate that the future q-expansion proof must fill. This is deliberately
not node completion: the completed-local-ring criterion, integral cusp
geometry, modular quotient, and cusp-collision theorem remain open.

The order-35 lane also now checks the opposite rational point-function
candidate and the composite identity `dual (candidate P) = 3 • P`, together
with the rational three-cover and visible-coset translations. The reduced
numerator/denominator calculation now proves that every nonexceptional source
ordinate has cube class `1`, `7`, or `49`. Target-curve finiteness (or the
more direct candidate-surjectivity input used here) remains open before the
conditional rank-zero chain becomes unconditional, so this still earns no
node credit.

The percentage and task graph come from
[`coordination/program.json`](coordination/program.json), not prose or line
counts. See the [live roadmap](https://mazur-theorem-formalization.vilin402100.chatgpt.site/), the
[progress methodology](docs/PROGRESS_METHOD.md), and the
[implementation inventory](docs/IMPLEMENTATION_STATUS.md).

## Can this be crowdsourced?

Yes—but not as one flat list of unrelated bounties.

At the current checkpoint, **14.9% of the total weighted work** is exposed
through exact, compiled contracts: **3.7%** as ordinary claimable tasks and
**11.2%** as
research-open problems where parallel approaches are welcome. With reviewed
interfaces and upstream coordination, roughly **35–45%** can be parallelized
into bounded work packages. The remaining **45–55%** is high-dependency
research and integration work that needs small, stable teams rather than
drive-by proof submissions.

That is more optimistic than “most of it cannot be crowdsourced,” but only
under a disciplined meaning of crowdsourcing: exact compiler-checked
contracts, dependency ownership, short claims, upstream-first development,
and maintainers responsible for integration. The roadmap marks which tasks
are claimable now and which are still research or interface design.

## Start contributing

1. Read [`CONTRIBUTING.md`](CONTRIBUTING.md) and
   [`docs/CLAIMING.md`](docs/CLAIMING.md).
2. Choose an ordinary **open** card or a nonexclusive **research-open** card
   on the
   [roadmap](https://mazur-theorem-formalization.vilin402100.chatgpt.site/#challenges).
3. Use the card's pre-filled form. Ordinary claims last 14 days and need a
   weekly heartbeat; research intentions do not reserve the problem.
4. Prove the exact declaration, compile its named consumer, and open a PR
   using the supplied checklist.

Research-level tasks may have more than one active team. Interface work is
reviewed before proof volume is accumulated behind it.

## Build

The package is pinned to Lean `v4.33.0-rc1` and the matching Mathlib release.
It needs about 8 GB of local cache. Fetch Mathlib's compiled cache first:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build MazurTorsion
```

For a contribution, build the smallest affected module:

```sh
LEAN_NUM_THREADS=1 lake build MazurTorsion.Path.To.Module
python3 scripts/quality.py
```

Full cold builds, documentation, and exposition extraction run in GitHub
Actions so contributors do not need a large workstation.

The mathematical dependency graph is built with the official
[`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint)
package:

```sh
cd blueprint
LEAN_NUM_THREADS=1 lake exe vbp build
LEAN_NUM_THREADS=1 lake exe vbp check
```

The interactive output is written to `blueprint/_out/site/html-multi` and
published at the stable `/blueprint/` route on GitHub Pages.

## Project map

- [`MazurTorsion/`](MazurTorsion/) — checked theorem development;
- [`EllipticCurves/`](EllipticCurves/) — attributed exact-pin reduction
  infrastructure;
- [`MazurTorsion/Upstream/`](MazurTorsion/Upstream/) — attributed AINTLIB
  geometry foundations and the checked Tau Ceti integration boundary;
- [`Challenge/`](Challenge/) — immutable open theorem contracts;
- [`coordination/program.json`](coordination/program.json) — canonical
  weighted DAG and claim metadata;
- [`docs/ROUTE_AUDIT.md`](docs/ROUTE_AUDIT.md) — audited selection of the
  Mazur-1978 formal-immersion route, rejected alternatives, and fallback
  policy;
- [`blueprint/MazurBlueprint/Blueprint.lean`](blueprint/MazurBlueprint/Blueprint.lean)
  — six-stage Verso blueprint, dependency graph, and progress summary;
- [`upstream/tauceti/`](upstream/tauceti/) — open Tau Ceti interface
  challenges, resolved separately at the same exact pins as the core;
- [`docs/`](docs/) — methodology, prior-art audit, and technical narrative;
- [`archive/drafts/`](archive/drafts/) — explicitly unverified historical
  scratch files, excluded from all proof and progress claims.

## Verification policy

Merged proof code must be placeholder-free, warning-free, and free of custom
axioms, `unsafe`, and `partial`. The only permitted foundational axioms in
audited declarations are `propext`, `Quot.sound`, and `Classical.choice`.
Open statements are allowed only in registered `Challenge/` files, with
exactly one whole-body `:= sorry`.

The Apache-2.0 license and third-party attribution are in
[`LICENSE`](LICENSE), [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md),
[`PORTING.md`](PORTING.md), and [`docs/PRIOR_ART.md`](docs/PRIOR_ART.md).
