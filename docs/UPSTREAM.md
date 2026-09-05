# Upstream and dependency strategy

Mazur's theorem sits across several formalization ecosystems. This repository
uses them as upstreams, not as untracked code mines.

## Core pin

The checked `MazurTorsion` package uses Lean `v4.33.0-rc1`, Mathlib commit
`79d0395a1825a6264ad5d269e35e60537518955e`, and Tau Ceti commit
`a74dfee78f800df63f085a19006f7d502eee365e`, based on upstream commit
`a3913fd9111b851af857f720b4ce6721e6634183`. These match the current Lean Pool
challenge and the separate Tau Ceti contract workspace. The full resolved
package-revision graph, not only the headline pins, is checked for equality.

## Mathlib

General-purpose results belong in Mathlib when their API and scope fit.
Downstream adapters should be thin and pinned. No local theorem is counted
complete merely because a similar theorem exists on a newer Mathlib revision.

## Lean Pool

Lean Pool provides the immutable target, comparator model, quality policy, and
many reusable completed projects. A final solution must be replayable against
the target statement without importing its open challenge.

## Tau Ceti

Tau Ceti is the preferred upstream for large algebraic-geometry interfaces
such as divisors, Picard functors, abelian varieties, and the Jacobian
roadmap. The root package now has a direct immutable Tau Ceti dependency, and
`MazurTorsion.Upstream.Geometry` compiles its line-bundle and Abel--Jacobi
layers beside the selected AINTLIB foundations. Upstream-facing open contracts
and their solved lifecycle bridges live in
[`upstream/tauceti/`](../upstream/tauceti/) as a separately resolved Lake
package, pinned to the same Tau Ceti, Lean, and Mathlib commits. The current
pin contains the finite-support/order-system result, the checked
abelian-variety product-dimension chain, and the smooth-proper-curve product
formula with divisor-quotient and scheme-Picard consumers. The quality gate
rejects any drift between those pins.

## AINTLIB

AINTLIB is used selectively, not as a Lake dependency. The audited
`dev/modular-curves` snapshot has a different Mathlib graph, many placeholders,
source-level option commands, and no root license at that revision. The local
tree therefore contains selected, reviewed ports rather than a checkout of the
upstream package.

At this revision there are 101 modules below
`MazurTorsion/Upstream/AINTLIB/`, in two independently audited cones:

- 95 modular-curve geometry modules from commit
  `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`: 91 under `ForMathlib/` and
  four under `Picard/`;
- six Hilbert 92/94 number-theory modules under `FltRegular/NumberTheory/`,
  selected from commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.

These totals count local Lean modules, not byte-for-byte vendored files. Some
are whole-file ports and some are documented narrow, option-free adaptations.
Their placement records source lineage; it does not imply automated
generation or transfer authorship to the project. [`PORTING.md`](../PORTING.md)
and [`THIRD_PARTY_NOTICES.md`](../THIRD_PARTY_NOTICES.md) are authoritative for
the source blob, retained authors, license evidence, local changes, and named
consumer of each cone.

`MazurTorsion.Upstream.Geometry` is the broad geometry boundary. The coherent
cohomology lane exposes smaller boundaries such as
`SchemeModuleCohomologyHZero`, `SchemeModuleBaseCechHOneComparison`, and
`ProperCurveCohomologyFinite`. `SchemeModuleBaseChangeCech` assembles the
canonical Cartesian pullback map over a finite affine cover, identifies the
scalar-extended complex and its homology, and exposes genuine `H⁰`/`H¹`
field-extension base change. `SchemeModuleProperBaseChange` applies it to the
finite subcover of the canonical affine cover, giving proper schemes and the
smooth proper integral-curve consumer a cover-independent API. The proper degree-zero and finite-free ordered
low-degree target boundaries are `ProperHZeroFinite` and
`ProperCurveCechLowDegreeFinite`; supplied open-local comparison data is
assembled by `SchemeModuleOrderedBaseCechLowDegreeSupport`, while
`SchemeModulePullbackCoherent` proves the canonical model coherent and
`ProperCurveFiniteSupport` uses its finite pushforward to make strict-support
global sections finite. `ProperCurveFiniteSupportCech` exposes the resulting
canonical `H⁰` and pointed ordered base-Cech `H⁰`/`H¹` finiteness, then uses
identity comodels to reduce the arbitrary coherent endpoint to full-support
comparison data. It also consumes the field-linear long exact sequence to
reduce canonical `H⁰` directly to a coherent map from an `H⁰`-finite source
with strict-support cokernel; `SchemeModuleComparisonSupportEpi` obtains that
strictness from an epimorphism on a nonempty open when the source has full
support, and conversely infers source full support from an open-local
epimorphism to a full-support target on an integral scheme. `ProperHZeroFinite`
proves that a monomorphism from this source into a finite free sheaf supplies
its canonical `H⁰` finiteness. `SchemeModuleAffineOpenPresentation` constructs
the required coherent source from finite generators on an affine open by a
restriction--pushforward transpose and pullback: it is monic toward a finite
free sheaf and epic toward the target after restriction. The resulting
kernel/image exact-sequence argument in `ProperCurveFiniteSupportCech`, followed
by the strict/full-support split at an affine neighborhood of the generic
point, proves canonical `H⁰` finite-dimensional for every coherent module on
the pointed proper curve. A unified facade combining those finiteness and
higher-vanishing results with the now cover-independent exact low-degree
comparison remains outside this boundary; general proper-flat base change and
semicontinuity remain downstream. The
Hilbert-94 cone is consumed through
`MazurTorsion.NumberTheory.CyclotomicHilbert94`. `MazurTorsion.lean` is their
aggregate audit consumer, not the recommended import for an individual
development. See the [Upstream directory map](../MazurTorsion/Upstream/README.md)
for the entry modules.

The retained relative Picard presheaf and coherent-cohomology infrastructure
do not supply a represented degree-zero Picard scheme or Jacobian. Likewise,
the retained finite-group-scheme substrate does not supply the represented
integral modular curve required by the theorem. Those frontiers remain open
until their complete cones satisfy the repository's proof, option, license,
exact-pin, and downstream-consumer requirements. This keeps reusable checked
content without importing AINTLIB's unresolved dependency graph.

## FLT repositories

The Imperial FLT and related repositories contain relevant interfaces and
experimental proof cones. A declaration stated as an axiom or depending on
unfinished work is design prior art, not a proof dependency. Any port must
retain its license, author headers, exact source commit, and a declaration
audit.

## Poincaré Conjecture project

The
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
repository was refreshed at commit
[`68475da55dca31369fe2b274b3e554d4f18aaec1`](https://github.com/frenzymath/Poincare-Conjecture/commit/68475da55dca31369fe2b274b3e554d4f18aaec1).
It separates a primary dependency-driven proof, source-faithful book and
article formalizations, shared infrastructure, and a public site that
distinguishes verified declarations from work in progress.

That is the right coordination pattern for a theorem whose prerequisites are
larger than its final statement. This repository adopts the dependency-first
blueprint, visible verification status, and source-project separation. It adds
an exact weighted ledger and compiler-checked claim contracts because Mazur's
current frontier spans separately resolved dependency graphs and several
unbuilt interfaces. The visual roadmap is coordination evidence, not proof
evidence.

## Dependency updates

Each dependency is pinned to an immutable commit in the roadmap. Updates must
be isolated PRs that:

- explain why the update is needed;
- rebuild affected consumers;
- report API changes and axiom results;
- update provenance and generated artifacts;
- do not change roadmap weights.
