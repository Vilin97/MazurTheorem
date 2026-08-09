# Third-party notices

## EllipticCurves

- Author and upstream maintainer: Michael Stoll
- Source: https://github.com/MichaelStollBayreuth/EllipticCurves
- Source commit: `3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`
- License: Apache License 2.0; see `LICENSE`

The retained modules have been modified for Lean `4.33.0-rc1` and mathlib
`79d0395a1825a6264ad5d269e35e60537518955e`. The modifications and exact
production-file manifest are recorded in `PORTING.md`.
The exact-pin X18 descent slices are:

- `EllipticCurves/X18WeakMordellWeil.lean`, selected from upstream
  `EllipticCurves/WeakMordellWeil.lean` through Step 6;
- `EllipticCurves/X18SelmerLocal.lean`, selected from the local finite-place
  portion of upstream `EllipticCurves/SelmerGroup.lean`.

`MazurTorsion/EllipticCurve/NonsingularReduction.lean` and
`MazurTorsion/EllipticCurve/NonsingularReductionAdditive.lean` are downstream
singular-fibre adaptations of the pinned good-reduction construction and
retain Michael Stoll's author credit.

## Variable-change implementation and local singular-cubic extension

- Copyright holders recorded in source: Kevin Buzzard; Vasily Ilin for the local extension
- Authors recorded in source: Michael Stoll, Claude, and Vasily Ilin
- Files:
  - `MazurTorsion/EllipticCurve/VariableChange.lean`
  - `EllipticCurves/VariableChange.lean`
- License: Apache License 2.0; see `LICENSE`

The original copyright, license, and author credit remain in the retained implementation.
Its header additionally records Vasily Ilin's derivative-transport and singular-cubic
nonsingular-locus generalization. The compatibility file avoids duplicating the declarations.

## Lean Pool torsion foundations

- Author: Victor Aguiar
- Source:
  https://github.com/vaguiarl/lean-pool/tree/vaguiarl/mazur-foundations/LeanPool/MazurTorsionFoundations
- Source commit: `60bec1602de9e747b67ad69641bcfb4265849123`
- License: Apache License 2.0; see `LICENSE`

The retained `TwoTorsion.lean`, `ThreeTorsion.lean`, and
`FullFourTorsion.lean` files preserve their source headers. The exact-pin
audit and local changes are recorded in `docs/PRIOR_ART.md`.

## Lean Pool Grothendieck vanishing

- Authors and copyright holders recorded in source: Vasily Ilin and Brian Nugent
- Source: https://github.com/Vilin97/lean-pool/tree/4eef1ffb3b643d606665e3b5585aa69454e137d1/LeanPool/GrothendieckVanishing
- Source commit: `4eef1ffb3b643d606665e3b5585aa69454e137d1`
- Upstream Lean 4.33 migration reference: `cc54a3adb51cb00b78cbe025818a24b676aeada7`
- Migration co-authors recorded upstream: `github-actions[bot]`, Vasily Ilin,
  and Claude Opus 5
- License: Apache License 2.0; see `LICENSE`

The 15 retained modules are stored under
`MazurTorsion/Upstream/LeanPool/GrothendieckVanishing/` with their original
headers. They prove Grothendieck vanishing for abelian sheaves on Noetherian
topological spaces. The local exact-pin adaptations and the named smooth
proper curve consumer are recorded in `PORTING.md` and `docs/PRIOR_ART.md`.

## AINTLIB geometry foundations

- Upstream author identified from repository authorship/history: Chris Birkbeck
- Source: https://github.com/CBirkbeck/AINTLIB
- Source commit: `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`
- Source paths:
  - `projects/ModularCurves/ModularCurves/ForMathlib/CartierDual.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafOfModulesMonoidal.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleSheaf.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCohomologyExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FormalCoproductAdditive.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechBasic.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCech.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechFlat.lean`
    (two core declarations only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCech.lean`
    (the core before the flatness tail only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechComparison.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechHOne.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechHOneFinite.lean`
  - `projects/ModularCurves/ModularCurves/Picard/Pic.lean`
- License evidence: the audited source commit has no root `LICENSE`. Selected
  files retain their per-file Apache-2.0 notices where present. Exact
  repository-level evidence is AINTLIB `origin/main` commit
  `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, whose root `LICENSE` is
  Apache License 2.0. The source and license-evidence commits are divergent;
  neither is an ancestor of the other. The three headerless selected sources
  are byte-identical at both commits: `SchemeModuleSheaf.lean` blob
  `b735f77f920d236c5416f43201aefd9804cea4b6`,
  `SheafCohomologyExact.lean` blob
  `5e8e401a5556eef7940273fd1443b84c236fabbb`, and
  `SchemeModuleBaseCech.lean` blob
  `d62a2d04dab99e404c934d5f25e28738b5539175`. Their local headers record
  Chris Birkbeck's authorship/history on those exact licensed blobs rather
  than claiming that the dev source supplied headers or a root license.

The selected source and slices are stored under
`MazurTorsion/Upstream/AINTLIB/`. The two
sheaf-cohomology files preserve the upstream declarations and proofs, with
only attribution, documentation, and formatting changes. The other files
have the import and exact-pin compatibility adjustments recorded in
`PORTING.md`; source-level option commands and linter findings were removed.
The base-Cech slice excludes the unused affine-comparison dependency and
splits the ordered core before the flat/Picard tail. No other AINTLIB
geometry source is included. Details are recorded in `PORTING.md` and
`docs/PRIOR_ART.md`.

## AINTLIB Hilbert 92 and Hilbert 94 foundations

- Upstream author identified from repository authorship/history: Chris Birkbeck
- Source: https://github.com/CBirkbeck/AINTLIB
- Source commit: `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`
- Source paths:
  - `projects/FltRegular/FltRegular/NumberTheory/CyclotomicRing.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/SystemOfUnits.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/Hilbert92.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/Unramified.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/RegularPrimes.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/Hilbert94.lean`
- License: Apache License 2.0 under the upstream repository-wide license; see
  `LICENSE`. The local selected files carry added attribution headers.

The selected files are stored under
`MazurTorsion/Upstream/AINTLIB/FltRegular/NumberTheory/`; only the
class-group power lemma is retained from `RegularPrimes.lean`. Imports and
proof details were adapted to the immutable Mathlib pin, including an
option-free universe-shrinking bridge for Hilbert 90. Details are recorded in
`PORTING.md` and `docs/PRIOR_ART.md`.

## Tau Ceti

- Upstream source: https://github.com/TauCetiProject/TauCeti
- Reviewed integration source: https://github.com/Vilin97/TauCeti
- Exact dependency commit: `a74dfee78f800df63f085a19006f7d502eee365e`
- Upstream base commit: `a3913fd9111b851af857f720b4ce6721e6634183`
- License: Apache License 2.0

Tau Ceti is an exact Git dependency, not vendored source. The root package and
the separate upstream-contract package deliberately resolve the same Tau Ceti,
Lean, and Mathlib revisions. The exact feature commit adds the finite-support
theorem for scheme-theoretic orders and its `OrderSystem` consumer, together
with faithful-integral, tensor-product, scheme-product, and abelian-variety
product-dimension theorems. It also constructs the rational-function map to
the projective line and proves the residue-degree product formula for smooth
proper integral curves, with a checked Picard-zero quotient consumer. Its
commits retain Tau Ceti's repository-wide license and contributor attribution.

## Mathlib Dedekind-zeta finite-fibre argument

- Author and copyright holder: Xavier Roblot
- Source: `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- Source commit: `79d0395a1825a6264ad5d269e35e60537518955e`
- License: Apache License 2.0

`MazurTorsion/NumberTheory/WeakChebotarev.lean` adapts the short
finite-fibre counting rewrite from Mathlib's proof of the Dedekind-zeta
class-number formula. The local file retains Xavier Roblot's copyright and
authorship; the surrounding ideal-pair injection and pole argument are new.

## AI-assisted development

Parts of the proof development were produced in Claude Code and Codex agent
sessions, then reviewed, compiled, and committed under Vasily Ilin's
direction. Files that record `Claude` in their authorship header retain that
credit. AI generation is provenance, not verification: every completion
claim is based on compiled Lean and the repository's axiom/source gates.
