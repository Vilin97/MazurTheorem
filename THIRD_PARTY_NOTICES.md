# Third-party notices

## EllipticCurves

- Author and upstream maintainer: Michael Stoll
- Source: https://github.com/MichaelStollBayreuth/EllipticCurves
- Source commit: `3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`
- License: Apache License 2.0; see `LICENSE`

The retained modules have been modified for Lean `4.33.0-rc1` and mathlib
`79d0395a1825a6264ad5d269e35e60537518955e`. The modifications and exact
production-file manifest are recorded in `PORTING.md`.
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

- Upstream authorship retained from the selected file headers: Chris
  Birkbeck and the AINTLIB ModularCurves contributors
- Source: https://github.com/CBirkbeck/AINTLIB
- Source commit: `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`
- Canonical-support audit commit:
  `6b879658fe916b5db2afcddebbed35a9dc10aa61`
- Historical direct low-degree audit commit:
  `d78d10a74577e28840d21eb4e07395d87c44370f`
- Source paths:
  - `projects/ModularCurves/ModularCurves/ForMathlib/CartierDual.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafOfModulesMonoidal.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleSheaf.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCohomologyExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FormalCoproductAdditive.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FiniteHomologySequence.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/BaseChangeKerCoker.lean`
    (`Module.Finite.of_exact_of_finite` only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechBasic.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCech.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechFlat.lean`
    (two core declarations only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCech.lean`
    (the core before the flatness tail only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechFunctor.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechLowDegreeFinite.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechComparison.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechHOne.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechHOneFinite.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechCochains.lean`
    (generic cochain slice only; affine-vanishing tail omitted)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechDifferential.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TopCatSheafRestrict.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafTerms.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafDifferential.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafComplex.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafAugmentation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafZeroExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafLocalContraction.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafPositiveExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafResolution.lean`
    (augmentation-mono slice only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/FlasqueCohomology.lean`
    (notation and two consumed instances only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechFlasqueHOne.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechInjectiveBicomplex.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNat.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatLowDegrees.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatHorizontalEdge.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatHorizontalEdgeHOne.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatVerticalEdge.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechInjectiveAugmentation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCechInjectiveComparison.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/AcyclicAffineCechComparison.lean`
    (degree-one comparison only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechHomology.lean`
    (homology isomorphisms only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleSupport.lean`
    (split between the closed-stalk rank core and the remaining support API)
  - `projects/ModularCurves/ModularCurves/ForMathlib/FinitePresentationOfFinite.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/BaseChangeAlongCompat.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/InvariantBaseChange.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/InvariantLocalization.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SpecGroupAction.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/PullbackLocalAtTarget.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/InvariantTorsor.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/EtaleCancellation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/AffineQuotient.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeQuotient.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeActionFree.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TorsorMap.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/QuotientTorsor.lean`
  - `projects/ModularCurves/ModularCurves/Picard/Pic.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/PullbackTensorGeneral.lean`
  - `projects/ModularCurves/ModularCurves/Picard/InvertibleSheaf.lean`
    (`sheafifyValIso` only)
  - `projects/ModularCurves/ModularCurves/EllipticCurve/PoleSheaf.lean`
    (generic tensor-section kernel only)
  - `projects/ModularCurves/ModularCurves/EllipticCurve/PullbackTensorSection.lean`
    (canonical pullback evaluator only)
  - `projects/ModularCurves/ModularCurves/Picard/RelativePic.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SpecBasicOpenAway.lean`
    (`specBasicOpen` only)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleRestrictLimits.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleRestrictPushforward.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafModuleFiniteTypeQuotient.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleComparisonCoherent.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleSupportDrop.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleComparisonSupport.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FiniteModuleSupportAnnihilation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FiniteFamilySupportAnnihilation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FiniteAffineSupportAnnihilation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/IdealSheafPowerSubscheme.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOpenCoverIso.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/AdjunctionUnitIsoTransport.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SurjectiveRestrictionScalars.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/AffineModuleBaseChange.lean`
    (affine-tilde unit slice)
  - `projects/ModularCurves/ModularCurves/ForMathlib/AffineIdealQuotientPullbackUnit.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModulePullbackUnitComposition.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/IdealSheafAffineChartPullbackUnit.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/IdealSheafSubschemeAffineChart.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/IdealSheafSubschemeRestrictPullbackUnit.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FiniteSupportIdealSheafPullbackUnit.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOpenUnitIso.lean`
  - `projects/ModularCurves/ModularCurves/Picard/DualPullback/OpenAdjunction.lean`
    (private explicit-square/mate slice in the preceding local module)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleCanonicalSupportThickening.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleCanonicalSupportFull.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeInducingOpenLift.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModulePushforwardMapRestrictionIso.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleRestrictionIsoMonotone.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechPushforward.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechPushforward.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechHomologyRetract.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModulePushforwardPullbackSupport.lean`
    (support-only slice)
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleOrderedBaseCechPushforwardFinite.lean`
    (degree-zero/degree-one specialization)
- License evidence: the audited source commit has no root `LICENSE`. Selected
  files retain their per-file Apache-2.0 notices where present. Exact
  repository-level evidence is AINTLIB `origin/main` commit
  `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, whose root `LICENSE` is
  Apache License 2.0. The source and license-evidence commits are divergent;
  neither is an ancestor of the other. Every headerless selected source is
  byte-identical at both commits; `PORTING.md` records every exact Git blob.
  Their local headers record Chris Birkbeck's authorship/history on those
  exact licensed blobs rather than claiming that the dev source supplied
  headers or a root license.
- Additional adapted proof source, not vendored as a module:
  - `projects/ModularCurves/ModularCurves/GroupScheme/TranslationBySection.lean`
    (blob `6223d2904bc6f2162d4ee4e77ed684a40396ef18`; Chris Birkbeck and
    Claude Opus 4.8)
- The adapted `TranslationBySection` blob had no header at the audited commit,
  but is byte-identical at AINTLIB commit
  `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, under root Apache-2.0 license
  blob `8dada3edaf50dbc082c9a125058f25def75e625a`. See `docs/PRIOR_ART.md`.

The selected source and slices are stored under
`MazurTorsion/Upstream/AINTLIB/`. The exact-sequence sheaf-cohomology files
preserve the upstream declarations and proofs, with only attribution,
documentation, and formatting changes. The other files have the import,
API-narrowing, and exact-pin compatibility adjustments recorded in
`PORTING.md`; source-level option commands and linter findings were removed.
The retained Cech lane excludes the unused flat/Picard and properness cones,
replaces the option-dependent flasque-cohomology proof with existing checked
project theorems, drops three unconsumed intermediate modules and the unused
packaged acyclic-resolution tail, and keeps only the degree-one affine and
base-homology comparisons. The separate canonical-support extension stops at
the canonical thickening/full-support model and strict support-drop API; it
does not retain or claim the Chow/projective producer or properness endpoint.
The finite-pushforward comparison extension retains the inverse-image-cover
complex isomorphisms, their low-degree finiteness transport, and the
support-only pushforward/pullback result; it omits the all-degree and
tensor/invertible tails.

The thirteen finite-action quotient files retain the upstream statements and
namespaces. Besides internal import repointing, formatting, and removal of
source-level compatibility options and linter suppressions forbidden by this
repository, `SpecGroupAction` has explicit coercion and primality witnesses
and `BaseChangeAlongCompat` uses the pinned Mathlib finite-affine and
fpqc-to-fppf proof APIs explicitly. `SchemeQuotient` uses current affine-open
naturality and diagonal-composition APIs. `QuotientTorsor` makes the affine
action invariance and pullback representatives explicit. No statement is
weakened. The additional translation proof adaptation and its exact-blob
license evidence are described above. Details are recorded in `PORTING.md`
and `docs/PRIOR_ART.md`.

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

## AINTLIB power-residue character adaptation

- Upstream author retained in the local file header: Chris Birkbeck
- Source: https://github.com/CBirkbeck/AINTLIB
- Source commit: `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`
- Source paths and exact Git blob identifiers:
  - `projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Basic.lean`
    (`7b5f3eb9e9fc05c78f08343b2e7e5bd26f7b0f36`)
  - `projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/Character.lean`
    (`3b0a7103f366944dec6ce6dd10e5fc9438c02a09`)
- Local derivative:
  `MazurTorsion/NumberTheory/CyclotomicJacobiCharacter.lean`
- License: Apache License 2.0 under the upstream repository-wide license; see
  `LICENSE`.

The local file selectively adapts the finite-field power-residue exponent
and its multiplicative-character packaging to the immutable Mazur pin, then
adds the cyclotomic specialization, Galois covariance, exact-order proof, and
the finite-field binomial-sum consumer. Its header credits both Vasily Ilin
and Chris Birkbeck. The later Jacobi-sum and ideal-factorization modules are
new project consumers of this attributed bridge.

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

`MazurTorsion/Upstream/ProjectiveLineCechHOneFinite.lean` repeats and adapts
the private standard-chart coordinate computations from
`TauCeti/AlgebraicGeometry/ProjectiveLine/Basic.lean` at the exact dependency
commit above. Those declarations are private upstream, so the local checked
cohomology consumer cannot import them by name. The local file retains this
source attribution in its header documentation. Its principal-parts
calculation, exact Cech differential, and assembly with the separately
attributed finite-pushforward and sheaf-cohomology infrastructure are new
project work.

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
