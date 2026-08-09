# Exact-pin ports

## Elliptic-curve reduction

## Provenance and license

The 29 retained implementation files identified as “upstream” below are derived from Michael Stoll’s
[`EllipticCurves`](https://github.com/MichaelStollBayreuth/EllipticCurves) repository at the
immutable commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

That work is licensed under Apache License 2.0. The unmodified upstream `LICENSE` is retained at
the package root and must accompany any distribution of the port. The historical
`EllipticCurves.VariableChange` module is a compatibility import of the pre-existing port
of the same pinned upstream file, avoiding duplicate declarations in the shared namespace. No
source from another elliptic-curve repository is included in this port. The exceptional-cubic
harness `EllipticCurves/Examples/ExceptionalCubicReduction.lean` is a new, separable integration
test.

The compatibility target is exactly:

- Lean `4.33.0-rc1`;
- mathlib tag `v4.33.0-rc1`, resolved by the manifest to
  `79d0395a1825a6264ad5d269e35e60537518955e`.

## Source-to-destination manifest

In this standalone repository, upstream modules retain their module names and
live under `EllipticCurves/`. “Modified” means changed only for the exact-pin
port as described in the next section. Older paths in the manifest retain the
historical `mazur-torsion/` prefix to document where the original port lived;
remove that prefix to obtain the current repository path.

| Upstream source at the pinned commit | Historical port destination | State |
|---|---|---|
| `EllipticCurves/IntegralModel.lean` | `mazur-torsion/EllipticCurves/IntegralModel.lean` | modified |
| `EllipticCurves/Mathlib/AdicCompletionExtension.lean` | `mazur-torsion/EllipticCurves/Mathlib/AdicCompletionExtension.lean` | modified |
| `EllipticCurves/Mathlib/AdicFormalGroupLog.lean` | `mazur-torsion/EllipticCurves/Mathlib/AdicFormalGroupLog.lean` | unchanged |
| `EllipticCurves/Mathlib/AdicValuation.lean` | `mazur-torsion/EllipticCurves/Mathlib/AdicValuation.lean` | unchanged |
| `EllipticCurves/Mathlib/Basic.lean` | `mazur-torsion/EllipticCurves/Mathlib/Basic.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/AdicTopology.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/AdicTopology.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/ExpConverge.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/ExpConverge.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Basic.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Basic.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Invariance.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Invariance.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Log.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Log.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Points.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Points.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/LocalRing.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/LocalRing.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/LogIso.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/LogIso.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/MvPSeries.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/MvPSeries.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/MvPowerSeriesComp.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/MvPowerSeriesComp.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/MvPowerSeriesPDeriv.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/MvPowerSeriesPDeriv.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/PSeries.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/PSeries.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/PadicInt.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/PadicInt.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/PadicValNat.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/PadicValNat.lean` | unchanged |
| `EllipticCurves/Mathlib/EllipticCurvePoint.lean` | `mazur-torsion/EllipticCurves/Mathlib/EllipticCurvePoint.lean` | modified |
| `EllipticCurves/ReductionAtPrime.lean` | `mazur-torsion/EllipticCurves/ReductionAtPrime.lean` | modified |
| `EllipticCurves/VariableChange.lean` | `mazur-torsion/EllipticCurves/VariableChange.lean` | compatibility import |
| `EllipticCurves/WeierstrassFormalGroup/Chord.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Chord.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/Eval.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Eval.lean` | unchanged |
| `EllipticCurves/WeierstrassFormalGroup/Filtration.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Filtration.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/Foundations.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Foundations.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/Reduction.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Reduction.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` | unchanged |
| new `EllipticCurves/Examples/ExceptionalCubicReduction.lean` | `mazur-torsion/EllipticCurves/Examples/ExceptionalCubicReduction.lean` | new harness |

The new harness is deliberately self-contained. The project-level bridge
`MazurTorsion/NumberTheory/ExceptionalCubicReduction.lean`, outside this 31-file cone, identifies
its model with `MazurTorsion.ExceptionalCubic.curve.toAffine` and supplies
`MazurTorsion.ExceptionalCubic.point_finite` to its final cardinality theorem.

`MazurTorsion/EllipticCurve/NonsingularReduction.lean` is new downstream
project code rather than a retained port. Its pointwise reduction, exact-kernel,
and negation proofs explicitly adapt Michael Stoll's pinned
`EllipticCurves/WeierstrassFormalGroup/Reduction.lean` construction from good
reduction to the nonsingular locus of a singular special fibre. The new file
retains Stoll's author credit and records the changed hypothesis boundary in
its module documentation.

`MazurTorsion/EllipticCurve/NonsingularReductionAdditive.lean` completes that
singular-fibre adaptation. Its congruence criterion and slope calculations
adapt the pinned proof of additivity, replacing global smoothness of the
reduced cubic by the explicit nonsingularity carried by the canonical domain.
It proves `sub_mem_filtration_of_nonsingularReduction_eq`,
`nonsingularReduction_add_of_mem_filtration_left`, and
`nonsingularReduction_isAdditive`, and retains Stoll's author credit. The
five- and eleven-adic constructors in that file are new downstream consumers.

## Exact-pin modifications

- `Mathlib/AdicCompletionExtension.lean`: retained lines 1–384 of the upstream mathematical
  source (369 lines after updating the now-accurate module documentation); removed the unused
  completion-extension tail, which belongs to the Selmer cone rather than reduction.
- `IntegralModel.lean:94–106`: used `change` for five intended goal conversions, as required by
  the exact-pin standard style linter.
- `Mathlib/Basic.lean`: selected the current `ramificationIdx'` API, made the
  valuation-quotient rewrite transparent with `erw`, and transported integral-basis
  coordinates through an explicit ring-of-integers element; the earlier `omit`-binder and
  goal-conversion cleanups remain in place.
- `Mathlib/Chabauty/FormalGroupLaw/Invariance.lean:65–86`: supplied the missing
  zero-family substitution identity from coefficient extensionality.
- `Mathlib/Chabauty/LogIso.lean:72–523`: replaced linter-option wrappers with explicit
  `omit` binders; weakened two proof-only `Fintype` assumptions to `Finite` and constructed
  `Fintype.ofFinite` locally; made proof-local decidable equality classical; removed a simp
  lemma that became redundant at 4.33.
- `Mathlib/Chabauty/MvPSeries.lean:239`: used the 4.33 namespace
  `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd`.
- `Mathlib/Chabauty/MvPowerSeriesPDeriv.lean:114–140`: proved the coefficient formula for
  multivariate polynomial partial derivatives, absent at this pin.
- `Mathlib/EllipticCurvePoint.lean:51–108`: moved the narrow curve-equality and field
  base-change point-map API out of the unrelated Selmer module and exposed an explicit
  nonsingularity transport to the canonical base-changed affine curve.
- `ReductionAtPrime.lean:10–11,246–297,395–458`: replaced the transitive Selmer import with the
  narrow point helper; split one expensive residue-compatibility proof into three lemmas so it
  elaborates within default heartbeat limits; removed two proof-only residue-field
  `DecidableEq` assumptions.
- `VariableChange.lean`: replaced the duplicate implementation with a public compatibility
  import of `MazurTorsion.EllipticCurve.VariableChange`, the pinned Stoll port exporting the
  required `Point.equivVariableChange` API. The retained implementation now also contains a
  locally authored derivative-transport proof and nonsingular-locus equivalence for singular
  Weierstrass cubics; its header and third-party notice record that extension separately.
- `WeierstrassFormalGroup/Chord.lean:590–638`: supplied the missing zero-family substitution
  lemma.
- `WeierstrassFormalGroup/Foundations.lean`: made quotient-map arguments and subtype
  coercions explicit, avoiding a default typeclass-search timeout; named a proof-local formal
  point so 4.33 can see the parameter equality without relying on reducibility.
- `WeierstrassFormalGroup/GroupLaw.lean:53–54,412–742`: removed the recursion-depth wrapper;
  the proof builds at default limits after using the compatibility substitution lemma.
- `WeierstrassFormalGroup/Filtration.lean`: used `change` for an intended goal conversion,
  made a proof-only field `DecidableEq` classical, and named a formal point plus its parameter
  equality for the stricter 4.33 elaborator.
- `WeierstrassFormalGroup/Reduction.lean`: applied the exact-pin notation whitespace, removed
  two proof-only residue-field `DecidableEq` assumptions, and now transports valuation bounds
  explicitly through `mem_adicCompletionIntegers` where 4.33 no longer unfolds the subtype
  membership automatically.
- `Examples/ExceptionalCubicReduction.lean`: rewrote the integer-quotient algebra equivalence
  proof using `Int.quotientSpanNatEquivZMod_comp_Quotient_mk`, the supported 4.33 API.

The 4.33 migration also touched downstream project files outside the 31-file reduction cone:
`Foundations/NaiveHeightDescent.lean` now reuses Mathlib's upstream `Point.sym2x` API and supplies
the new `Filter.TendstoCofinite` instance expected by `Northcott.comp_of_finite_fibers`; the five
`XOne*Reduction`/`XZero*Reduction` modules with integer-quotient maps use the same supported
`Int.quotientSpanNatEquivZMod_comp_Quotient_mk` proof as the harness.

No proof-strengthening option is used.

## LeanPool Grothendieck vanishing

The 15 modules below are derived from the Apache-2.0 LeanPool development at
`4eef1ffb3b643d606665e3b5585aa69454e137d1`. That source used Lean
`v4.32.0-rc1` and Mathlib commit
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`. The upstream migration at
`cc54a3adb51cb00b78cbe025818a24b676aeada7` was used as the reference for
Lean `v4.33.0-rc1` and the repository's exact Mathlib commit
`79d0395a1825a6264ad5d269e35e60537518955e`. The local provenance commit
retains the migration commit's `github-actions[bot]`, Vasily Ilin, and Claude
Opus 5 co-author credits.

| Upstream source below `LeanPool/GrothendieckVanishing/` | Local destination below `MazurTorsion/Upstream/LeanPool/GrothendieckVanishing/` |
|---|---|
| `ClosedImmersion.lean` | `ClosedImmersion.lean` |
| `ClosedImmersionCohomology.lean` | `ClosedImmersionCohomology.lean` |
| `CohomologyAPI.lean` | `CohomologyAPI.lean` |
| `ConstantSheafFlasque.lean` | `ConstantSheafFlasque.lean` |
| `FinitelyGeneratedVanishing.lean` | `FinitelyGeneratedVanishing.lean` |
| `FlasqueVanishing.lean` | `FlasqueVanishing.lean` |
| `GeneratedSubsheaf.lean` | `GeneratedSubsheaf.lean` |
| `GrothendieckVanishing.lean` | `GrothendieckVanishing.lean` |
| `GrothendieckVanishingOverview.lean` | `GrothendieckVanishingOverview.lean` |
| `IrreducibleStep.lean` | `IrreducibleStep.lean` |
| `PresheafFilteredColimit.lean` | `PresheafFilteredColimit.lean` |
| `PresheafFilteredColimitCore.lean` | `PresheafFilteredColimitCore.lean` |
| `PresheafFilteredColimitGeneral.lean` | `PresheafFilteredColimitGeneral.lean` |
| `TopologicalKrullDim.lean` | `TopologicalKrullDim.lean` |
| `ZeroOutside.lean` | `ZeroOutside.lean` |

The mathematical decomposition and public theorem statements are retained.
Imports are repointed into the project namespace. Exact-pin elaboration
repairs name the opaque `TopCat.Sheaf` objects used at categorical boundaries,
use the canonical abelian image `kernel (cokernel.π f)` and its factorization,
and keep sheaf-cohomology targets as bundled `sheafCohomologyFunctor` objects.
Filtered-colimit quotient naturality and its universal property are proved
through explicit typed morphisms. The upstream `implicit_reducible` commands
are not retained; the one class-valued constructor carries Lean's supported
`instance_reducible` API annotation.

`MazurTorsion.Upstream.CurveCohomologyGrothendieckVanishing` is the named
downstream consumer. It combines Tau Ceti's codimension-one theorem for a
smooth integral relative curve with properness and smooth finite type to prove
Noetherianity, then applies `GrothendieckVanishing` to the actual underlying
additive sheaf of a scheme module. It proves vanishing in every degree at least
two; it deliberately makes no finite-dimensionality or coherence claim.

## Mathlib Dedekind-zeta finite-fibre adaptation

`MazurTorsion/NumberTheory/WeakChebotarev.lean` adapts the finite-fibre
counting rewrite in Xavier Roblot's Apache-2.0
`Mathlib/NumberTheory/NumberField/DedekindZeta.lean` at the exact pinned
Mathlib commit `79d0395a1825a6264ad5d269e35e60537518955e`. The file retains
the upstream copyright and author credit. Its norm-product ideal embedding,
zeta-square domination, and nonsplitting theorem are new local work.

## AINTLIB geometry substrate

Ninety local Apache-2.0 modules were selected from the AINTLIB
`dev/modular-curves` snapshot at
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684` and placed below
`MazurTorsion/Upstream/AINTLIB/`. The original forty-four-module foundation
and the thirteen finite-action quotient modules comprise the whole files and
narrow option-free slices in the following table:

| Upstream source below `projects/ModularCurves/ModularCurves/` | Local destination |
|---|---|
| `ForMathlib/CartierDual.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/CartierDual.lean` |
| `ForMathlib/SheafOfModulesMonoidal.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafOfModulesMonoidal.lean` |
| `ForMathlib/SchemeModuleSheaf.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleSheaf.lean` |
| `ForMathlib/SheafCohomologyExact.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCohomologyExact.lean` |
| `ForMathlib/FinitePresentationOfFinite.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/FinitePresentationOfFinite.lean` |
| `ForMathlib/BaseChangeAlongCompat.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/BaseChangeAlongCompat.lean` |
| `ForMathlib/InvariantBaseChange.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/InvariantBaseChange.lean` |
| `ForMathlib/InvariantLocalization.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/InvariantLocalization.lean` |
| `ForMathlib/SpecGroupAction.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SpecGroupAction.lean` |
| `ForMathlib/PullbackLocalAtTarget.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/PullbackLocalAtTarget.lean` |
| `ForMathlib/InvariantTorsor.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/InvariantTorsor.lean` |
| `ForMathlib/EtaleCancellation.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/EtaleCancellation.lean` |
| `ForMathlib/AffineQuotient.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/AffineQuotient.lean` |
| `ForMathlib/SchemeQuotient.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeQuotient.lean` |
| `ForMathlib/SchemeActionFree.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeActionFree.lean` |
| `ForMathlib/TorsorMap.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TorsorMap.lean` |
| `ForMathlib/QuotientTorsor.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/QuotientTorsor.lean` |
| `Picard/Pic.lean` | `MazurTorsion/Upstream/AINTLIB/Picard/Pic.lean` |
| `ForMathlib/FormalCoproductAdditive.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/FormalCoproductAdditive.lean` |
| `ForMathlib/FiniteHomologySequence.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/FiniteHomologySequence.lean` |
| `ForMathlib/BaseChangeKerCoker.lean` (only `Module.Finite.of_exact_of_finite`) | moved into `FiniteHomologySequence.lean` |
| `ForMathlib/SchemeModuleBaseCechBasic.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleBaseCechBasic.lean` |
| `ForMathlib/SchemeModuleBaseCech.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleBaseCech.lean` |
| `ForMathlib/SchemeModuleBaseCechExact.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleBaseCechExact.lean` |
| `ForMathlib/SchemeModuleBaseCechFlat.lean` (only `baseCechFactor` and `baseCechXIsoPi`) | moved into the preceding two core modules |
| `ForMathlib/SchemeModuleOrderedBaseCech.lean` (lines 1–310, before the flatness tail) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechBasic.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechFunctor.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechFunctor.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechExact.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechExact.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechLowDegreeFinite.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechLowDegreeFinite.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechComparison.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechComparison.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechHOne.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechHOne.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechHOneFinite.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechHOneFinite.lean` |
| `ForMathlib/SchemeModuleSupport.lean` (closed-stalk support rank core only) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleClosedStalkSupport.lean` |
| `ForMathlib/SheafCechCochains.lean` (generic product/cochain equivalences and separated affine-intersection lemma; affine-vanishing tail omitted) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechCochains.lean` |
| `ForMathlib/SheafCechDifferential.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechDifferential.lean` |
| `ForMathlib/TopCatSheafRestrict.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TopCatSheafRestrict.lean` |
| `ForMathlib/SheafCechSheafTerms.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafTerms.lean` |
| `ForMathlib/SheafCechSheafDifferential.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafDifferential.lean` |
| `ForMathlib/SheafCechSheafComplex.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafComplex.lean` |
| `ForMathlib/SheafCechSheafAugmentation.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafAugmentation.lean` |
| `ForMathlib/SheafCechSheafZeroExact.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafZeroExact.lean` |
| `ForMathlib/SheafCechSheafLocalContraction.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafLocalContraction.lean` |
| `ForMathlib/SheafCechSheafPositiveExact.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafPositiveExact.lean` |
| `ForMathlib/SheafCechSheafResolution.lean` (augmentation-mono slice only) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechSheafResolution.lean` |
| `ForMathlib/FlasqueCohomology.lean` (notation and the two consumed instances only) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCohomologyCompat.lean` |
| `ForMathlib/SheafDerivedGlobalSections.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafDerivedGlobalSections.lean` |
| `ForMathlib/SheafCechGlobalSections.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechGlobalSections.lean` |
| `ForMathlib/SheafCechFlasqueHOne.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechFlasqueHOne.lean` |
| `ForMathlib/SheafCechInjectiveBicomplex.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechInjectiveBicomplex.lean` |
| `ForMathlib/TotalComplexUpNat.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TotalComplexUpNat.lean` |
| `ForMathlib/TotalComplexUpNatLowDegrees.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TotalComplexUpNatLowDegrees.lean` |
| `ForMathlib/TotalComplexUpNatHorizontalEdge.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TotalComplexUpNatHorizontalEdge.lean` |
| `ForMathlib/TotalComplexUpNatHorizontalEdgeHOne.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TotalComplexUpNatHorizontalEdgeHOne.lean` |
| `ForMathlib/TotalComplexUpNatVerticalEdge.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TotalComplexUpNatVerticalEdge.lean` |
| `ForMathlib/SheafCechInjectiveAugmentation.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechInjectiveAugmentation.lean` |
| `ForMathlib/SheafCechInjectiveComparison.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechInjectiveComparison.lean` |
| `ForMathlib/AcyclicAffineCechComparison.lean` (degree-one comparison only) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/AcyclicAffineCechComparison.lean` |
| `ForMathlib/SchemeModuleBaseCechHomology.lean` (homology isomorphisms only) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleBaseCechHomology.lean` |

The canonical-support extension adds twenty-six local modules. It draws on
the following twenty-seven source files because the open-unit module embeds
only the required mate-comparison slice of `OpenAdjunction`, while the support
source is split between the earlier rank core and the remaining support API:

| Upstream source below `projects/ModularCurves/ModularCurves/` | Local destination or retained slice |
|---|---|
| `ForMathlib/SpecBasicOpenAway.lean` | `ForMathlib/SpecBasicOpen.lean` (`specBasicOpen` only) |
| `ForMathlib/SchemeModuleRestrictLimits.lean` | same basename |
| `ForMathlib/SchemeModuleRestrictPushforward.lean` | same basename |
| `ForMathlib/SchemeModuleQuasicoherent.lean` | same basename |
| `ForMathlib/SheafModuleFiniteTypeQuotient.lean` | same basename |
| `ForMathlib/SchemeModuleSupport.lean` | `SchemeModuleSupport.lean` (after the separately retained rank core) |
| `ForMathlib/SchemeModuleComparisonCoherent.lean` | same basename |
| `ForMathlib/SchemeModuleSupportDrop.lean` | same basename |
| `ForMathlib/SchemeModuleComparisonSupport.lean` | same basename |
| `ForMathlib/FiniteModuleSupportAnnihilation.lean` | same basename |
| `ForMathlib/FiniteFamilySupportAnnihilation.lean` | same basename |
| `ForMathlib/FiniteAffineSupportAnnihilation.lean` | same basename |
| `ForMathlib/IdealSheafPowerSubscheme.lean` | same basename |
| `ForMathlib/SchemeModuleOpenCoverIso.lean` | same basename |
| `ForMathlib/AdjunctionUnitIsoTransport.lean` | same basename |
| `ForMathlib/SurjectiveRestrictionScalars.lean` | same basename |
| `ForMathlib/AffineModuleBaseChange.lean` | same basename (affine-tilde unit slice) |
| `ForMathlib/AffineIdealQuotientPullbackUnit.lean` | same basename |
| `ForMathlib/SchemeModulePullbackUnitComposition.lean` | same basename |
| `ForMathlib/IdealSheafAffineChartPullbackUnit.lean` | same basename |
| `ForMathlib/IdealSheafSubschemeAffineChart.lean` | same basename |
| `ForMathlib/IdealSheafSubschemeRestrictPullbackUnit.lean` | same basename |
| `ForMathlib/FiniteSupportIdealSheafPullbackUnit.lean` | same basename |
| `ForMathlib/SchemeModuleOpenUnitIso.lean` | same basename |
| `Picard/DualPullback/OpenAdjunction.lean` | private comparison slice in `SchemeModuleOpenUnitIso.lean` |
| `ForMathlib/SchemeModuleCanonicalSupportThickening.lean` | same basename |
| `ForMathlib/SchemeModuleCanonicalSupportFull.lean` | same basename |

The finite-pushforward/Čech extension adds seven local AINTLIB modules:

| Upstream source below `projects/ModularCurves/ModularCurves/` | Local destination or retained slice |
|---|---|
| `ForMathlib/SchemeInducingOpenLift.lean` | same basename |
| `ForMathlib/SchemeModulePushforwardMapRestrictionIso.lean` | same basename |
| `ForMathlib/SchemeModuleRestrictionIsoMonotone.lean` | same basename |
| `ForMathlib/SchemeModuleOrderedBaseCechPushforward.lean` | same basename |
| `ForMathlib/SchemeModuleBaseCechPushforward.lean` | same basename |
| `ForMathlib/SchemeModuleOrderedBaseCechHomologyRetract.lean` | same basename |
| `ForMathlib/SchemeModulePushforwardPullbackSupport.lean` | same basename (support-only slice) |

The project-owned `SchemeModuleFinitePushforward` proves that pushforward
along a finite morphism preserves finite type for quasicoherent modules.
Its checked consumer `SchemeModuleFinitePushforwardCech` specializes the
Apache-licensed AINTLIB
`SchemeModuleOrderedBaseCechPushforwardFinite.lean` comparison to the
retained degree-zero/degree-one predicate and combines it with that finite
pushforward theorem.

The audited `dev/modular-curves` snapshot has no root `LICENSE` file. The
selected sources preserve their per-file Apache-2.0 headers and authorship
where present. Exact repository-level license evidence is AINTLIB
`origin/main` commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`,
whose root `LICENSE` is Apache License 2.0. That commit and the selected dev
commit are divergent: neither is an ancestor of the other. Every selected
source without a per-file header is byte-identical at the license-bearing main
commit. The exact Git blob identities are:

| Headerless source | Blob at both exact commits |
|---|---|
| `ForMathlib/SchemeModuleSheaf.lean` | `b735f77f920d236c5416f43201aefd9804cea4b6` |
| `ForMathlib/SheafCohomologyExact.lean` | `5e8e401a5556eef7940273fd1443b84c236fabbb` |
| `ForMathlib/SchemeModuleBaseCech.lean` | `d62a2d04dab99e404c934d5f25e28738b5539175` |
| `ForMathlib/SheafCechCochains.lean` | `cba6087ad0f679b62d96e6ed90a903b98d208a45` |
| `ForMathlib/SheafCechDifferential.lean` | `09f04ff660cd0409dd09d478bbfa03f8ae023428` |
| `ForMathlib/TopCatSheafRestrict.lean` | `329d123b629d4f6f3a1ed835b581979fdf8157f0` |
| `ForMathlib/SheafCechSheafTerms.lean` | `39d21d24b4486535f4eb3619e4ba3ffa6f7d9d2a` |
| `ForMathlib/SheafCechSheafDifferential.lean` | `f850801ff3badb73afe98caddbb473cecc41195c` |
| `ForMathlib/SheafCechSheafComplex.lean` | `8300aa4c67c0b49ecc4c7a2feb3af931d2c944bd` |
| `ForMathlib/SheafCechSheafAugmentation.lean` | `edbb87a0c8ccc10fec7ae0909342d2c320db7633` |
| `ForMathlib/SheafCechSheafZeroExact.lean` | `c50ea2fe69a40fea5a8c95df35fa5cd289867c64` |
| `ForMathlib/SheafCechSheafLocalContraction.lean` | `7632d45aa819b7722e7c0d706fa39ec7a6225ce4` |
| `ForMathlib/SheafCechSheafPositiveExact.lean` | `ca8c7d356551d86ac376ec0b49b1d91dc098d61f` |
| `ForMathlib/SheafCechSheafResolution.lean` | `d8fe553af7e3ad4c8aa1e026a4870c9d1b553f1f` |
| `ForMathlib/FlasqueCohomology.lean` | `1f221974db26088d0125f98660e0e112bec31057` |
| `ForMathlib/SheafDerivedGlobalSections.lean` | `ae7d7b84958a41952839b7db3933cfd74289b6e8` |
| `ForMathlib/SheafCechGlobalSections.lean` | `60596d0bfcbb4898d0b3e9f8b7d12e338f48b760` |
| `ForMathlib/SheafCechFlasqueHOne.lean` | `493e1a337d56be17655f5226c8225b10e83cda7d` |
| `ForMathlib/SheafCechInjectiveBicomplex.lean` | `818e9a665c5c6a95c94fd5d61caa68f72d9aca0d` |
| `ForMathlib/TotalComplexUpNat.lean` | `0474bd3f2a2aa1e2e7d7b6d29de4a4452bd1d12c` |
| `ForMathlib/TotalComplexUpNatLowDegrees.lean` | `5c930050e242125ff6e40e18bf6c92dc470222cf` |
| `ForMathlib/TotalComplexUpNatHorizontalEdge.lean` | `7afc3676283db484a633f32e4030e860980f6028` |
| `ForMathlib/TotalComplexUpNatHorizontalEdgeHOne.lean` | `53e26cb1b79780764cf5436b16c13adcbb942f87` |
| `ForMathlib/TotalComplexUpNatVerticalEdge.lean` | `18e9971b7c022c493e95dc92b071f74efd5a63f1` |
| `ForMathlib/SheafCechInjectiveAugmentation.lean` | `8ac8456dd40af6d01d98248d8d065dba5b35053f` |
| `ForMathlib/SheafCechInjectiveComparison.lean` | `335e363809ef308c61d920e13f1e74d7fbab72ac` |
| `ForMathlib/AcyclicAffineCechComparison.lean` | `8d75511490b1de235f7eb18bccb4b3182111afd7` |
| `ForMathlib/SchemeModuleBaseCechHomology.lean` | `12d8d3ba48e121d543cc3cc065d9fa56ced92801` |

Their local headers use that exact licensed-blob evidence together with Chris
Birkbeck's repository authorship/history; they were not present in the dev
source files.
`SchemeModuleOrderedBaseCechHOneFinite.lean` retains its broader AINTLIB
contributors header. The port preserves declarations and namespaces. The
`SchemeModuleSheaf` and `SheafCohomologyExact` declarations and proofs are
source-preserving modulo formatting and syntax modernization; they compile
directly at the immutable pin. Changes to `CartierDual`,
`SheafOfModulesMonoidal`, and `Pic` are limited to repointing the one
internal import, removing source-level `set_option` commands, replacing
linter-reported goal conversions with `change`, explicitly omitting unused
section variables, and using `erw` at one semireducible sheaf-map rewrite
required by the immutable Mathlib pin.

The sheaf-Cech foundation removes the source import of
`AcyclicAffineOpenCover` from `SheafCechCochains` and omits that file's affine
tail. Its generic cochain API instead imports the already reviewed local
base-Cech foundation. `TopCatSheafRestrict` carries no backward-elaboration
options: its adjunction unit component is proved with the explicit Mathlib
`sheafPushforwardContinuous_unit_app_hom_app` theorem. The named downstream
consumer of these foundations is the checked sheaf-level complex
`TopCat.Sheaf.cechComplex` in `SheafCechSheafComplex`.

The remainder of the retained sheaf-Cech lane proves exactness of the
augmented sheaf complex, computes its global sections, constructs the
first-quadrant injective Cech bicomplex and its two low-degree edge maps, and
identifies native Cech homology in degree one with Ext-based sheaf cohomology.
`SheafCechSheafResolution` is cut immediately after
`cechAugmentation_mono`; its unused packaged acyclic-complex tail is omitted.
The unused `SheafCohomologyFiniteProducts`, `SheafCechFlasqueTerms`, and
`SheafCechZero` modules are not retained. Global sections imports the narrow
resolution slice directly, and the injective bicomplex exposes only the
degree-one row exactness consumed by comparison.
The full source `FlasqueCohomology` module is not retained: the four notation
aliases and two instances actually consumed by this lane live in
`SheafCohomologyCompat`, and the instances are derived from the already
checked project theorems `injectiveSheaf_isFlasque` and
`flasqueSheaf_H_succ_subsingleton`. The three source compatibility options in
`TotalComplexUpNatVerticalEdge` are replaced by explicitly typed flip maps,
the sign equality, and its composition calculation. Same-file construction
machinery is private in the local API.

The affine comparison is also deliberately narrow. The degree-one theorem
from `AcyclicAffineCechComparison` obtains the required restricted positive
cohomology vanishing from the project's checked affine quasicoherent theorem,
instead of importing AINTLIB's larger `AffineVanishing` cone.
`SchemeModuleBaseCechHomology` retains only the two homology isomorphisms
needed to pass from the base-linear complex to the native additive Cech
complex and then to sheaf `H¹`.

The thirteen finite-action quotient modules retain the declarations and
namespaces of the same exact snapshot. Imports between retained AINTLIB
modules are repointed into the local namespace, blank lines are normalized,
and source-level backward-elaboration options and linter suppressions are
omitted. Their exact upstream blobs, in the table order from
`FinitePresentationOfFinite` through `QuotientTorsor`, are
`a63130001df32873fa40737b55c3f916a282bc93`,
`f4f98c82bcb0d3db4f9626a5d5c520e70f351e14`,
`4ad231cfa7290a7d577970b1a72fa71ef44feac2`,
`f4843478116fef7247d67ab319e34a1e9c275f16`,
`002f96481b6bdc393cb4209dd8cdc78dd524d76d`,
`df99ae754b2ddac032c4b016a6b6b99780f2e0eb`,
`13d27b67025a5b610abbd0824090e3e7f66926e0`,
`a019115d6f72da6ee7d8c536115a0354fd5a1469`,
`83a2c33579548f37b3279d5dd8aa978117c66a5b`,
`69f2aa854184ac53c24b23ae6eba46f83eccf9a8`,
`08c2bdb598a75f6f8ab7aed7100616e732a6ee64`,
`11ccd932de1300067c26118dc277d8adaceb5aa6`, and
`722ec41c6ec7da27031c1cc2e4d664fe87b1c57f`. Each exact blob has an explicit
Apache-2.0 file header. Four proof-level elaboration repairs were required at
this repository's
immutable pin. In `SpecGroupAction`, the prime-ideal membership proof now
states the scheme/prime-spectrum coercion explicitly and installs the two
available `IsPrime` witnesses locally. In `BaseChangeAlongCompat`, the finite
affine-target predicate is named to resolve its `outParam`, and the existing
Mathlib witnesses for locality, base-change stability, fppf descent, and
étale multiplicativity are applied explicitly instead of through fragile
`inferInstance` calls. Its finite affine-property proof is adapted from pinned
Mathlib `Morphisms/Finite.lean` blob
`cf6826b55377d33e384b8db846996ecf55bf8c9b` (Christian Merten and Andrew
Yang), and its fpqc-to-fppf descent proof from `Morphisms/FlatDescent.lean`
blob `754666351a96d06b20f2d755c23e39601f590178` (Christian Merten); both are
Apache-2.0. In `SchemeQuotient`, affine-open naturality uses the current
`IsAffineOpen.isoSpec_hom` and `Scheme.Opens.toSpecΓ_SpecMap_appLE` API, the
now-redundant closing `rfl` is removed, and diagonal composition is expressed
through an explicitly named morphism property. In `QuotientTorsor`, the
affine torsor comparison names its correctly typed invariance witness and
normalizes the two pullback legs and final symmetry to explicit `Spec.map`
representatives, so the existing componentwise isomorphism instances apply.
No statement is weakened. The modules construct the
quotient of a scheme by a finite action from a stable affine atlas, prove the
quotient projection finite, and in the free-action case prove it finite
étale, surjective, and a torsor after arbitrary base change. The new local
translation-quotient consumer descends the commutative group law through that
checked universal property.

That consumer also adapts proof skeletons from AINTLIB
`GroupScheme/TranslationBySection.lean`, exact blob
`6223d2904bc6f2162d4ee4e77ed684a40396ef18`. The file at the audited
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684` snapshot has no license header,
so the license basis is the identical blob at AINTLIB commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, whose root Apache-2.0 license
has blob `8dada3edaf50dbc082c9a125058f25def75e625a`. Authorship from the introducing
commit is retained for Chris Birkbeck and co-author Claude Opus 4.8. Only the
constant-section, translation, and elementary composition proof skeletons are
adapted; the tensor equivariance, inverse conjugation, action, quotient
descent, and group-object construction are new local proofs. This adapted
source is not counted among the eighteen vendored modules above.

The retained exact-sequence core and exact additive-sheaf forgetful functor
are consumed by
`MazurTorsion.Upstream.SchemeModuleCohomologyDimensionShift`. That module
proves the injective long-exact-sequence step for the actual affine-cover
short exact sequence. It does not import AINTLIB's full affine-vanishing
proof: the local-killing and cokernel-vanishing argument remains a separate
checked dependency.

The ordered/native base-Cech lane is a separate option-free slice. The
unused `AcyclicAffineCechComparison` import in `SchemeModuleBaseCech` is
replaced by the direct `SchemeModuleSheaf` dependency. The two concrete
factor/product declarations needed by comparison are moved out of
`SchemeModuleBaseCechFlat`, and the ordered complex is cut immediately
after `orderedBaseCechLinearDifferential_comp`, before its flatness and
Picard-specific tail. Its only compatibility change is supplying the pivot
argument to `Fin.succAbove_right_injective`, eliminating two current style
warnings. No proof option, source placeholder, affine-comparison module,
flat/Picard module, or properness cone is imported.
Declarations used only as same-file proof machinery remain private in the
local port, and the unused exact-retract helper and its sole downstream proof
are omitted. The base-presheaf and base-Cech functors are now public because
the exactness and low-degree modules below are compiled consumers.

The low-degree finiteness extension was audited both at the selected pin and
at AINTLIB head `6b879658fe916b5db2afcddebbed35a9dc10aa61` (2026-08-08).
Every newly selected source blob is byte-identical at those commits:
`FiniteHomologySequence` `3fe42c878286f9ef96898a29dc9ff2a3d19d4f47`,
`SchemeModuleBaseCechExact` `cba942a282cb96812f71c9df1245193724baef28`,
`SchemeModuleOrderedBaseCechFunctor`
`8e848e5fd9cc80bba786e9ae7f1043b1c45fa7e2`,
`SchemeModuleOrderedBaseCechExact`
`3178e4d70a15754557cfe03eb17e73f519a70915`,
`SchemeModuleOrderedBaseCechLowDegreeFinite`
`cf75b285fa7296c58ee07acbbe97cd01fadbc5c2`,
`SchemeModuleSupport` `05e468b4ebf3d416878f813a51f3d9b09e91e07a`,
and `BaseChangeKerCoker` `a3f9de90ecf592ea374d40bd30dccb1ab207fd38`.
All carry per-file Apache-2.0 headers.

The canonical-support extension was checked at the selected snapshot, AINTLIB
head `6b879658fe916b5db2afcddebbed35a9dc10aa61`, and the license-bearing main
commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`. Every source blob below is
byte-identical at all three commits:

```text
SpecBasicOpenAway                         e095f85c410aaf1f801fa56f487d76c554406d54
SchemeModuleRestrictLimits                4fe7c7bfca56a2c998e605626abfe2ece9b415ec
SchemeModuleRestrictPushforward           ea28c07e0ef7b10b88289f1553033ceaa8e1e606
SchemeModuleQuasicoherent                 057755cb6d2bf099a37c7a6cd5a6a22e5379205a
SheafModuleFiniteTypeQuotient             b8f4a381af4a1e065dd5902dc8540d2b96b8e86a
SchemeModuleSupport                       05e468b4ebf3d416878f813a51f3d9b09e91e07a
SchemeModuleComparisonCoherent            317261046fcf79bcfe62814d2418cb16630f1900
SchemeModuleSupportDrop                   d9d5b1e42f7ed8430cc4be63ee8c8da8abcf6da0
SchemeModuleComparisonSupport             ae86e35866a3598a2f07390c9c0a9b3b5d459813
FiniteModuleSupportAnnihilation           875f3cfcd0abd5c439ba3da82f80d8a711abbbfe
FiniteFamilySupportAnnihilation           4bef8777d1a0b3cf3f85fbe61da5fa9c7b3c6427
FiniteAffineSupportAnnihilation           f85d62d009d257f27e35a2362103d4756eb62fb8
IdealSheafPowerSubscheme                  f9952c7efea956f34d9c994e6653102ebb316849
SchemeModuleOpenCoverIso                  d465c770c8e1ce2df4385af6e2c59a83e1e68b18
AdjunctionUnitIsoTransport                fd2abc869c3f903765fe3ecf911904d2c4d2d122
SurjectiveRestrictionScalars              23273f3b313ee2ce7ad9d104f81abb34782136ee
AffineModuleBaseChange                    bf22627acabeed6cb8e1d6f67d413b5b69f030dc
AffineIdealQuotientPullbackUnit           9fcc28f9acb8992d1f38cab69f60bc0ed1921e36
SchemeModulePullbackUnitComposition       fd04f9660e2580a0f94c7a393890460284497ae0
IdealSheafAffineChartPullbackUnit         62c309c86671c759805fcbd425960c437ad6c140
IdealSheafSubschemeAffineChart            bd2070312717e39dbbc481a3eeff1a7ae23bed21
IdealSheafSubschemeRestrictPullbackUnit   226d1f541c164c20051e90922157dd9baa7e2c51
FiniteSupportIdealSheafPullbackUnit       bda3f5b8cb5626982f4f4382270beaf78125b618
SchemeModuleOpenUnitIso                   8dd3b6b404de1f0bd74b8239684ab600f4bbb7ab
Picard/DualPullback/OpenAdjunction        82b26b00fe5e8b57f9c3ec98d6db0971ecb99be1
SchemeModuleCanonicalSupportThickening    2bbf06a913a5f6bb55570a8929a131f7f7201e78
SchemeModuleCanonicalSupportFull          ff3b65392ba91c12e5f250c9dde9dd1640850efd
```

The extension is adapted to the immutable older Mathlib pin without options.
`SpecBasicOpen` stops before the source compatibility tail. The full support
module imports the already retained rank core and omits only duplicate
declarations. The affine-base-change module retains exactly the tilde-unit
comparison consumed by the affine ideal-quotient theorem; quasicoherence of
its pullback is transported across that same comparison. The open-unit module
keeps its public localization theorem and the explicit pullback-square
comparison consumed by the pushforward/pullback support theorem, while its
conjugate-equivalence calculation remains private; this avoids the unrelated
Picard dependency cone. The generated long-name colimit instance in the
quasicoherent source is expanded to its source proof body for the style gate,
and the older-pin finite-module call is supplied explicitly. The two
base-presheaf restriction comparison declarations are public only because
`SchemeModuleQuasicoherent` is their compiled downstream consumer.

This checkpoint proves that every finite-type quasicoherent module on a
Noetherian scheme has a canonical closed thickening model whose
pullback--pushforward unit is invertible, and that the model has full closed
stalk support. It also retains the finite-type/quasicoherent comparison
residuals and their strict support decrease. These are inputs to, not a
substitute for, the Chow/projective low-degree comodel. No properness or
cohomology-finiteness conclusion is claimed at this checkpoint.

The finite-pushforward/Čech extension was checked at historical direct
low-degree commit `d78d10a74577e28840d21eb4e07395d87c44370f`, AINTLIB head
`6b879658fe916b5db2afcddebbed35a9dc10aa61`, and license-bearing main commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`. Every source blob is
byte-identical at all three commits:

```text
SchemeInducingOpenLift                         ccf539a03181e015fa47166cd71593c4278bdf9d
SchemeModulePushforwardMapRestrictionIso      43fcbc86d17090eb407ccc1e9c394e53809c50de
SchemeModuleRestrictionIsoMonotone            93c4c4968e3a18013575acaae7ac65ec06cedda1
SchemeModuleOrderedBaseCechPushforward        b990c1c8b7bffc3b6aafbadab40e449df1d5bc07
SchemeModuleBaseCechPushforward               5e7753aca27fa64b6aff8d27f3370a41a23985cc
SchemeModuleOrderedBaseCechHomologyRetract    12a220cf08300a3ae58e278c14bdb4c105dcdf6a
SchemeModulePushforwardPullbackSupport        77359ef7d3bed34bad0c0dbf808bda8cd62cb218
SchemeModuleOrderedBaseCechPushforwardFinite  48ab1220efbbaee5acb3dad357c402c11630fc3c
```

All eight sources carry per-file Apache-2.0 headers. Imports are repointed to
the reviewed local cone. `SchemeModuleOrderedBaseCechPushforward` defines
locally the two section abbreviations that its source obtains from a broader
base-change module. `SchemeModulePushforwardPullbackSupport` stops before the
unconsumed tensor/invertible tail. The low-degree consumer transports only
degrees zero and one rather than importing AINTLIB's all-degree finiteness
predicate. Public helper declarations in the existing Čech and open-unit
modules now each have one of these checked comparison/support modules as a
downstream consumer.

The original closed-support induction slice does not import the 1,956-line
`SchemeModuleQuasicoherent` module; the later canonical-support,
finite-pushforward, and projective-line extensions intentionally do. None of
these retained slices imports AINTLIB's all-degree properness cone.
Affine-open exactness in the induction slice reuses the project's checked
affine quasicoherent section-surjectivity theorem, transported through the
affine spectrum isomorphism. The one Noetherian exact-pair lemma needed by
the long homology sequence is retained as the named `BaseChangeKerCoker`
slice. The zero-object case is proved directly in degrees zero and one, and
the support induction takes quasicoherence of the comparison image as an
explicit comodel witness. The source exactness declarations receive shorter
local names to satisfy the repository's style gate. The projective-line
extension uses the reviewed local quasicoherent module to obtain finite-type
chart sections and their localization maps for coherent modules.

The project-facing `IsCoherentLowDegreeSupportComodel` packages the remaining
producer boundary. Its closed-support induction consumer proves ordered
degree-one finiteness, which feeds
`genuineSheafHOne_finite_of_coherentSupportComodels`. This is a checked
low-degree reduction, not a properness theorem: the canonical-support Chow
construction producing such comodels remains the next open seam.

The new project-facing consumer
`MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.nativeBaseCechHOne_finite_of_ordered`
takes finite generation of ordered degree-one homology and proves finite
generation of native base-Cech degree-one homology. It does not identify
Cech homology with Ext/sheaf cohomology or establish the ordered input from
properness.

The separate checked boundary
`MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.nativeBaseCechHOneForgetIso_of_affineOpenCover`
now identifies the additive group underlying native base-Cech degree-one
homology with genuine sheaf `H¹` on an affine open cover. Its elementwise
consumer `exists_nativeBaseCechHOne_class_of_sheafHOne_class` verifies that
the comparison is actually usable. The project-facing module
`SchemeModuleBaseCechHOneModule` transports the global-functions action from
native base-Cech homology to genuine sheaf `H¹` without registering a global
instance, and exposes a linear equivalence for that explicit action. Its named
downstream consumer
`genuineSheafHOne_finite_of_ordered_affineOpenCover` transfers ordered Cech
finite generation through both the ordered/native and native/sheaf
comparisons. The remaining seams include the proper ordered input, low-degree
Chow/properness input, general proper-curve `H¹` finiteness, and the complete
curve facade; the transport alone asserts no properness, base change, or
semicontinuity.

`MazurTorsion.Upstream.ProjectiveLineCechHOneFinite` supplies a distinct
checked ordered input for the two standard affine charts of `P¹`. Its
principal-parts calculation identifies the degree-zero differential, after
the explicit overlap equivalence, as the infinity restriction minus the
standard restriction. Finite generation of the resulting cokernel gives
ordered Cech `H¹` finiteness and hence genuine sheaf `H¹` finiteness for every
finite-type quasicoherent module on `P¹`. The finite-pushforward comparison
then transports this result along any finite morphism to `P¹`. Restricting the
explicit global-functions action through the canonical isomorphism
`K ≃ Γ(Spec K, ⊤)` gives a checked `K`-module structure and finite-dimensional
`H¹`. The named consumers `genuineSheafHOne_finite_of_hyperellipticMap` and
`genuineSheafHOne_finiteDimensional_of_hyperellipticMap` apply these results
to the default-transparency finite hyperelliptic map from the projective
order-thirteen curve. The generic theorem keeps that finite map as an explicit
hypothesis: it does not construct a finite map to `P¹` for every proper curve,
classify modular-curve rational points, or prove Mazur's torsion theorem.

The larger relative-Picard cone was tested but not retained: at this pin its
essential elaboration depends on source-level backward-compatibility options,
which this repository forbids. `MuN.lean` was also not copied because the
audited file lacks an explicit license header. Files with placeholders or an
unclean transitive cone remain prior art only. This is why AINTLIB is a
selective attributed port rather than a Lake dependency.

`MazurTorsion.Upstream.Geometry` is the reviewed boundary for the Picard and
Cartier-duality ports;
`MazurTorsion.Upstream.SchemeModuleCohomologyDimensionShift` is the boundary
for the two sheaf-cohomology ports. The named boundary for the ordered/native
Cech lane is `MazurTorsion.Upstream.SchemeModuleBaseCechHOneFinite`.
The named boundary for the native-Cech/sheaf-cohomology comparison is
`MazurTorsion.Upstream.SchemeModuleBaseCechHOneComparison`.
The named boundary for its explicit global-functions action is
`MazurTorsion.Upstream.SchemeModuleBaseCechHOneModule`, consumed by the
ordered-H¹ finiteness boundary.
The named boundary for the projective-line principal-parts and finite-map
specialization is
`MazurTorsion.Upstream.ProjectiveLineCechHOneFinite`.
`MazurTorsion.lean` is the named checked consumer of the earlier geometry
boundaries. The geometry boundary also imports Tau Ceti's line-bundle and
Abel--Jacobi layers from the root package's exact dependency.

## AINTLIB Hilbert 92 and Hilbert 94

Six Apache-2.0 modules were selected from AINTLIB's `main` snapshot at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b` and placed below
`MazurTorsion/Upstream/AINTLIB/FltRegular/NumberTheory/`:

| Upstream source below `projects/FltRegular/FltRegular/NumberTheory/` | Local destination |
|---|---|
| `CyclotomicRing.lean` | `CyclotomicRing.lean` |
| `SystemOfUnits.lean` | `SystemOfUnits.lean` |
| `Hilbert92.lean` | `Hilbert92.lean` |
| `Unramified.lean` | `Unramified.lean` |
| the class-group power lemma from `RegularPrimes.lean` | `RegularPrimes.lean` |
| `Hilbert94.lean` | `Hilbert94.lean` |

The 1,499-line local cone adds attribution headers naming Chris Birkbeck,
based on the upstream authorship/history and repository-wide Apache-2.0
license; the selected upstream files themselves had no per-file headers. It
proves the generic theorem that an unramified cyclic number-field extension
of odd prime degree has degree dividing the base class number. The source used
Lean `v4.33.0-rc1` and Mathlib commit
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`; the local port compiles against
the immutable Mazur Mathlib commit
`79d0395a1825a6264ad5d269e35e60537518955e`.

The port removes every source-level transparency option. Pure type aliases
for relative units are `abbrev`s locally, quotient finiteness and finrank
comparisons are supplied through explicit quotient maps and equalities, and
the system-of-units argument uses an explicit restrict-scalars linear
equivalence. The cyclotomic-integer module uses the equivalent theorem names
available at the older pin. `RegularPrimes.lean` is intentionally pruned to
the one class-group lemma used by Hilbert 94. Because the pinned Mathlib
cohomological Hilbert-90 endpoint fixes its extension field in `Type`, the
local `Hilbert94.lean` adds an option-free `Shrink` transfer for finite
extensions. Thus the checked Hilbert-94 theorem remains universe-polymorphic
in the extension field over its small number-field base. No theorem statement
is weakened. That file also names Vasily Ilin for this local universe-polymorphic
adaptation.

`MazurTorsion.NumberTheory.CyclotomicHilbert94` is the reviewed specialization
boundary. It proves only that an everywhere finite-place unramified
`InverseExtension` forces `p` to divide the full cyclotomic class number.
`MazurTorsion.PrimeOrder.CyclotomicObstruction` is its named downstream
consumer. This result is explicitly non-equivariant: it does not select the
inverse-character class-group component and therefore does not replace the
remaining reciprocity/reflection theorem.

The checked target is:

```text
LEAN_NUM_THREADS=1 lake build MazurTorsion.NumberTheory.CyclotomicHilbert94
```

`#print axioms dvd_card_classGroup_of_unramified_isCyclic` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## AINTLIB power-residue character adaptation

`MazurTorsion/NumberTheory/CyclotomicJacobiCharacter.lean` selectively adapts
the finite-field power-residue exponent and `MulChar` bridge from these
Apache-2.0 AINTLIB sources at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`:

| Upstream source below `projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/` | Exact source blob | Local destination |
|---|---|---|
| `Basic.lean` | `7b5f3eb9e9fc05c78f08343b2e7e5bd26f7b0f36` | `MazurTorsion/NumberTheory/CyclotomicJacobiCharacter.lean` |
| `Furtwaengler/Character.lean` | `3b0a7103f366944dec6ce6dd10e5fc9438c02a09` | `MazurTorsion/NumberTheory/CyclotomicJacobiCharacter.lean` |

The local derivative removes the upstream package/module syntax, targets the
older immutable Mathlib API, and specializes the character to the residue
field of a prime in `Q(zeta_p)`. It adds the canonical integral root of unity,
exact character order, Galois covariance, and the binomial-sum vanishing
needed by the diagonal Jacobi-sum consumer. The source header retains Chris
Birkbeck as co-author; no source-level options, linter suppressions, or
placeholders are retained.

The checked downstream chain is `CyclotomicJacobiSumTwo` ->
`CyclotomicJacobiIdealFaithful` ->
`CyclotomicJacobiReciprocityReduction`. Mathlib's Apache-2.0
`NumberTheory.JacobiSum.Basic` supplies the generic Jacobi/Gauss-sum
identities; the cyclotomic specialization and ideal factorization are local
proofs. The chain does not import or assume AINTLIB's unfinished one-sided
reciprocity theorem.

## Build and audit

From this standalone package:

```text
lake build EllipticCurves.ReductionAtPrime EllipticCurves.Mathlib.EllipticCurvePoint
lake build EllipticCurves.Examples.ExceptionalCubicReduction
lake build
```

For aggregate integration, the package has a local `lean_lib` named `EllipticCurves` with globs
`["EllipticCurves", "EllipticCurves.+"]`; the existing `MazurTorsion` library imports these modules without
introducing a second mathlib version.

The selected production cone is 31 Lean files and 14,142 lines. On the current pin,
`MazurTorsion.Arithmetic.CardinalityReduction` builds successfully across 8,713 jobs and the
standalone challenge library builds successfully across 8,725 jobs.

A source scan of the 31 files has no proof placeholders, no option-setting command, no
native evaluator invocation, and no custom logical declaration. `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]` for the reduction kernel theorem, `redHom`, the
finite-field count, torsion injectivity, finite-group injectivity, and the final cardinal bound.
