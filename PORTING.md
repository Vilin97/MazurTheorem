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

Thirty-eight local Apache-2.0 modules were selected from the AINTLIB
`dev/modular-curves` snapshot at
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684` and placed below
`MazurTorsion/Upstream/AINTLIB/`. Thirty-two upstream files are retained
whole; seven additional source files contribute the narrow option-free slices
recorded below:

| Upstream source below `projects/ModularCurves/ModularCurves/` | Local destination |
|---|---|
| `ForMathlib/CartierDual.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/CartierDual.lean` |
| `ForMathlib/SheafOfModulesMonoidal.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafOfModulesMonoidal.lean` |
| `ForMathlib/SchemeModuleSheaf.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleSheaf.lean` |
| `ForMathlib/SheafCohomologyExact.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCohomologyExact.lean` |
| `Picard/Pic.lean` | `MazurTorsion/Upstream/AINTLIB/Picard/Pic.lean` |
| `ForMathlib/FormalCoproductAdditive.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/FormalCoproductAdditive.lean` |
| `ForMathlib/SchemeModuleBaseCechBasic.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleBaseCechBasic.lean` |
| `ForMathlib/SchemeModuleBaseCech.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleBaseCech.lean` |
| `ForMathlib/SchemeModuleBaseCechFlat.lean` (only `baseCechFactor` and `baseCechXIsoPi`) | moved into the preceding two core modules |
| `ForMathlib/SchemeModuleOrderedBaseCech.lean` (lines 1–310, before the flatness tail) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechBasic.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechComparison.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechComparison.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechAlternating.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechHOne.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechHOne.lean` |
| `ForMathlib/SchemeModuleOrderedBaseCechHOneFinite.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SchemeModuleOrderedBaseCechHOneFinite.lean` |
| `ForMathlib/SheafCechCochains.lean` (generic product/cochain equivalences; affine-vanishing tail omitted) | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafCechCochains.lean` |
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
Declarations used only as same-file proof machinery are private in the local
port, and the unused exact-retract helper and its sole downstream proof are
omitted. The public comparison spine and the source theorem statements used
by later modules are unchanged.

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
the comparison is actually usable. This is only an additive-group
isomorphism: it does not assert compatibility with the scalar action of
global functions, finite generation, properness, base change, or
semicontinuity. The remaining seams therefore include base-linear Ext
transport, the proper ordered input, low-degree Chow/properness input, proper
`H¹` finiteness, and the curve facade.

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
