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

Twenty-two file-level Apache-2.0 modules were selected from audited AINTLIB
history and placed below `MazurTorsion/Upstream/AINTLIB/`. Nineteen come from
the `dev/modular-curves` snapshot at
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`; the three additional fine-`Y₁`
prerequisite leaves and their exact provenance are recorded below.

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
| `ForMathlib/RepresentableAut.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/RepresentableAut.lean` |
| `ForMathlib/GradedQuotient.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/GradedQuotient.lean` |
| `ForMathlib/ProjFromGlobalSectionsMap.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/ProjFromGlobalSectionsMap.lean` |
| `ForMathlib/TateNormalForm.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/TateNormalForm.lean` |
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

Each file retains its upstream copyright and authorship header (Chris
Birkbeck or the AINTLIB contributors) and Apache-2.0 attribution. The port
preserves declarations and namespaces. In the original five-file tranche,
the `SchemeModuleSheaf` and `SheafCohomologyExact` declarations and proofs are
source-preserving modulo formatting and syntax modernization; they compile
directly at the immutable pin. Changes to the other three files in that
tranche are limited to repointing the one internal import, removing
source-level `set_option` commands, replacing linter-reported goal
conversions with `change`, explicitly omitting unused section variables, and
using `erw` at one semireducible sheaf-map rewrite required by the immutable
Mathlib pin.

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

`RepresentableAut.lean` is retained byte-for-byte from the same snapshot
(exact blob `de1c89486034c2a167d7bb0200360148662091d0`). It has a two-module
Mathlib-only import cone, no source options or placeholders, and compiles at
the immutable pin without adaptation. Its `transportHom` and `autMulHom`
definitions are the Yoneda transport needed to turn the units action on a
future fine `Gamma₁` moduli functor into an action on its representing
scheme. The file is also byte-identical at AINTLIB commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, whose root Apache-2.0 license has
blob `8dada3edaf50dbc082c9a125058f25def75e625a`.

`ProjFromGlobalSectionsMap.lean` is taken from the clean AINTLIB history at
commit `4b93c0d423dd009ecb6f4bb8497bfa3f0df655e5`, exact source blob
`7bab020b5a677bd1d6c6d63c1d28e007158767c0`. Its explicit Chris Birkbeck
Apache-2.0 header is retained. The only exact-pin proof adaptation replaces a
goal-shape `show` by `change` in the final naturality proof; declarations and
statements are unchanged. This leaf supplies the scheme-level naturality of
`Proj.fromOfGlobalSections` under a homogeneous coordinate map.

`GradedQuotient.lean` is retained from AINTLIB exact blob
`4ddeb0cda0187baa7c7f785e9e4ca6cc007625ec`, byte-identical at the licensed
default-branch commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`. Its explicit AINTLIB
contributors Apache-2.0 header is retained. It constructs the grading on the
quotient by a homogeneous ideal, its graded-algebra instance, the degree-zero
base map, and the functorial quotient graded homomorphism. This is the clean
scheme-theoretic prerequisite for forming `Proj (A[X,Y,Z]/(F))`; it contains
no source options or placeholders.

`TateNormalForm.lean` is retained byte-for-byte from AINTLIB exact blob
`6955ff2b550043b1a430433348067ef7b7ec416e`, which is identical at the
licensed default-branch commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`. Its header records the original
Mathlib PR #25218 source by Kenny Lau, branch `kckennylau/tatenf`, commit
`8b7741e0d12ae7a6e8eb998bfbcff29a4f2470c8`, together with the subsequent
AINTLIB additions. The file has only two Mathlib imports and supplies the
Tate coordinate change, uniqueness, and division-polynomial bridges needed by
the fine-`Y₁` route.

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
source is not counted among the twenty-two vendored modules above.

`MazurTorsion/ModularCurve/XZeroGammaOneTateBase.lean` additionally adapts
only the ring-level Tate-normalization and relative affine-base formulas from
AINTLIB `Moduli/Representability.lean` and `ModularCurve/YOneAssembly.lean`.
The required prefix of `Representability.lean` is byte-identical in the
licensed default-branch file, blob
`efd838f8a7702725bcbe974b9e7141e683eee644`; its license basis is that
commit's root Apache-2.0 license blob
`8dada3edaf50dbc082c9a125058f25def75e625a`. `YOneAssembly.lean` has exact
blob `7732e39a206a348ca7c6d59ecdb9b8359abccc33`, byte-identical at the same
licensed commit, and retains an explicit Apache-2.0 file header. The local
leaf also adapts the elementary proper-divisor lemma from that source. It
constructs `Spec R[A,B][Δ⁻¹]` and its Tate equation but deliberately makes no
representability, classifying-map, or modular-curve claim. Its header preserves
the Vasily Ilin and Chris Birkbeck copyrights and credits Kenny Lau, Claude
Fable 5, and Claude Opus 4.8 for the adapted source work.

`MazurTorsion/ModularCurve/XZeroGammaOneTateProjectiveFamily.lean` adapts the
option-free projective-model prefix from AINTLIB
`EllipticCurve/WeierstrassModel.lean`, exact licensed-default blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26`, and the affine-section prefix
from `EllipticCurve/AffinePointSection.lean`, exact blob
`c64a5935d8b886faf3a912447e37a20a6c1fa480`. Both files have explicit Chris
Birkbeck Apache-2.0 headers and occur at the licensed default-branch commit
above. The local extraction replaces the source transparency-option proof of
coordinate-class irrelevance by the direct positive-degree lemma and factors
the two coordinate evaluations through one generic normalized-section
construction. It constructs the actual homogeneous quotient `Proj`, its
projection, and the `[0:1:0]` and `[0:0:1]` sections over arbitrary
commutative bases. It does not port the option-tainted model comparison,
smoothness, base-change, group-law, killed-locus, or representability tails.
The companion `XZeroGammaOneTateProjectiveBaseChange.lean` is new local
categorical work: it forms the chosen pullback along an arbitrary scheme
morphism and pulls back both sections. It does not adapt AINTLIB's stronger
affine coefficient-`Proj` comparison.
`XZeroGammaOneTateProjectiveProper.lean` adapts the subsequent clean
degree-zero/properness prefix of the same `WeierstrassModel.lean` blob. The
generic homogeneous-quotient surjectivity theorem and evaluation at infinity
identify the degree-zero ring with the coefficient ring; Mathlib's properness
of `Proj.toSpecZero` then proves the universal family projection proper.

`ForMathlib/ProjQuotientAway.lean` is a declaration-sliced adaptation of
AINTLIB `ForMathlib/ProjClosedImmersion.lean`, exact blob
`7713fc7254aadc94b713028a74178b0ec439e1f6`. The blob is byte-identical at the
licensed default-branch commit above, whose root Apache-2.0 license has blob
`8dada3edaf50dbc082c9a125058f25def75e625a`. The local leaf retains only the
away-map surjectivity theorem and the principal chart-kernel computation. It
omits the source's option-dependent scheme closed-immersion proof and its
unused projective-chart import, and uses a private copy of the elementary
localization-value ring hom rather than importing that larger chart file.

`ForMathlib/StandardSmoothHypersurface.lean` adapts AINTLIB exact blob
`a1640ea5835d14050eea045a8ce3bacdb0504659`, which has Chris Birkbeck's
explicit Apache-2.0 header and is also byte-identical at the licensed
default-branch commit above. The local blob is
`7349274e42eaddd346b9d1b793b2cbae714a158c`: it removes the source's sole
backward-definitional-equality option, factors the finite relation-to-variable
injectivity proof through an explicitly typed private lemma, and applies only
the pinned linter's mechanical `show`-to-`change` conversions. The localized
hypersurface standard-smooth theorem and its formulas are unchanged.

`ForMathlib/ProjectiveSpaceChart.lean` selectively adapts AINTLIB exact blob
`b987dd389601b36b17803e93e680afde78d6dd51`, byte-identical at the licensed
default-branch commit above and carrying the explicit AINTLIB-contributors
Apache-2.0 header. The local blob is
`0cdf68289e8279b3d021a905b9e8e13565ed9e00`. It retains the dehomogenization,
homogenization, and projective chart ring equivalence, omits independent map
naturality/nonzerodivisor declarations and the resulting `AwayCongr` import,
and applies six mechanical `show`-to-`change` linter conversions.

`XZeroGammaOneTateProjectiveChartCover.lean` adapts the clean coordinate-cover
slice of the licensed `WeierstrassModel.lean` blob recorded above. It proves
that the three degree-one quotient coordinate classes generate the irrelevant
ideal and that their `Proj` basic opens cover the model. It adds no chart-point
dictionary or field-point identification.

`ForMathlib/ProjPrincipalQuotientChart.lean` is a declaration-generalized
adaptation of the principal chart equivalences in the same licensed
`WeierstrassModel.lean` blob.  Its local blob is
`59ca4c8b1c07244727e4db56e649770b13ffd1c9`.  It combines the separately
audited projective-space chart and quotient-away APIs and makes no scheme or
point assertion.  `XZeroGammaOneTateProjectiveChartAlgebra.lean`, local blob
`df98d4fd5733b68c63051e93918364a39546f8f6`, specializes that generic theorem
to a Weierstrass cubic and adapts the source's coefficient-map compatibility
formulas.

`XZeroGammaOneTateProjectiveJacobian.lean`, local blob
`1addf5c465365a2c5dd37805edbebab857aa943e`, selectively adapts the three-chart
Jacobian-comaximality slice of `WeierstrassModel.lean`.  The intermediate
evaluation and singularity formulas are private; its three public theorems
say exactly that the dehomogenized cubic and its two partial derivatives span
the unit ideal on each chart.  `XZeroGammaOneTateProjectiveSmooth.lean`, local
blob `16099929e72b1e7e50dbc55af6f71cb6a252956e`, adapts the subsequent
standard-smooth chart argument.  Instead of the source's two backward-
definitional-equality option wrappers, it installs the precisely typed
ring-hom property instances, normalizes the quotient-coordinate spelling,
and glues directly for the projection to `Spec A`.  It proves relative
dimension one for the generic model, the universal Tate family, and every
arbitrary scheme base change.

`XZeroGammaOneTateProjectiveChartPoints.lean`, local blob
`e662a79fe8bb4bde093ff2539fe8d23d8aa00113`, selectively adapts the first
field-point/chart slice of `WeierstrassModel.lean`.  It reuses the chart
algebra above, proves that every field-valued point factors through a
coordinate chart, and identifies chart points with compatible ring maps and
dehomogenized solutions.  The companion
`XZeroGammaOneTateProjectiveChartTransition.lean`, local blob
`4e5b99a99d61950286c1633e7282ec0c751e287d`, adapts the next overlap slice:
it identifies the coordinate readout `X_j / X_i` and characterizes
factorization through the second chart by its nonvanishing.  The source's
backward-definitional-equality option is replaced by two explicitly typed
basic-open membership lemmas and an explicit quotient-grading-hom
normalization.  These two leaves still stop before the global pointed
field-points dictionary.

`XZeroGammaOneTateProjectivePoints.lean`, local blob
`d2234805dd3cb9fa634fc8221f9e4fd2029bab50`, selectively adapts that global
field-point dictionary from the same licensed `WeierstrassModel.lean` blob.
It constructs the generic infinity section `[0:1:0]`, proves it is the unique
point outside the `Z`-chart, and gives an explicit pointed equivalence between
scheme-valued field points and Mathlib's affine Weierstrass points.  The local
proof reuses the separately checked chart equivalences and overlap criterion;
it omits the source's choice-normalized wrapper, group-law compatibility, and
`Over` equivalence.

`ForMathlib/WeierstrassSecondAdditionLaw.lean`, local blob
`4b24e35e355735bb0afb20b2b056db258506d061`, selectively adapts the second
Bosma--Lenstra bidegree-`(2,2)` addition law from AINTLIB
`EllipticCurve/AdditionLaw.lean`, exact source blob
`c6ea88db42629fd166902494bb5617d4511e309b`.  The source has Chris
Birkbeck's explicit Apache-2.0 header and occurs at the licensed default
commit above.  The local algebraic leaf retains the three coordinate
polynomials, their bihomogeneity, their six zero-left/zero-right formulas,
and their four diagonal identities.  It does not by itself assert coverage,
construct a morphism, or install a group object.

`ForMathlib/WeierstrassSecondAdditionCoverage.lean`, local blob
`896d90689047adfd003294843bbf96dd7470a00d`, is the next declaration slice.
It combines the three exact cross-minor certificates from the same
`AdditionLaw.lean` blob with the field proportionality/coverage proofs from
`AdditionLawField.lean`, exact blob
`2d2dedf5639d707f9dda0a0e26a25a123b842c0d`, and the minimum first-law
on-curve/scaling slice from `AdditionLawOnCurve.lean`, exact blob
`6cdd1aa98921c9fbf607b855e3243de316fdca6d`.  All three source blobs occur at
the licensed default commit and carry the recorded AINTLIB Apache-2.0
attribution.  The public endpoint proves that both triples lie on an elliptic
curve and cannot vanish simultaneously over field-valued nonsingular inputs;
it still makes no scheme-morphism or group-object claim.

`ForMathlib/WeierstrassAdditionJacobson.lean`, local blob
`8dccefe9964b42907718d5a4ff166654dd750cc8`, selectively adapts the
reduced-Jacobson promotion from the same `AdditionLawOnCurve.lean` blob.  Its
private radical/Jacobson vanishing helper comes from the `AdditionLaw.lean`
blob recorded above.  Both sources occur at the licensed default commit and
carry the recorded Apache-2.0 attribution.  Exactly two declarations are
exported: each Bosma--Lenstra triple satisfies the curve equation over a
reduced Jacobson ring with invertible discriminant.  The leaf does not define
addition charts, prove that their coordinate rings are reduced or Jacobson,
or construct a global group law.

`ForMathlib/AffineGeometricOrbit.lean`, local blob
`ceb746d32b33fb751c59a9950b9e7517a5033c1b`, is a one-declaration slice of
AINTLIB `Moduli/GammaHRepresentability.lean`, exact source blob
`dcd6e523ba797116398a1566ffa596f0e412e8e8` at the licensed default commit.
Its explicit AINTLIB-contributors Apache-2.0 header is retained.  The theorem
says that two algebra maps to an algebraically closed field which agree on
all invariants differ by the finite group action.  No `GammaH` moduli cone,
option wrapper, or conditional representability theorem is imported.

The retained exact-sequence core and exact additive-sheaf forgetful functor
are consumed by
`MazurTorsion.Upstream.SchemeModuleCohomologyDimensionShift`. That module
proves the injective long-exact-sequence step for the actual affine-cover
short exact sequence. It does not import AINTLIB's full affine-vanishing
proof: the local-killing and cokernel-vanishing argument remains a separate
checked dependency.

The larger relative-Picard cone was tested but not retained: at this pin its
essential elaboration depends on source-level backward-compatibility options,
which this repository forbids. `MuN.lean` was also not copied because the
audited file lacks an explicit license header. Files with placeholders or an
unclean transitive cone remain prior art only. This is why AINTLIB is a
selective attributed port rather than a Lake dependency.

`MazurTorsion.Upstream.Geometry` is the reviewed boundary for the Picard and
Cartier-duality ports;
`MazurTorsion.Upstream.SchemeModuleCohomologyDimensionShift` is the boundary
for the two sheaf-cohomology ports. `MazurTorsion.lean` is their named checked
consumer. The geometry boundary also imports Tau Ceti's line-bundle and
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
