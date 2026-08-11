/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Challenge: the divisor-line-bundle dictionary on a smooth proper curve

This contract captures the remaining A3 existence and equivalence deliverable: a scheme-level
dictionary relating chosen invertible-sheaf representatives, the Picard group, and Weil divisor
classes. The affine tilde restriction isomorphism and global tilde invertibility are now proved
in checked code. A checked equivalence reduces existence of the dictionary to the full Picard
comparison together with a divisor-class/Picard equivalence; chosen line bundles and their
compatibilities are constructed from those data. The contract does not prescribe a canonical
affine-chart normalization. On affine schemes, the localized tensor maps have now been assembled
into an objectwise tilde tensor-product isomorphism. This gives a canonical injective
module-Picard to scheme-Picard map. For affine Dedekind domains, the divisor map has exactly the
principal divisors as kernel, divisor classes are equivalent to its range, and the chosen tilde
line bundles are tensor-additive. The chosen Picard representative is now identified with the
explicit inverse fractional ideal attached to the divisor. Relative to these fixed comparisons,
multiplication of explicit inverse ideals now determines named tensor/addition equivalences for
the chosen affine modules, with a checked pure-tensor formula in the fraction field. Tilde
transports this to `AffineDivisorLocalization.ExplicitIdeal.lineBundleAddIso`, and the named
chartwise consumer `CurveDivisorDescent.localLineBundleAddIso` identifies `O(D + E)` with
`O(D) ⊗ O(E)` on every compatible affine chart. At the raw common-extension level,
`CommonExtension.extendedInverseIdealTensorAddEquiv` and its `_tmul` theorem identify tensor
addition with multiplication in the common fraction field. The `_baseChange_tmul` and
`_baseChange` theorems prove that multiplication-direction equivalence commutes with a further
flat epimorphic scalar extension through `AlgebraTensorModule.distribBaseChange`. The fixed
chosen-module comparison is now exposed by
`CommonExtension.lineBundleModuleBaseChangeEquivExtendedInverseIdeal` and its `_tmul` theorem,
and `lineBundleModuleTensorAddEquiv_baseChange` proves the corresponding tensor-to-sum square.
The genuine curve consumer
`CurveDivisorDescent.localLineBundleModuleTensorAddEquiv_baseChangeOnCommonAffineOpen` derives
the restriction algebra, flat-epimorphism, fraction-field, and scalar-tower data for one canonical
affine restriction leg. Thus the fixed chosen-module tensor-to-sum map is natural on that raw
module-level leg. The generic
`Scheme.Modules.tildePullbackIsoExtendScalars` comparison identifies affine pullback of a tilde
module with tilde of its extension of scalars. At the common-extension level,
`extendedInverseIdealAddIso` lifts raw inverse-ideal addition through tilde, while
`lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars` and
`lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars` give the direct comparisons
from the pulled-back fixed bundle and pulled-back fixed tensor to the corresponding raw
extended-ideal tilde sheaves. The theorem `lineBundleAddIso_pullback_viaExtendScalars` proves the
resulting deterministic sum-to-tensor square, and
`CurveDivisorDescent.localLineBundleAddIso_pullbackViaExtendScalarsOnCommonAffineOpen`
specializes it to one genuine affine restriction leg.
`CommonExtension.restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq_viaExtendScalars`
identifies the legacy single-factor restriction mate with the restriction-to-pullback
comparison followed by `ViaExtendScalars`, and
`CurveDivisorDescent.localRestrictionIsoExtendedInverseIdeal_eq_viaExtendScalarsOnCommonAffineOpen`
is its genuine affine-open consumer. The project-original
`Scheme.Modules.tildePullbackGenerator` API exposes the top-section pullback generator, identifies
it with the transported pullback-unit section, and evaluates the affine tilde/base-change
comparison on it. Naturality of the affine tilde tensor comparison is checked in both hom and
inverse orientations, and its top-section evaluator computes pure tensor sections. Together with
`ModularCurves.pullback_δ_unit_tensorSection`, these formulas prove the generic
`AffineTilde.tildePullbackIsoExtendScalars_tensor_hom` base-change square. The comparison
`CommonExtension.lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator`
factors through that canonical cotensorator and the two factorwise scalar-extension
comparisons. The direct comparison has the same hom, hence is the same isomorphism, and the
genuine curve specialization proves this equality on one fixed common-affine restriction leg.
Transporting the inverse pullback tensorator through the legacy restriction-to-pullback
comparison gives `CommonExtension.lineBundleTensorRestrictionIsoViaPullback`. The theorem
`CommonExtension.lineBundleAddIso_restrict_viaPullback` proves the deterministic tensor/addition
square for the legacy restriction comparisons, and
`CurveDivisorDescent.localLineBundleAddIso_restrictViaPullbackOnCommonAffineOpen` is its genuine
curve specialization on that same fixed leg. Equality-induced multiplication of raw extended
inverse-ideal tilde sheaves is now natural across two chart rings:
`Boundary.overlapInverseIdealExtensionEq_add` derives the comparison for a divisor sum,
`CommonExtension.extendedInverseIdealAddIso_naturality` proves the resulting sum-to-tensor
square, and
`CurveDivisorDescent.localExtendedInverseIdealAddIso_naturalityViaPairwiseIntersection` is the
proper-smooth curve consumer whose factorwise equalities come through the pairwise intersection.
The chosen coordinate-divisor restriction comparisons now satisfy the corresponding cross-chart
tensor/addition square: `CommonExtension.lineBundleAddIso_restrict_viaPullback_naturality`
proves the generic square, and
`CurveDivisorDescent.localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection`
is its proper-smooth pairwise-intersection consumer. The named transports
`CurveDivisorDescent.localLineBundleCoordinateIso` and
`CurveDivisorDescent.localLineBundleAddSourceCoordinateIso` expose the proof-defined global-divisor
bundles in those coordinate presentations, and
`CurveDivisorDescent.localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection_global`
aligns the square with the actual proof-defined local addition maps and pairwise-intersection
transitions. The definition
`CurveDivisorDescent.localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve`
transports the whole pairwise-intersection tensor model to Mathlib's chosen pullback, and
`CurveDivisorDescent.localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel` proves
that the proof-defined local addition maps commute there with this whole transported tensor
transition and the raw sum transition. Conditional on an already supplied divisor cocycle `CDE`
for `D + E`, `CurveDivisorDescent.localLineBundleTransportedTensorModelDescentData` constructs the
full `changeObjects` target on the chartwise tensor objects, and
`CurveDivisorDescent.localLineBundleAddDescentDataIsoViaTransportedTensorModel` gives its full
`DescentData` isomorphism with the source sum cocycle. The theorem
`CurveDivisorDescent.localLineBundleTransportedTensorModelEffective_of_sumCocycleEffective`
transfers an already supplied effectivity witness, while
`CurveDivisorDescent.localLineBundleTransportedTensorModelDescentData_hom_on_chosenOverlap`
identifies the chosen transition with the whole transported tensor model under exact per-overlap
alignment of `CDE`'s Homs with the raw sum family. Separately, strong monoidality of pullback
composition is now checked first for presheaves of modules and then for scheme modules.
`LineBundleDescent.pullbackOverlapIsoOfModel_tensor` identifies transport of a tensor transition
through the exact-pseudofunctor comparison with the cotensorator-conjugated tensor of the two
factor transports. The curve-level theorem
`CurveDivisorDescent.localLineBundleTensorChosenOverlapIsoOfPairwiseModel_eq_tensorRawOverlapIsoFamily`
specializes this to the two raw divisor transitions, and
`CurveDivisorDescent.localLineBundleAddIso_chosenOverlap_commViaFactorwiseRawTensor` proves the
resulting local-add Hom square. The conditional consumers still do not construct the required raw
arbitrary-divisor cocycle or prove unconditional effectivity. Packaging the full factorwise
descent-data morphism and constructing a `CurveDivisorDescent.DescendedTensorAdditive` witness
remain open. On a same-chart principal open,
equality of divisor coefficients proves equality of the localized inverse ideals, equivalently
equality after common-field extension, and constructs an isomorphism of the chosen restricted
tilde bundles. Meanwhile,
`AffineDivisorLocalization.Boundary.OverlapInverseIdealExtensionEq` isolates cross-chart
ideal-extension equality and
`AffineDivisorLocalization.CommonExtension.RestrictionIdentifiesExtendedInverseIdeal` isolates
the restriction/base-change identification. Affine tilde base change and flat epimorphic
tensor/span comparison now prove the latter for every affine open immersion, without a classical
localization presentation. Hence the packaged cross-chart extension condition, which also
records the scalar towers, constructs the actual chosen restriction isomorphism. For two distinct
chart rings, extension equality is proved for the principal divisors defined by the same rational
function, giving the actual restriction isomorphism on every common affine overlap satisfying the
standing Dedekind and common-fraction-field assumptions. For arbitrary divisors, open-immersion
prime extension proves extended-ideal equality from contracted coefficient equality on any
common Dedekind affine overlap; the classical-localization theorem is now only a specialization.
For restrictions of one ambient divisor, equality of the two coordinate maps to the curve makes
the contracted ambient points, coefficients, extended ideals, and actual chosen restrictions
agree automatically. The resulting checked consumer is
`CurveDivisorDescent.localLineBundleRestrictionIsoOfCommonMap`. More concretely,
`localLineBundleRestrictionIsoOnCommonAffineOpen` derives every algebraic and geometric input
canonically from a chosen common nonempty Dedekind affine subopen. Under separatedness,
`localLineBundleRestrictionIsoOnIntersection` specializes this to the full intersection of two
nonempty affine charts, conditional only on its coordinate ring being Dedekind. For the intended
proper curve over a field, `localLineBundleRestrictionIsoOnProperCurveIntersection` derives the
separatedness input from properness. With smooth relative dimension one,
`localLineBundleRestrictionIsoOnProperSmoothCurveIntersectionOfNormality` further replaces the
intersection Dedekind hypothesis by exactly the existing mapwise normality contract. Canonical
Picard surjectivity is proved
equivalent to the reverse tensor-unit/local-rank-one comparison, while the forward affine gap is
isolated as the checked localization predicate `AffineTilde.TildeReflectsInvertibility`.
The chart API identifies height-one primes with ambient codimension-one points and proves order
compatibility automatically from a Dedekind-domain instance. Over a field, locally
standard-smooth relative dimension one now proves both dimension at most one and integral
closedness; `AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve` is the unconditional
consumer for the intended charts. The historical
`AffineChart.SmoothRelativeCurveRingConditions` and
`AffineChart.SmoothRelativeCurveNormality` predicates remain compatibility wrappers, not open
field-base hypotheses. The local divisor-to-Picard map has exactly the principal divisors as
kernel, descends injectively to chart divisor classes, and identifies them with its scheme-Picard
range. `AffineTilde.tildeReflectsInvertibility` now discharges the former affine localization
predicate and supplies the forward tensor-inverse comparison. The remaining A3 boundary begins
with packaging the checked raw arbitrary-divisor overlap family as the required
`DivisorCocycle`, selecting or supplying a universe-zero nonempty affine coordinate cover, and
applying ordinary module effectivity to that concrete datum. The remaining boundary for
descending the fixed chartwise addition maps now has the full transported tensor-object descent
datum, its `DescentData` isomorphism with an already supplied sum cocycle, conditional transfer of
effectivity, and its chosen transition under raw-Hom alignment. Strong monoidality of pullback
composition, factorwise chosen-overlap tensor coherence, and the resulting local-add Hom square
are checked. Constructing the required raw cocycle, assembling the full factorwise descent-data
morphism, proving effectivity without a supplied sum-cocycle witness, and constructing a
`CurveDivisorDescent.DescendedTensorAdditive` witness remain open.
Principal coherence, object
separation, rational normalization and principal detection, exactness, Picard surjectivity, and
the stronger global comparison for arbitrary invertible sheaves also remain.
The
residue-degree product formula remains the separately registered A2 prerequisite in the roadmap;
the affine and local A3 modules here do not import it.
The companion module `CurveAffineChart` isolates the upstream-compatible sufficient input
`PicardIso.PullbackMonoidalData`: given strong monoidality of sheaf pullback, checked code
transports the divisor and class maps to `Pic(U)` while preserving the exact principal kernel
and range equivalence. The option-free selective AINTLIB pullback-monoidal cone and its
tensor-section evaluator now enter the A3 route through a separate companion module; the
Challenge itself does not import that larger cone. For gluing, the separately importable modules
`AffineDivisorLocalization`, `CurveLineBundleDescent`, `CurveLineBundleLocality`,
`CurveDivisorDescent`, `CurveDivisorPicardDescent`, `CurveLineBundleCompatibleFamilies`,
and `CurveLineBundleCocycleForcesNormalization` construct the actual affine `O(D)` on a coordinate
cover and prove that every principal divisor gives a trivial line bundle on each chart.
Same-chart coefficient agreement on a principal open constructs the actual restriction
isomorphism between the corresponding chartwise divisor bundles. The raw arbitrary-divisor
overlap family satisfies the pointwise all-index cocycle, including repeated indices. The generic
`normalization_of_iso_cocycle` theorem derives its diagonal identity, and the derived
`LineBundleCocycle.normalization` theorem is its concrete structure-level consumer.
`LineBundleCocycle` stores exact-pseudofunctor-map overlap isomorphisms and the pointwise all-index
cocycle; it has no independent normalization field. Packaging the raw divisor family as this
structure and then as `CurveDivisorDescent.DivisorCocycle` remains open. Locality of Tau Ceti
invertibility is proved for arbitrary scheme open covers, and ordinary module effectivity is
proved for every `OpenCover.{0}`, but neither theorem has yet been applied to a concrete
arbitrary-divisor cocycle system.
A prestack instance for the scheme-module pseudofunctor now has a checked consumer producing
fully faithful descent and hence object separation, but no such instance is currently available.
For a divisor-indexed cocycle family, objectwise effectivity, tensor-additivity, and triviality
of the zero-divisor bundle construct an actual divisor-to-Picard homomorphism: the bundle for
`-D` is an explicit inverse to the bundle for `D`. Coherent triviality of the principal cocycles
supplies zero triviality and descends this map to divisor classes under object separation. Exact
principal kernel is equivalent, under coherent principal triviality and object separation, to
`ExplicitInverse.TrivialLineBundleDetectsPrincipal`: only principal divisors have globally
trivial descended line bundle. A global trivialization is proved to make the divisor principal
on every chart. The witness-level condition
`TrivialDescendedLineBundleHasGlobalPrincipalWitness` says that one rational function gives all
chart restrictions; under agreement of the chosen global and scheme orders, checked code proves
this condition equivalent to principal detection in both directions. It is therefore not an
additional gluing hypothesis. Constructing compatible rational data from the explicit
line-bundle cocycle remains absent. Exactness gives an equivalence with the actual Picard range,
and
adding surjectivity gives the full divisor-class/Picard equivalence without a global
tensor-inverse comparison. Such a comparison is still required only by the stronger
`DivisorPicard.Dictionary`, which records the class of every invertible sheaf. Chosen-pullback
transport and the raw all-index overlap equation are checked. Conditional on an already supplied
sum cocycle, the full transported tensor-object descent datum, its change-of-objects
`DescentData` isomorphism, transfer of a supplied effectivity witness, and chosen-transition
identification under raw-Hom alignment are also checked. Strong monoidality of pullback
composition now identifies the whole transported transition with the cotensorator-conjugated
tensor of the two separately transported raw factor transitions, and the corresponding local-add
Hom square is checked. No arbitrary-divisor `DivisorCocycle` or divisor cocycle system, concrete
Type-0 effectivity application, global divisor-line-bundle family, unconditional effectivity,
full factorwise descent-data morphism,
`CurveDivisorDescent.DescendedTensorAdditive` witness, coherent principal triviality,
prestack/object-separation, rationally normalized cocycle data, geometric principal detection,
exact kernel, Picard surjectivity, or global tensor-inverse comparison is asserted. No additional
localization Challenge is needed; the weighted product formula remains the separate A2
prerequisite. These remaining packaging, global compatibility, and equivalence results are open,
so the contract earns no Mazur completion credit.
The Challenge's published import list remains unchanged; solvers use these checked route
modules explicitly.
-/

open AlgebraicGeometry
open MazurTorsion.AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- Construct an exact divisor-line-bundle dictionary for the geometric order system on a
smooth proper curve. -/
theorem divisorLineBundleDictionary
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    Nonempty (MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary S X) := sorry

/-- The two irreducible global outputs extracted from the dictionary contract. Checked code
proves conversely that these data construct all chosen divisor line bundles and dictionary
compatibilities. -/
theorem divisorPicardCoreData
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    PicardComparison X ∧ Nonempty (DivisorPicard.ClassEquivalence S X) := by
  apply DivisorPicard.Dictionary.nonempty_iff_picardComparison_and_classEquivalence.mp
  exact divisorLineBundleDictionary K X π S hord

/-- The divisor-class/Picard equivalence extracted from the exact dictionary. This is an
acceptance consumer for `divisorLineBundleDictionary`. -/
noncomputable def divisorClassEquivPicard
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    S.ClassGroup ≃+ MazurTorsion.AlgebraicGeometry.PicardGroup X :=
  (divisorPicardCoreData K X π S hord).2.some

end MazurTheorem.Challenge
