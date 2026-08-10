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
`O(D) ⊗ O(E)` on every compatible affine chart. Naturality of these maps under chart
restriction or overlap base change is not claimed. On a same-chart principal open,
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
applying ordinary module effectivity to that concrete datum. Restriction/overlap base-change
naturality of the fixed chartwise addition maps needed to descend those maps remains open, and no
`CurveDivisorDescent.DescendedTensorAdditive` witness is supplied. Principal coherence, object
separation, rational normalization and principal detection, exactness, Picard surjectivity, and
the stronger global comparison for arbitrary invertible sheaves also remain.
The
residue-degree product formula remains the separately registered A2 prerequisite in the roadmap;
the affine and local A3 modules here do not import it.
The companion module `CurveAffineChart` isolates the upstream-compatible sufficient input
`PicardIso.PullbackMonoidalData`: given strong monoidality of sheaf pullback, checked code
transports the divisor and class maps to `Pic(U)` while preserving the exact principal kernel
and range equivalence. The pinned upstream AINTLIB source proves general pullback monoidality,
but that cone is not in the current checked import graph and cannot be copied here under this
task's no-`set_option` constraint. For gluing, the separately importable companion modules
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
transport and the raw all-index overlap equation are checked, but no arbitrary-divisor
`DivisorCocycle` or divisor cocycle system, concrete Type-0 effectivity application, global
divisor-line-bundle family, overlap-compatible global tensor-additivity (in particular, no
`CurveDivisorDescent.DescendedTensorAdditive` witness), coherent principal triviality,
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
