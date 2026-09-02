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
explicit inverse fractional ideal attached to the divisor. On a same-chart principal open,
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
from presheaf restriction on a chosen common nonempty Dedekind affine subopen. Under separatedness,
`localLineBundleRestrictionIsoOnIntersection` specializes this to the full intersection of two
nonempty affine charts, conditional only on its coordinate ring being Dedekind. For the intended
proper curve over a field, `localLineBundleRestrictionIsoOnProperCurveIntersection` derives the
separatedness input from properness. With smooth relative dimension one,
`localLineBundleRestrictionIsoOnProperSmoothCurveIntersection` further replaces the intersection
Dedekind hypothesis unconditionally.
`localLineBundlePullbackIsoOnIntersection` transports that isomorphism across the categorical
pullback/intersection comparison, and `coordinateDivisorOverlapIso` lands in the exact chosen
pairwise-overlap objects used by the descent package.
`coordinateDivisorOverlapIso_normalization` proves the exact diagonal normalization required by
the descent package. Canonical Picard surjectivity is proved
equivalent to the reverse tensor-unit/local-rank-one comparison, while the forward affine gap is
isolated as the checked localization predicate `AffineTilde.TildeReflectsInvertibility`.
What remains here includes proving the base-change law and triple-cocycle coherence for the chosen
pairwise maps, the affine Picard comparison inputs, global curve divisor gluing, and global
divisor-class/Picard surjectivity. The
chart API already identifies height-one primes with
ambient codimension-one points and now proves the order compatibility automatically from a
Dedekind-domain instance; that remaining algebraic condition is exactly dimension at most one
plus integral closedness. `AffineChart.SmoothRelativeCurveRingConditions` is a map-parameterized
predicate packaging those two consequences. Over a field, locally standard-smooth relative
dimension one is now proved to imply both consequences: an étale-domain integral-closure theorem
and localization descent supply normality, while the checked prime-chain argument supplies the
dimension bound. `AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve` therefore
constructs the required order compatibility on every nonempty affine chart without an extra
hypothesis. No universal smooth-over-arbitrary-base implication is asserted. The local
divisor-to-Picard
map has exactly the principal divisors as kernel, descends injectively to chart divisor classes,
and identifies them with its scheme-Picard range. `AffineTilde.TildeReflectsInvertibility` is a
checked conditional interface, not a solved
existence result or separately registered Challenge declaration; discharging it remains part of
this unchanged global A3 Challenge. The
residue-degree product formula remains the separately registered A2 prerequisite in the roadmap;
the affine and local A3 modules here do not import it.
The companion module `CurveAffineChart` isolates the upstream-compatible sufficient input
`PicardIso.PullbackMonoidalData`: given strong monoidality of sheaf pullback, checked code
transports the divisor and class maps to `Pic(U)` while preserving the exact principal kernel
and range equivalence. The pinned upstream AINTLIB source proves general pullback monoidality,
but that cone is not in the current checked import graph and cannot be copied here under this
task's no-`set_option` constraint. For gluing, the separately importable companion modules
`AffineDivisorLocalization`, `CurveLineBundleDescent`, `CurveLineBundleLocality`,
`CurveDivisorDescent`, and `CurveDivisorPicardDescent` construct the actual affine `O(D)` on a
canonical coordinate cover and prove that every principal divisor gives a trivial line bundle
on each chart. Same-chart coefficient agreement on a principal open now constructs the actual
restriction isomorphism between the corresponding chartwise divisor bundles.
`CurveDivisorDescent.DivisorCocycle` is the exact remaining triple-coherent completion of the
now-constructed normalized pairwise maps for those specified bundles. Given such a cocycle,
checked code converts it to Mathlib descent data and, under object-specific
`LineBundleDescent.EffectiveInvertible`, constructs a global line bundle whose restriction is
the chosen affine `O(D)`. Locality of Tau Ceti invertibility is now proved for arbitrary scheme
open covers, so ordinary module effectivity alone upgrades locally invertible descent data to
effective global line bundles.
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
`DivisorPicard.Dictionary`, which records the class of every invertible sheaf. No inhabitant of
the required divisor cocycle system,
coherent overlap system,
module-effectivity, coherent-principal-triviality,
prestack/object-separation, rationally normalized cocycle data,
geometric-principal-detection, exact-kernel, surjectivity, or global tensor-inverse comparison is
asserted. `AffineTilde.TildeReflectsInvertibility` and the cover-wide
`CurveDivisorDescent.DivisorCocycle` and effectivity packages are
precise compiled conditional contracts subsumed by this unchanged registered A3 Challenge,
rather than separately registered open theorems. No additional localization Challenge is needed;
the weighted product formula remains the separate A2 prerequisite. These existence results remain
open, so the contract earns no Mazur completion credit.
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
