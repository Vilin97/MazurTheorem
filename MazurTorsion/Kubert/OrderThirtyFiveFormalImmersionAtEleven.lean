/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionSpecialFiber
import MazurTorsion.AlgebraicGeometry.FormalImmersionCollision
import MazurTorsion.Kubert.OrderThirtyFiveGoodReductionAtEleven

/-!
# The order-35 formal-immersion collision at eleven

This file is the local theorem-level consumer for the squarefree level-35
route.  A quotient-cotangent calculation on the actual characteristic-eleven
cusp stalk lifts to a formal immersion of total completed stalks.  If the
modular section specializes to that cusp and its image in the finite
rank-zero quotient equals the cusp image, the collision forces the original
rational `j`-invariant to be eleven-adically integral.

The final theorem sends this valuation bound through the selected minimal
eleven-adic equation, canonical nonsingular reduction, good-reduction
specialization, and the checked `F_11` enumeration.  The remaining explicit
premises are precisely the modular/cusp geometry, quotient specialization,
special-cubic classification, and component bound.
-/

noncomputable section

namespace MazurTorsion.OrderThirtyFive

open CategoryTheory
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open _root_.AlgebraicGeometry

local instance : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The closed-fibre point selected by an eleven-adic integral section. -/
abbrev closedFiberPointAtEleven {X : Scheme}
    (s : Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X) : X :=
  s (IsLocalRing.closedPoint (atEleven.adicCompletionIntegers ℚ))

/-- The actual cusp-stalk quotient-cotangent certificate supplies the
eleven-adic `j`-valuation bound through the formal-immersion collision. -/
theorem valuation_j_le_one_of_quotientCotangentCertificateAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (data : IsLocalRing.QuotientCotangentCertificate
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atEleven.valuation ℚ E.j ≤ 1 := by
  by_contra hj
  apply hne
  have hpoint := hspecializes hj
  have hformal : IsFormalImmersionAt f
      (closedFiberPointAtEleven cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_quotientCotangentCertificate_of_isLocallyNoetherian
      f (closedFiberPointAtEleven cuspSection) hresidue data
  have hformalAtModular : IsFormalImmersionAt f
      (closedFiberPointAtEleven modularSection) := by
    simpa only [hpoint] using hformal
  exact hformalAtModular.spec_ext_of_comp_eq_of_isNoetherian
    modularSection cuspSection hpoint (hquotient hj)

/-- The level-35 special-fibre cotangent calculation reaches the rational
order-35 exclusion through the canonical nonsingular-reduction endpoint at
eleven. -/
theorem
    rationalPoint_addOrderOf_ne_thirtyFive_of_quotientCotangentAtEleven_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (data : IsLocalRing.QuotientCotangentCertificate
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (hadd : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        NonsingularReductionIsAdditive
          (minimalCompletionIntegralModelAtEleven_map E))
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ hA,
      Nat.card ((minimalCompletionAtEleven E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E) (hadd hA)) ≤ 4)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  rationalPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_nonsingularReductionAtEleven
    (valuation_j_le_one_of_quotientCotangentCertificateAtEleven
      f modularSection cuspSection hresidue data hne hspecializes hquotient)
    hadd especial hcomponent P

end MazurTorsion.OrderThirtyFive
