/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFiniteField
import MazurTorsion.PrimeOrder.TorsionSpecialization

/-!
# Rational points of order thirty-five

This module reserves the permanent library destination for the order-35
challenge. A solution belongs here; the published challenge module can then
become a thin, immutable bridge to that theorem.
-/

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurTorsion.IntegerPrimeSpecialization

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The checked `F_11` enumeration rules out a specialized point of exact
order 35.  The remaining rational theorem must construct this point through
the squarefree-level formal-immersion and Néron-specialization route. -/
theorem reductionAtEleven_addOrderOf_ne_thirtyFive
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  intro hP
  have hdvd : addOrderOf P ∣ Nat.card W.toAffine.Point :=
    addOrderOf_dvd_natCard P
  have hle : addOrderOf P ≤ 18 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans
      (card_reductionAtEleven_le_eighteen W)
  omega

/-- If an integral model has good reduction at eleven, a rational point on
its generic fibre cannot have exact order 35.  This is the checked join
between unramified specialization and the exhaustive `F_11` certificate. -/
theorem rationalPoint_addOrderOf_ne_thirtyFive_of_goodReductionAtEleven
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    {P : E.Point} :
    addOrderOf P ≠ 35 := by
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    norm_num)
  letI : (MazurTorsion.PrimeOrder.reductionCurveAtEleven W₀).IsElliptic :=
    MazurTorsion.PrimeOrder.reductionCurveAtEleven_isElliptic W₀
  apply reductionAtEleven_addOrderOf_ne_thirtyFive
    (MazurTorsion.PrimeOrder.reductionCurveAtEleven W₀)
    (MazurTorsion.PrimeOrder.reductionAtElevenToZMod hE P)
  exact
    (MazurTorsion.PrimeOrder.specializedPointZMod_addOrderOf_eq_atEleven_of_goodReduction
      hE hP).trans horder

end MazurTorsion.OrderThirtyFive
