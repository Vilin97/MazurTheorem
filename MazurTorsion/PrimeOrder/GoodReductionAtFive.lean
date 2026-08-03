/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.PrimeOrder.FiniteFieldFiveOrder
import MazurTorsion.PrimeOrder.TorsionSpecialization

/-!
# The prime-order contradiction after good reduction at five

This module joins the unramified formal-kernel specialization theorem to the
checked enumeration of elliptic curves over `F_5`.  It is the downstream
consumer required by the formal-immersion route once the preceding local
argument has supplied an integral model with good reduction at five.
-/

open WeierstrassCurve

namespace MazurTorsion.PrimeOrder

open WeierstrassCurve.Affine
open MazurTorsion.IntegerPrimeSpecialization

/-- If an integral model has good reduction at five, none of its rational
torsion points has exact order at least eleven. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_goodReductionAtFive
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    {P : E.Point} {N : ℕ} (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    omega)
  letI : (reductionCurveAtFive W₀).IsElliptic := reductionCurveAtFive_isElliptic W₀
  apply zmod_five_addOrderOf_ne_of_eleven_le
    (reductionCurveAtFive W₀) (reductionAtFiveToZMod hE P) N hN
  exact (specializedPointZMod_addOrderOf_eq_atFive_of_goodReduction hE hP).trans horder

end MazurTorsion.PrimeOrder
