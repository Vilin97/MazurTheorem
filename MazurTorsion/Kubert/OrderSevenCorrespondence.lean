/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The level-seven modular correspondence polynomial

This file exposes the symmetric bidegree-`(7,7)` polynomial used by the
`X₀(49)` transfer.  Its factorization as the off-diagonal part of the
cross-multiplied level-seven `j`-identity gives the eventual order-`49` tower
an algebraic interface independent of the private transfer certificates.

Only the checked polynomial interface and its elementary boundary behaviour
are recorded here.  The quotient family and the identification with the
modular correspondence remain separate steps.
-/

namespace MazurTorsion.Kubert

/-- The numerator in the level-seven Hauptmodul formula
`j(t) = J₇(t) / t⁷`. -/
def orderSevenJNumerator (t : ℚ) : ℚ :=
  (t ^ 2 + 13 * t + 49) * (t ^ 2 + 245 * t + 2401) ^ 3

/-- The Fricke-twisted level-seven correspondence polynomial. -/
def orderSevenG7F (s B : ℚ) : ℚ :=
  -678223072849 * B ^ 6 - 678223072849 * s * B ^ 5 - 387556041628 * s * B ^ 6
  - 678223072849 * s ^ 2 * B ^ 4 - 387556041628 * s ^ 2 * B ^ 5 - 90957030178 * s ^ 2 * B ^ 6
  - 678223072849 * s ^ 3 * B ^ 3 - 387556041628 * s ^ 3 * B ^ 4 - 90957030178 * s ^ 3 * B ^ 5
  - 10976181104 * s ^ 3 * B ^ 6 - 678223072849 * s ^ 4 * B ^ 2 - 387556041628 * s ^ 4 * B ^ 3
  - 90957030178 * s ^ 4 * B ^ 4 - 10976181104 * s ^ 4 * B ^ 5 - 695893835 * s ^ 4 * B ^ 6
  - 678223072849 * s ^ 5 * B - 387556041628 * s ^ 5 * B ^ 2 - 90957030178 * s ^ 5 * B ^ 3
  - 10976181104 * s ^ 5 * B ^ 4 - 695893835 * s ^ 5 * B ^ 5 - 20706224 * s ^ 5 * B ^ 6
  - 678223072849 * s ^ 6 - 387556041628 * s ^ 6 * B - 90957030178 * s ^ 6 * B ^ 2
  - 10976181104 * s ^ 6 * B ^ 3 - 695893835 * s ^ 6 * B ^ 4 - 20706224 * s ^ 6 * B ^ 5
  - 196882 * s ^ 6 * B ^ 6 + s ^ 7 * B ^ 7

/-- The level-seven correspondence is symmetric in its two legs. -/
theorem orderSevenG7F_comm (s B : ℚ) :
    orderSevenG7F s B = orderSevenG7F B s := by
  simp only [orderSevenG7F]
  ring

/-- The cross-multiplied equality of the two level-seven `j`-values factors
as the diagonal times the correspondence polynomial. -/
theorem orderSevenJNumerator_crossDifference (s B : ℚ) :
    orderSevenJNumerator s * B ^ 7 - orderSevenJNumerator B * s ^ 7 =
      (s - B) * orderSevenG7F s B := by
  simp only [orderSevenJNumerator, orderSevenG7F]
  ring

/-- Off the diagonal, equality of the cross-multiplied level-seven
`j`-values is exactly the correspondence equation. -/
theorem orderSevenG7F_eq_zero_iff_crossMultiply
    {s B : ℚ} (hsB : s ≠ B) :
    orderSevenG7F s B = 0 ↔
      orderSevenJNumerator s * B ^ 7 =
        orderSevenJNumerator B * s ^ 7 := by
  constructor
  · intro hG
    apply sub_eq_zero.mp
    rw [orderSevenJNumerator_crossDifference, hG, mul_zero]
  · intro hJ
    have hprod : (s - B) * orderSevenG7F s B = 0 := by
      rw [← orderSevenJNumerator_crossDifference]
      exact sub_eq_zero.mpr hJ
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hsB)

/-- On the left boundary, the correspondence polynomial is a nonzero
constant times the sixth power of the other coordinate. -/
@[simp]
theorem orderSevenG7F_zero_left (B : ℚ) :
    orderSevenG7F 0 B = -678223072849 * B ^ 6 := by
  simp [orderSevenG7F]

/-- On the right boundary, the correspondence polynomial is a nonzero
constant times the sixth power of the other coordinate. -/
@[simp]
theorem orderSevenG7F_zero_right (s : ℚ) :
    orderSevenG7F s 0 = -678223072849 * s ^ 6 := by
  simp [orderSevenG7F]

/-- The left boundary meets the affine correspondence only at the cusp image. -/
theorem orderSevenG7F_zero_left_iff (B : ℚ) :
    orderSevenG7F 0 B = 0 ↔ B = 0 := by
  rw [orderSevenG7F_zero_left]
  norm_num

/-- The right boundary meets the affine correspondence only at the cusp image. -/
theorem orderSevenG7F_zero_right_iff (s : ℚ) :
    orderSevenG7F s 0 = 0 ↔ s = 0 := by
  rw [orderSevenG7F_zero_right]
  norm_num

end MazurTorsion.Kubert
