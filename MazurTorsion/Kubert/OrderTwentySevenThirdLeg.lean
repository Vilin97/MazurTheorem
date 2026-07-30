/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesB
import MazurTorsion.Kubert.OrderTwentySevenLegStagesD

/-!
# The third hauptmodul leg of the order-twenty-seven tower

The trisection abscissa produces a third leg completing the `X₀(9)` chain after the two family legs.
-/

namespace MazurTorsion.Kubert

lemma quad_pow_ne (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    a2legD f ≠ 0 := by
  simp only [a2legD]
  exact mul_ne_zero (mul_ne_zero hf0 (sub_ne_zero.mpr hf1))
    (pow_ne_zero 3 (quad_ne f))

lemma G9F_fraction_link (f B : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    orderNineG9F (a2legN f / a2legD f) B =
      (((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * B ^ 3 + (36 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 -
        6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2) * B ^ 2 + (270 * (f
        ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 * (f ^ 3 -
        6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 * (f * (f -
        1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * B + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9)) / (f * (f -
        1) * (f ^ 2 - f + 1) ^ 3) ^ 3 := by
  have h1 : f - 1 ≠ 0 := sub_ne_zero.mpr hf1
  have h2 : f ^ 2 - f + 1 ≠ 0 := quad_ne f
  simp only [orderNineG9F, a2legN, a2legD]
  field_simp
  ring

theorem thirdLeg_exists (f ξ : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0)
    (hT : trisectionPoly f ξ = 0) :
    ∃ s₃ : ℚ, orderNineG9F (a2legN f / a2legD f) s₃ = 0 := by
  have hT' := trisection_chunks hT
  have hD := tl_d_ne hf0 hf1 hT'
  have hMz := kernel_cubic_at hT' hD
  set Z : ℚ := (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) / (tlD0 f ξ + tlD1 f ξ)
  have hE := zl_e_ne hMz hf0 hf1 hK
  have hbig := zl_big hMz
  refine ⟨(zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 f Z) / (zlE0 f Z + zlE1 Z) ^ 2, ?_⟩
  rw [G9F_fraction_link f _ hf0 hf1, div_eq_zero_iff]
  left
  have hE2 : (zlE0 f Z + zlE1 Z) ^ 2 ≠ 0 := pow_ne_zero 2 hE
  field_simp
  linear_combination hbig

end MazurTorsion.Kubert
