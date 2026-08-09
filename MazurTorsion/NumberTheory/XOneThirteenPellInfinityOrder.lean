/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellQuadratic

/-!
# Exact infinity-chart order certificates for the `X₁(13)` Pell function

The reciprocal sextic and Pell polynomials, together with their product
identity, are already checked in `XOneThirteenDescent`.  This file adds only
the missing local algebra certificate.

With `x = 1/z` and `η = z³y`, the normalized Pell brackets are

`H∞(z) + η K∞(z)` and `H∞(z) - η K∞(z)`.

There is no additional power of `z` on `K∞`: both summands result after
multiplying `H(x) ± yK(x)` by `z¹⁹`.  At either infinity sign, one
bracket has value `2`.  Dividing `-4` by that nonvanishing bracket gives an
explicit rational chart function whose product with the conjugate bracket is
exactly `z³⁸`; its value at the relevant boundary point is `-2`.  Thus the
checked data exhibit the exact unit cofactor needed for an order-`38`
calculation, without constructing a local ring or asserting a divisor result.
-/

namespace MazurTorsion.XOneThirteenDescent

noncomputable section

/-- The normalized equation on the reciprocal chart `x = 1/z`, `η = z³y`. -/
def IsInfinityChartPoint (z η : ℚ) : Prop :=
  η ^ 2 = infinitySextic z

/-- Away from `z = 0`, the reciprocal chart maps back to the original affine
sextic by `(x, y) = (1/z, η/z³)`. -/
theorem affine_curve_of_isInfinityChartPoint
    (z η : ℚ) (hz : z ≠ 0) (hchart : IsInfinityChartPoint z η) :
    (η / z ^ 3) ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial (1 / z) := by
  rw [div_pow, hchart,
    infinitySextic_eq_reciprocal z hz]
  field_simp [hz]

/-- The normalized `H + yK` bracket on the reciprocal chart. -/
def infinityPellPlusBracket (z η : ℚ) : ℚ :=
  infinityPellH z + η * infinityPellK z

/-- The normalized `H - yK` bracket on the reciprocal chart. -/
def infinityPellMinusBracket (z η : ℚ) : ℚ :=
  infinityPellH z - η * infinityPellK z

/-- Clearing the pole of `H(x) + yK(x)` by `z¹⁹` gives the plus bracket.
In particular, no extra `z` multiplies `K∞`. -/
theorem infinityPellPlusBracket_eq_reciprocal
    (z η : ℚ) (hz : z ≠ 0) :
    infinityPellPlusBracket z η =
      z ^ 19 *
        (pellH (1 / z) + (η / z ^ 3) * pellK (1 / z)) := by
  rw [infinityPellPlusBracket,
    infinityPellH_eq_reciprocal z hz,
    infinityPellK_eq_reciprocal z hz]
  field_simp [hz]

/-- Clearing the pole of `H(x) - yK(x)` by `z¹⁹` gives the minus bracket. -/
theorem infinityPellMinusBracket_eq_reciprocal
    (z η : ℚ) (hz : z ≠ 0) :
    infinityPellMinusBracket z η =
      z ^ 19 *
        (pellH (1 / z) - (η / z ^ 3) * pellK (1 / z)) := by
  rw [infinityPellMinusBracket,
    infinityPellH_eq_reciprocal z hz,
    infinityPellK_eq_reciprocal z hz]
  field_simp [hz]

/-- Both normalized infinity signs lie on the reciprocal chart. -/
theorem infinityChart_boundary_points :
    IsInfinityChartPoint 0 1 ∧ IsInfinityChartPoint 0 (-1) := by
  rcases infinity_pell_boundary_values with ⟨hf, -⟩
  simp [IsInfinityChartPoint, hf]

/-- Values of both normalized brackets at both infinity signs. -/
theorem infinityPell_bracket_boundary_values :
    infinityPellPlusBracket 0 1 = 2 ∧
      infinityPellMinusBracket 0 1 = 0 ∧
      infinityPellPlusBracket 0 (-1) = 0 ∧
      infinityPellMinusBracket 0 (-1) = 2 := by
  rcases infinity_pell_boundary_values with ⟨_, hH, hK, _, _⟩
  norm_num [infinityPellPlusBracket, infinityPellMinusBracket, hH, hK]

/-- Rational quotient which becomes the `z³⁸` cofactor for the minus
bracket near the infinity sign `η = 1`.  Its denominator has value `2` there. -/
def infinityPellMinusOrderQuotient (z η : ℚ) : ℚ :=
  -4 / infinityPellPlusBracket z η

/-- Rational quotient which becomes the `z³⁸` cofactor for the plus
bracket near the infinity sign `η = -1`.  Its denominator has value `2` there. -/
def infinityPellPlusOrderQuotient (z η : ℚ) : ℚ :=
  -4 / infinityPellMinusBracket z η

/-- On the chart, wherever the plus bracket is nonzero, the vanishing minus
bracket is exactly `z³⁸` times its explicit rational cofactor. -/
theorem infinityPellMinusBracket_eq_pow_mul_orderQuotient
    (z η : ℚ) (hchart : IsInfinityChartPoint z η)
    (hplus : infinityPellPlusBracket z η ≠ 0) :
    infinityPellMinusBracket z η =
      z ^ 38 * infinityPellMinusOrderQuotient z η := by
  have hproduct :
      infinityPellPlusBracket z η * infinityPellMinusBracket z η =
        -4 * z ^ 38 := by
    exact infinity_pell_factorization z η hchart
  unfold infinityPellMinusOrderQuotient
  apply mul_left_cancel₀ hplus
  rw [hproduct]
  field_simp [hplus]

/-- On the chart, wherever the minus bracket is nonzero, the vanishing plus
bracket is exactly `z³⁸` times its explicit rational cofactor. -/
theorem infinityPellPlusBracket_eq_pow_mul_orderQuotient
    (z η : ℚ) (hchart : IsInfinityChartPoint z η)
    (hminus : infinityPellMinusBracket z η ≠ 0) :
    infinityPellPlusBracket z η =
      z ^ 38 * infinityPellPlusOrderQuotient z η := by
  have hproduct :
      infinityPellPlusBracket z η * infinityPellMinusBracket z η =
        -4 * z ^ 38 := by
    exact infinity_pell_factorization z η hchart
  unfold infinityPellPlusOrderQuotient
  apply mul_left_cancel₀ hminus
  calc
    infinityPellMinusBracket z η * infinityPellPlusBracket z η =
        infinityPellPlusBracket z η * infinityPellMinusBracket z η :=
      mul_comm _ _
    _ = -4 * z ^ 38 := hproduct
    _ = infinityPellMinusBracket z η *
        (z ^ 38 * (-4 / infinityPellMinusBracket z η)) := by
      field_simp [hminus]

/-- The minus-bracket cofactor has nonzero boundary value `-2` at `η = 1`. -/
theorem infinityPellMinusOrderQuotient_zero_one :
    infinityPellMinusOrderQuotient 0 1 = -2 := by
  have hvalues := infinityPell_bracket_boundary_values
  norm_num [infinityPellMinusOrderQuotient, hvalues.1]

/-- The plus-bracket cofactor has nonzero boundary value `-2` at `η = -1`. -/
theorem infinityPellPlusOrderQuotient_zero_neg_one :
    infinityPellPlusOrderQuotient 0 (-1) = -2 := by
  have hvalues := infinityPell_bracket_boundary_values
  norm_num [infinityPellPlusOrderQuotient, hvalues.2.2.2]

theorem infinityPellMinusOrderQuotient_zero_one_ne_zero :
    infinityPellMinusOrderQuotient 0 1 ≠ 0 := by
  rw [infinityPellMinusOrderQuotient_zero_one]
  norm_num

theorem infinityPellPlusOrderQuotient_zero_neg_one_ne_zero :
    infinityPellPlusOrderQuotient 0 (-1) ≠ 0 := by
  rw [infinityPellPlusOrderQuotient_zero_neg_one]
  norm_num

end

end MazurTorsion.XOneThirteenDescent
