/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerBounds

/-!
# The rational Kummer cover behind the positive `X₁(13)` Pell split

The checked integral split

`H(a,b) + c K(a,b) = 2 r³⁸`, `c K(a,b) - H(a,b) = 2 s³⁸`, `b = rs`

has a useful intrinsic formulation on the affine curve.  Put

`x = a / b`, `y = c / b³`, and `t = r / s`.

Then the Pell unit is an actual nineteenth power,

`pellH x + y * pellK x = 2 * t¹⁹`,

its conjugate is `-2 / t¹⁹`, and the checked archimedean bounds become
the strict strip `t - 1 < x < t` with `1 < t`.

This is the explicit rational Kummer cover to which a later height or
Jacobian descent must be applied.  The file does not assert that the cover
has no rational points.
-/

namespace MazurTorsion.XOneThirteenDescent

/-- Rational data on the nineteenth-power cover cut out by the Pell unit. -/
structure PositivePellKummerLift where
  x : ℚ
  y : ℚ
  t : ℚ
  one_lt_t : 1 < t
  strip : t - 1 < x ∧ x < t
  curve :
    y ^ 2 = MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x
  pellPower : pellH x + y * pellK x = 2 * t ^ 19
  pellConjugate : pellH x - y * pellK x = -2 / t ^ 19

private theorem normalized_curve_equation
    (a b c : ℤ) (hb : b ≠ 0)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    (((c : ℚ) / (b : ℚ) ^ 3) ^ 2) =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial
        ((a : ℚ) / (b : ℚ)) := by
  have hhom := integerSexticHomogeneous_eq_den_pow_mul a b hb
  have hcurveQ :
      (c : ℚ) ^ 2 = (integerSexticHomogeneous a b : ℚ) := by
    exact_mod_cast hcurve
  calc
    ((c : ℚ) / (b : ℚ) ^ 3) ^ 2 =
        (c : ℚ) ^ 2 / (b : ℚ) ^ 6 := by ring
    _ = (integerSexticHomogeneous a b : ℚ) / (b : ℚ) ^ 6 := by
      rw [hcurveQ]
    _ = MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial
        ((a : ℚ) / (b : ℚ)) := by
      rw [hhom]
      field_simp [Int.cast_ne_zero.mpr hb]

private theorem normalized_pell_power
    (a b c r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    pellH ((a : ℚ) / (b : ℚ)) +
          ((c : ℚ) / (b : ℚ) ^ 3) *
            pellK ((a : ℚ) / (b : ℚ)) =
        2 * ((r : ℚ) / (s : ℚ)) ^ 19 ∧
      pellH ((a : ℚ) / (b : ℚ)) -
          ((c : ℚ) / (b : ℚ) ^ 3) *
            pellK ((a : ℚ) / (b : ℚ)) =
        -2 / ((r : ℚ) / (s : ℚ)) ^ 19 := by
  have hb : b ≠ 0 := by rw [hbSplit]; exact mul_ne_zero hr hs
  have hH := pellHHomogeneous_eq_den_pow_mul a b hb
  have hK := pellKHomogeneous_eq_den_pow_mul a b hb
  have hplusQ :
      (pellHHomogeneous a b : ℚ) +
          (c : ℚ) * (pellKHomogeneous a b : ℚ) =
        2 * (r : ℚ) ^ 38 := by
    exact_mod_cast hplus
  have hminusQ :
      (c : ℚ) * (pellKHomogeneous a b : ℚ) -
          (pellHHomogeneous a b : ℚ) =
        2 * (s : ℚ) ^ 38 := by
    exact_mod_cast hminus
  let x : ℚ := (a : ℚ) / (b : ℚ)
  let y : ℚ := (c : ℚ) / (b : ℚ) ^ 3
  have hKterm :
      (b : ℚ) ^ 19 * (y * pellK x) =
        (c : ℚ) * (pellKHomogeneous a b : ℚ) := by
    rw [hK]
    dsimp only [x, y]
    field_simp [Int.cast_ne_zero.mpr hb]
  have hplusNormalized :
      (b : ℚ) ^ 19 * (pellH x + y * pellK x) =
        2 * (r : ℚ) ^ 38 := by
    rw [mul_add, hKterm, ← hH]
    exact hplusQ
  have hminusNormalized :
      (b : ℚ) ^ 19 * (pellH x - y * pellK x) =
        -2 * (s : ℚ) ^ 38 := by
    rw [mul_sub, hKterm, ← hH]
    linarith
  constructor
  · change pellH x + y * pellK x = _
    apply mul_left_cancel₀ (pow_ne_zero 19 (Int.cast_ne_zero.mpr hb : (b : ℚ) ≠ 0))
    rw [hplusNormalized, hbSplit]
    push_cast
    field_simp [Int.cast_ne_zero.mpr hs]
  · change pellH x - y * pellK x = _
    apply mul_left_cancel₀ (pow_ne_zero 19 (Int.cast_ne_zero.mpr hb : (b : ℚ) ≠ 0))
    rw [hminusNormalized, hbSplit]
    push_cast
    field_simp [Int.cast_ne_zero.mpr hr, Int.cast_ne_zero.mpr hs]

/-- Every positive Pell-power split gives a rational point on the explicit
nineteenth-power Kummer cover, lying in the strict real strip `t-1 < x < t`.
-/
noncomputable def positivePellKummerLift_of_powerSplit
    (a b c r s : ℤ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (hs : 0 < s)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b)
    (hplus : positivePellFactor a b c = 2 * r ^ 38)
    (hminus : negativePellFactorMagnitude a b c = 2 * s ^ 38)
    (hbSplit : b = r * s) :
    PositivePellKummerLift := by
  have hbNe : b ≠ 0 := ne_of_gt hb
  have hrNe : r ≠ 0 := ne_of_gt hr
  have hsNe : s ≠ 0 := ne_of_gt hs
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hsQ : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  obtain ⟨hsr, har, hrsum⟩ :=
    pell_power_split_strict_bounds a b c r s ha hb hr hs
      hplus hminus hbSplit
  have hsrQ : (s : ℚ) < (r : ℚ) := by exact_mod_cast hsr
  obtain ⟨hpower, hconjugate⟩ :=
    normalized_pell_power a b c r s hrNe hsNe hplus hminus hbSplit
  refine
    { x := (a : ℚ) / (b : ℚ)
      y := (c : ℚ) / (b : ℚ) ^ 3
      t := (r : ℚ) / (s : ℚ)
      one_lt_t := ?_
      strip := ?_
      curve := normalized_curve_equation a b c hbNe hcurve
      pellPower := hpower
      pellConjugate := hconjugate }
  · calc
      (1 : ℚ) = (s : ℚ) / (s : ℚ) := by
        field_simp [Int.cast_ne_zero.mpr hsNe]
      _ < (r : ℚ) / (s : ℚ) :=
        (div_lt_div_iff_of_pos_right hsQ).2 hsrQ
  · constructor
    · have ht :
          (r : ℚ) / (s : ℚ) = (r : ℚ) ^ 2 / (b : ℚ) := by
        rw [hbSplit]
        push_cast
        field_simp [Int.cast_ne_zero.mpr hrNe, Int.cast_ne_zero.mpr hsNe]
      rw [ht]
      rw [show (r : ℚ) ^ 2 / (b : ℚ) - 1 =
          ((r : ℚ) ^ 2 - (b : ℚ)) / (b : ℚ) by
        field_simp [Int.cast_ne_zero.mpr hbNe]]
      apply (div_lt_div_iff_of_pos_right hbQ).2
      have hrsumQ : (r : ℚ) ^ 2 < (a : ℚ) + (b : ℚ) := by
        exact_mod_cast hrsum
      linarith
    · have ht :
          (r : ℚ) / (s : ℚ) = (r : ℚ) ^ 2 / (b : ℚ) := by
        rw [hbSplit]
        push_cast
        field_simp [Int.cast_ne_zero.mpr hrNe, Int.cast_ne_zero.mpr hsNe]
      rw [ht]
      apply (div_lt_div_iff_of_pos_right hbQ).2
      exact_mod_cast har

end MazurTorsion.XOneThirteenDescent
