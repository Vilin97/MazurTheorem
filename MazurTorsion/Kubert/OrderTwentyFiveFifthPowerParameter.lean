/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveQuotientDegeneracy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The fifth-power parameter above the order-twenty-five degeneracy map

The second degeneracy value on `X₀(25)` has a rational lift to the
generator-marked order-five Tate line exactly when its Tate parameter is a
fifth power.  More explicitly, the lift is parametrized by

`c = k⁵,   n = k - 1 / k - 1`.

For an actual point of exact order twenty-five, the normalization at `5P`
supplies precisely such a lift.  The final theorem records the resulting
rational Kummer parameter while retaining its identification with the
Lécacheux orbit Hauptmodul.  This is the input for a generator-level descent;
it does not assert that Fricke inversion preserves a rational generator.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The rational parameter on the generator-marked lift of the second
order-twenty-five degeneracy map. -/
def orderTwentyFiveFifthPowerHauptmodul (k : ℚ) : ℚ :=
  k - 1 / k - 1

/-- The square factor left after pulling the order-five generator
discriminant back along the second degeneracy map. -/
def orderTwentyFiveSecondLiftSquareFactor (n : ℚ) : ℚ :=
  n ^ 4 + 4 * n ^ 3 + 9 * n ^ 2 + 10 * n + 5

/-- The square factor in the second-degeneracy lift never vanishes over the
rationals. -/
theorem orderTwentyFiveSecondLiftSquareFactor_ne_zero (n : ℚ) :
    orderTwentyFiveSecondLiftSquareFactor n ≠ 0 := by
  have hnonnegFour := sq_nonneg ((n + 1) ^ 2)
  have hnonnegTwo := sq_nonneg (n + 1)
  intro hzero
  simp only [orderTwentyFiveSecondLiftSquareFactor] at hzero
  nlinarith

/-- The discriminant of the quadratic generator lift of the second
degeneracy value is one fixed square times `n² + 2n + 5`. -/
theorem orderTwentyFiveSecondDegeneracy_liftDiscriminant (n : ℚ) :
    orderTwentyFiveSecondDegeneracyParameter n ^ 2 +
        22 * orderTwentyFiveSecondDegeneracyParameter n + 125 =
      (n ^ 2 + 2 * n + 5) *
        orderTwentyFiveSecondLiftSquareFactor n ^ 2 := by
  simp only [orderTwentyFiveSecondDegeneracyParameter,
    orderTwentyFiveHauptmodulDenominator,
    orderTwentyFiveSecondLiftSquareFactor]
  ring

/-- The explicit fifth-power lift has the prescribed second degeneracy
value. -/
theorem orderFiveXZeroParameter_fifthPower
    (k : ℚ) (hk : k ≠ 0) :
    orderFiveXZeroParameter (k ^ 5) =
      orderTwentyFiveSecondDegeneracyParameter
        (orderTwentyFiveFifthPowerHauptmodul k) := by
  simp only [orderFiveXZeroParameter,
    orderTwentyFiveSecondDegeneracyParameter,
    orderTwentyFiveHauptmodulDenominator,
    orderTwentyFiveFifthPowerHauptmodul]
  field_simp [hk]
  ring

/-- A three-adic unit `k` gives a three-integral value of the fifth-power
Hauptmodul.  This is the elementary denominator calculation used to turn the
old residual Hauptmodul case into a genuine Kummer-unit obstruction. -/
theorem orderTwentyFiveFifthPowerHauptmodul_threeIntegral_of_threeUnit
    (k : ℚ) (hk : k ≠ 0)
    (hunit : orderTwentyFiveRatIsThreeUnit k) :
    orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveFifthPowerHauptmodul k) := by
  have hnum : k.num ≠ 0 := Rat.num_ne_zero.mpr hk
  have hden : (k.den : ℤ) ≠ 0 := by
    exact_mod_cast k.den_nz
  apply orderTwentyFiveRatIsThreeIntegral_of_eq_div
    (orderTwentyFiveFifthPowerHauptmodul k)
    (k.num ^ 2 - k.num * (k.den : ℤ) - (k.den : ℤ) ^ 2)
    (k.num * (k.den : ℤ)) (mul_ne_zero hnum hden)
  · rw [orderTwentyFiveFifthPowerHauptmodul]
    conv_lhs => rw [← Rat.num_div_den k]
    push_cast
    field_simp [hnum, hden]
    ring
  · simpa only [Int.cast_mul, Int.cast_natCast] using
      mul_ne_zero hunit.2 hunit.1

/-- Every nonzero rational generator lift of a second degeneracy value is
parametrized by a nonzero rational fifth root. -/
theorem exists_orderTwentyFiveFifthPowerParameter_of_secondDegeneracy
    (c n : ℚ) (hc : c ≠ 0)
    (hlift : orderFiveXZeroParameter c =
      orderTwentyFiveSecondDegeneracyParameter n) :
    ∃ k : ℚ, k ≠ 0 ∧ c = k ^ 5 ∧
      n = orderTwentyFiveFifthPowerHauptmodul k := by
  let s := orderTwentyFiveSecondDegeneracyParameter n
  let B := orderTwentyFiveSecondLiftSquareFactor n
  let y := (2 * c - s - 11) / B
  let k := (y + n + 1) / 2
  have hB : B ≠ 0 := by
    exact orderTwentyFiveSecondLiftSquareFactor_ne_zero n
  have hcurve : c ^ 2 - (s + 11) * c - 1 = 0 := by
    have h : (c ^ 2 - 11 * c - 1) / c = s := by
      simpa only [orderFiveXZeroParameter, s] using hlift
    field_simp [hc] at h
    linear_combination h
  have hsquare :
      (2 * c - s - 11) ^ 2 = s ^ 2 + 22 * s + 125 := by
    nlinarith [hcurve]
  have hfactor :
      s ^ 2 + 22 * s + 125 =
        (n ^ 2 + 2 * n + 5) * B ^ 2 := by
    simpa only [s, B] using
      orderTwentyFiveSecondDegeneracy_liftDiscriminant n
  have hy : y ^ 2 = n ^ 2 + 2 * n + 5 := by
    dsimp only [y]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hB)).2
    nlinarith [hsquare, hfactor]
  have hk : k ≠ 0 := by
    intro hkzero
    have hlinear : y + n + 1 = 0 := by
      dsimp only [k] at hkzero
      linarith
    nlinarith [hy]
  have hkLinear : 2 * k = y + n + 1 := by
    dsimp only [k]
    ring
  have hkProduct : k * (y - n - 1) = 2 := by
    dsimp only [k]
    rw [div_mul_eq_mul_div]
    rw [show (y + n + 1) * (y - n - 1) =
        y ^ 2 - (n + 1) ^ 2 by ring]
    rw [hy]
    ring
  have hinverse : 1 / k = (y - n - 1) / 2 := by
    field_simp [hk]
    linarith [hkProduct]
  have hn : n = orderTwentyFiveFifthPowerHauptmodul k := by
    simp only [orderTwentyFiveFifthPowerHauptmodul]
    rw [hinverse]
    dsimp only [k]
    ring
  have hyParam : y = k + 1 / k := by
    rw [hinverse]
    dsimp only [k]
    ring
  have hparamIdentity :
      2 * k ^ 5 - s - 11 = B * (k + 1 / k) := by
    dsimp only [s, B]
    rw [hn]
    simp only [orderTwentyFiveFifthPowerHauptmodul,
      orderTwentyFiveSecondDegeneracyParameter,
      orderTwentyFiveHauptmodulDenominator,
      orderTwentyFiveSecondLiftSquareFactor]
    field_simp [hk]
    ring
  have hyDefinition : B * y = 2 * c - s - 11 := by
    dsimp only [y]
    field_simp [hB]
  have hcPower : c = k ^ 5 := by
    rw [hyParam] at hyDefinition
    nlinarith [hyDefinition, hparamIdentity]
  exact ⟨k, hk, hcPower, hn⟩

/-- The normalization at `5P` of an exact-order-twenty-five marked Tate
point has a rational fifth-power parameter, and the associated Hauptmodul is
the signed Lécacheux orbit parameter already identified by the two degeneracy
maps. -/
theorem orderTwentyFive_fiveMultiple_fifthPowerParameter
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ k : ℚ, k ≠ 0 ∧
      orderTwentyFiveFiveTateParameter b c = k ^ 5 ∧
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul k := by
  have hc5 := (orderTwentyFiveFiveTateParameter_ne
    b c hb h00 horder).1
  apply exists_orderTwentyFiveFifthPowerParameter_of_secondDegeneracy
    (orderTwentyFiveFiveTateParameter b c)
    (-(orderTwentyFiveOrbitParameter
      (orderTwentyFiveBrunaultXZero b c)
      (orderTwentyFiveBrunaultXOne b c)
      (orderTwentyFiveBrunaultXTwo b c)
      (orderTwentyFiveBrunaultXThree b c)
      (orderTwentyFiveBrunaultXFour b c))) hc5
  simpa only [orderTwentyFiveFiveTateParameter] using
    orderTwentyFive_fiveMultiple_xZeroParameter_eq_orbitDegeneracy
      b c hb h00 horder

/-- Any hypothetical exact-order-twenty-five marked Tate point lies in the
nonunit branch of the rational fifth-power parameter.  The reciprocal
Hauptmodul remains three-integral, so this packages the precise arithmetic
case that a generator-level Kummer descent must eliminate. -/
theorem orderTwentyFive_fifthPowerParameter_residual_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ k : ℚ, k ≠ 0 ∧
      orderTwentyFiveFiveTateParameter b c = k ^ 5 ∧
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul k ∧
      ¬orderTwentyFiveRatIsThreeUnit k ∧
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul k) := by
  let N := orderTwentyFiveOrbitParameter
    (orderTwentyFiveBrunaultXZero b c)
    (orderTwentyFiveBrunaultXOne b c)
    (orderTwentyFiveBrunaultXTwo b c)
    (orderTwentyFiveBrunaultXThree b c)
    (orderTwentyFiveBrunaultXFour b c)
  obtain ⟨hN, hNNotIntegral, hNReciprocal⟩ :=
    orderTwentyFiveOrbitParameter_residual_integrality_of_marked_order
      b c hb h00 horder
  obtain ⟨k, hk, hc, hkParameter⟩ :=
    orderTwentyFive_fiveMultiple_fifthPowerParameter
      b c hb h00 horder
  have hkNotUnit : ¬orderTwentyFiveRatIsThreeUnit k := by
    intro hunit
    have hintegral :=
      orderTwentyFiveFifthPowerHauptmodul_threeIntegral_of_threeUnit
        k hk hunit
    rw [← hkParameter] at hintegral
    apply hNNotIntegral
    simpa only [orderTwentyFiveRatIsThreeIntegral,
      Rat.den_neg_eq_den] using hintegral
  have hreciprocal :
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul k) := by
    rw [← hkParameter]
    convert hNReciprocal using 1
    field_simp [hN]
  exact ⟨k, hk, hc, hkParameter, hkNotUnit, hreciprocal⟩

end MazurTorsion.Kubert
