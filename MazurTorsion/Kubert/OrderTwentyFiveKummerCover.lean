/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveFifthPowerParameter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The generator-marked order-twenty-five Kummer cover

The fifth-power lift writes the signed `X₀(25)` Hauptmodul as

`k - 1 / k - 1`.

Substituting its negative into Lehmer's cyclic quintic and clearing the four
powers of `k` gives the explicit integral polynomial below.  Thus a
hypothetical point of exact order twenty-five produces a rational point on
this fixed two-variable cover, together with the non-three-unit and
three-integral reciprocal conditions already isolated by the preceding
module.

This is the compact equation consumed by the generator-level Kummer descent;
no rational Fricke lift is asserted.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The integral affine equation obtained by pulling Lehmer's genus-four
cover back to the rational fifth-root parameter and clearing `k⁴`. -/
def orderTwentyFiveKummerCoverPolynomial
    {R : Type*} [CommRing R] (k x : R) : R :=
  k ^ 4 * x ^ 5 -
    k ^ 2 * (k ^ 2 - k - 1) ^ 2 * x ^ 4 -
    2 * k * (k ^ 6 - k ^ 4 + 2 * k ^ 3 + k ^ 2 - 1) * x ^ 3 +
    (-k ^ 8 - k ^ 7 + 2 * k ^ 6 - k ^ 5 + k ^ 4 + k ^ 3 +
      2 * k ^ 2 + k - 1) * x ^ 2 +
    k * (k ^ 6 + k ^ 5 + 2 * k ^ 4 + k ^ 3 - 2 * k ^ 2 + k - 1) * x -
    k ^ 4

/-- The displayed Kummer-cover equation is exactly the denominator-cleared
Lehmer equation at the fifth-power Hauptmodul. -/
theorem orderTwentyFiveKummerCoverPolynomial_eq_clearedLehmer
    (k x : ℚ) (hk : k ≠ 0) :
    orderTwentyFiveKummerCoverPolynomial k x =
      k ^ 4 * orderTwentyFiveLehmerPolynomial
        (-orderTwentyFiveFifthPowerHauptmodul k) x := by
  simp only [orderTwentyFiveKummerCoverPolynomial,
    orderTwentyFiveLehmerPolynomial,
    orderTwentyFiveFifthPowerHauptmodul]
  field_simp [hk]
  ring

/-- The two rational parameters above the same signed Hauptmodul are
exchanged by `k ↦ -1/k`. -/
theorem orderTwentyFiveFifthPowerHauptmodul_neg_inv
    (k : ℚ) (hk : k ≠ 0) :
    orderTwentyFiveFifthPowerHauptmodul (-1 / k) =
      orderTwentyFiveFifthPowerHauptmodul k := by
  simp only [orderTwentyFiveFifthPowerHauptmodul]
  field_simp [hk]
  ring

/-- The deck transformation `k ↦ -1/k` preserves the pulled-back cover,
up to the harmless clearing factor `k⁸`. -/
theorem orderTwentyFiveKummerCoverPolynomial_neg_inv
    (k x : ℚ) (hk : k ≠ 0) :
    k ^ 8 * orderTwentyFiveKummerCoverPolynomial (-1 / k) x =
      orderTwentyFiveKummerCoverPolynomial k x := by
  simp only [orderTwentyFiveKummerCoverPolynomial]
  field_simp [hk]
  ring

/-- Vanishing of the pulled-back cover is invariant under its rational deck
transformation. -/
theorem orderTwentyFiveKummerCoverPolynomial_neg_inv_eq_zero_iff
    (k x : ℚ) (hk : k ≠ 0) :
    orderTwentyFiveKummerCoverPolynomial (-1 / k) x = 0 ↔
      orderTwentyFiveKummerCoverPolynomial k x = 0 := by
  constructor
  · intro hzero
    rw [← orderTwentyFiveKummerCoverPolynomial_neg_inv k x hk,
      hzero, mul_zero]
  · intro hzero
    have hidentity :=
      orderTwentyFiveKummerCoverPolynomial_neg_inv k x hk
    rw [hzero] at hidentity
    exact (mul_eq_zero.mp hidentity).resolve_left (pow_ne_zero 8 hk)

/-- The first modular-unit coordinate of an actual marked point is a root of
Lehmer's quintic at its recovered orbit parameter.  This is the direct
marked-point input to the pulled-back cover. -/
theorem orderTwentyFiveBrunaultXZero_lehmerRoot_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveLehmerPolynomial
      (orderTwentyFiveOrbitParameter
        (orderTwentyFiveBrunaultXZero b c)
        (orderTwentyFiveBrunaultXOne b c)
        (orderTwentyFiveBrunaultXTwo b c)
        (orderTwentyFiveBrunaultXThree b c)
        (orderTwentyFiveBrunaultXFour b c))
      (orderTwentyFiveBrunaultXZero b c) = 0 := by
  have ha : orderTwentyFiveBrunaultXZero b c ≠ 1 := by
    rw [orderTwentyFiveBrunaultXZero_eq_U]
    exact orderTwentyFiveBrunaultU_ne_one_of_marked_order
      b c hb h00 horder
  exact (orderTwentyFiveLehmer_selectedRoots_of_orbit
    (orderTwentyFiveBrunaultXZero b c)
    (orderTwentyFiveBrunaultXOne b c)
    (orderTwentyFiveBrunaultXTwo b c)
    (orderTwentyFiveBrunaultXThree b c)
    (orderTwentyFiveBrunaultXFour b c) ha
    (orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order
      b c hb h00 horder)
    (orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
      b c hb h00 horder)).1

/-- A hypothetical exact-order-twenty-five point supplies a rational point on
the cleared generator-marked Kummer cover.  The same witness retains the
fifth-power Tate parameter and the precise residual three-adic conditions. -/
theorem orderTwentyFive_kummerCover_of_marked_order
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
        (-5 / orderTwentyFiveFifthPowerHauptmodul k) ∧
      orderTwentyFiveBrunaultXZero b c ≠ 0 ∧
      orderTwentyFiveBrunaultXZero b c ≠ 1 ∧
      orderTwentyFiveKummerCoverPolynomial k
        (orderTwentyFiveBrunaultXZero b c) = 0 := by
  obtain ⟨k, hk, hc, hkParameter, hkNotUnit, hreciprocal⟩ :=
    orderTwentyFive_fifthPowerParameter_residual_of_marked_order
      b c hb h00 horder
  have hxZero :=
    (orderTwentyFiveBrunault_orbit_units_ne_zero
      b c hb h00 horder).1
  have hxZeroOne : orderTwentyFiveBrunaultXZero b c ≠ 1 := by
    rw [orderTwentyFiveBrunaultXZero_eq_U]
    exact orderTwentyFiveBrunaultU_ne_one_of_marked_order
      b c hb h00 horder
  refine ⟨k, hk, hc, hkParameter, hkNotUnit, hreciprocal,
    hxZero, hxZeroOne, ?_⟩
  rw [orderTwentyFiveKummerCoverPolynomial_eq_clearedLehmer k _ hk]
  have hparameter :
      -orderTwentyFiveFifthPowerHauptmodul k =
        orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c) := by
    linarith
  rw [hparameter,
    orderTwentyFiveBrunaultXZero_lehmerRoot_of_marked_order
      b c hb h00 horder, mul_zero]

end MazurTorsion.Kubert
