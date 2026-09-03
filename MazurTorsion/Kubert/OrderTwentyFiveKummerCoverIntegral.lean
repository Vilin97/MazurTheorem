/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveKummerCover

/-!
# Primitive integral data for the order-twenty-five Kummer cover

The deck involution `k ↦ -1 / k` orients every non-three-unit rational
parameter as a primitive fraction `m / n` with `3 ∣ m` and `3 ∤ n`.  This
file then writes a rational cover point `x = u / v` in normalized primitive
coordinates and clears all denominators from the cover equation.

Reducing the resulting homogeneous equation modulo three gives its first
descent dichotomy: three divides either `u` or `v`.  The final theorem is the
named modular-point consumer and supplies exactly this integral descent data
from a hypothetical marked point of order twenty-five.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Orient a non-three-unit Kummer parameter by the deck involution.  The
resulting numerator and denominator are primitive, the numerator vanishes
modulo three, the denominator does not, and both the Hauptmodul and the cover
point are unchanged. -/
theorem orderTwentyFiveKummerCover_threeAdicOrientation
    (k x : ℚ) (hk : k ≠ 0)
    (hkNotUnit : ¬orderTwentyFiveRatIsThreeUnit k)
    (hcover : orderTwentyFiveKummerCoverPolynomial k x = 0) :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ IsCoprime m n ∧
      (m : ZMod 3) = 0 ∧ (n : ZMod 3) ≠ 0 ∧
      orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) =
        orderTwentyFiveFifthPowerHauptmodul k ∧
      orderTwentyFiveKummerCoverPolynomial
          ((m : ℚ) / (n : ℚ)) x = 0 := by
  by_cases hden : (k.den : ZMod 3) = 0
  · have hnum : k.num ≠ 0 := Rat.num_ne_zero.mpr hk
    have hnum3 : (k.num : ZMod 3) ≠ 0 :=
      orderTwentyFiveRat_num_mod_three_ne_zero_of_den_eq_zero k hden
    have hdenInt : (k.den : ℤ) ≠ 0 := by
      exact_mod_cast k.den_nz
    have hfraction :
        ((-(k.den : ℤ) : ℤ) : ℚ) / (k.num : ℚ) = -1 / k := by
      calc
        ((-(k.den : ℤ) : ℤ) : ℚ) / (k.num : ℚ) =
            -1 / ((k.num : ℚ) / (k.den : ℚ)) := by
              push_cast
              field_simp [hnum, hdenInt]
        _ = -1 / k := by rw [Rat.num_div_den]
    refine ⟨-(k.den : ℤ), k.num, neg_ne_zero.mpr hdenInt, hnum,
      (Rat.isCoprime_num_den k).symm.neg_left, ?_, hnum3, ?_, ?_⟩
    · simpa using hden
    · rw [hfraction,
        orderTwentyFiveFifthPowerHauptmodul_neg_inv k hk]
    · rw [hfraction]
      exact
        (orderTwentyFiveKummerCoverPolynomial_neg_inv_eq_zero_iff
          k x hk).2 hcover
  · have hnum3 : (k.num : ZMod 3) = 0 := by
      by_contra hnum3
      exact hkNotUnit ⟨hden, hnum3⟩
    have hnum : k.num ≠ 0 := Rat.num_ne_zero.mpr hk
    have hdenInt : (k.den : ℤ) ≠ 0 := by
      exact_mod_cast k.den_nz
    refine ⟨k.num, (k.den : ℤ), hnum, hdenInt,
      Rat.isCoprime_num_den k, hnum3, hden, ?_, ?_⟩
    · simp only [Int.cast_natCast, Rat.num_div_den]
    · simpa only [Int.cast_natCast, Rat.num_div_den] using hcover

/-- The integral polynomial obtained by substituting `k = m / n` and
`x = u / v` into the Kummer cover and multiplying by `n⁸ v⁵`. -/
def orderTwentyFiveKummerCoverClearedNumerator
    (m n u v : ℤ) : ℤ :=
  m ^ 4 * n ^ 4 * u ^ 5 -
    m ^ 2 * n ^ 2 * (m ^ 2 - m * n - n ^ 2) ^ 2 * u ^ 4 * v -
    2 * m * n *
      (m ^ 6 - m ^ 4 * n ^ 2 + 2 * m ^ 3 * n ^ 3 +
        m ^ 2 * n ^ 4 - n ^ 6) * u ^ 3 * v ^ 2 +
    (-m ^ 8 - m ^ 7 * n + 2 * m ^ 6 * n ^ 2 - m ^ 5 * n ^ 3 +
      m ^ 4 * n ^ 4 + m ^ 3 * n ^ 5 + 2 * m ^ 2 * n ^ 6 +
      m * n ^ 7 - n ^ 8) * u ^ 2 * v ^ 3 +
    m * n *
      (m ^ 6 + m ^ 5 * n + 2 * m ^ 4 * n ^ 2 + m ^ 3 * n ^ 3 -
        2 * m ^ 2 * n ^ 4 + m * n ^ 5 - n ^ 6) * u * v ^ 4 -
    m ^ 4 * n ^ 4 * v ^ 5

/-- Clearing the two rational denominators gives exactly the displayed
integral polynomial. -/
theorem orderTwentyFiveKummerCoverClearedNumerator_rat_identity
    (m n u v : ℤ) (hn : n ≠ 0) (hv : v ≠ 0) :
    (orderTwentyFiveKummerCoverClearedNumerator m n u v : ℚ) =
      (n : ℚ) ^ 8 * (v : ℚ) ^ 5 *
        orderTwentyFiveKummerCoverPolynomial
          ((m : ℚ) / (n : ℚ)) ((u : ℚ) / (v : ℚ)) := by
  simp only [orderTwentyFiveKummerCoverClearedNumerator,
    orderTwentyFiveKummerCoverPolynomial]
  push_cast
  field_simp [hn, hv]

/-- A rational cover root, expressed by two nonzero-denominator integer
fractions, satisfies the cleared integral equation. -/
theorem orderTwentyFiveKummerCoverClearedNumerator_eq_zero
    (m n u v : ℤ) (hn : n ≠ 0) (hv : v ≠ 0)
    (hcover : orderTwentyFiveKummerCoverPolynomial
      ((m : ℚ) / (n : ℚ)) ((u : ℚ) / (v : ℚ)) = 0) :
    orderTwentyFiveKummerCoverClearedNumerator m n u v = 0 := by
  have hidentity :=
    orderTwentyFiveKummerCoverClearedNumerator_rat_identity
      m n u v hn hv
  rw [hcover, mul_zero] at hidentity
  exact_mod_cast hidentity

/-- In the three-adically oriented chart, reduction of the cleared cover
equation forces one of the root coordinates to vanish modulo three. -/
theorem orderTwentyFiveKummerCoverClearedNumerator_mod_three
    (m n u v : ℤ)
    (hm : (m : ZMod 3) = 0) (hn : (n : ZMod 3) ≠ 0)
    (hcover : orderTwentyFiveKummerCoverClearedNumerator m n u v = 0) :
    (u : ZMod 3) = 0 ∨ (v : ZMod 3) = 0 := by
  have hmod :
      (orderTwentyFiveKummerCoverClearedNumerator m n u v : ZMod 3) = 0 := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hcover
  have hformula :
      (orderTwentyFiveKummerCoverClearedNumerator m n u v : ZMod 3) =
        -((n : ZMod 3) ^ 8 * (u : ZMod 3) ^ 2 *
          (v : ZMod 3) ^ 3) := by
    simp only [orderTwentyFiveKummerCoverClearedNumerator]
    push_cast
    rw [hm]
    ring
  rw [hformula] at hmod
  have hproduct :
      (n : ZMod 3) ^ 8 * (u : ZMod 3) ^ 2 *
          (v : ZMod 3) ^ 3 = 0 :=
    neg_eq_zero.mp hmod
  by_cases hu : (u : ZMod 3) = 0
  · exact Or.inl hu
  · right
    by_contra hv
    exact (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 8 hn) (pow_ne_zero 2 hu))
      (pow_ne_zero 3 hv)) hproduct

/-- For primitive root coordinates, the two alternatives in the first
modulo-three descent are mutually exclusive. -/
theorem orderTwentyFiveKummerCoverClearedNumerator_primitive_mod_three
    (m n u v : ℤ) (huv : IsCoprime u v)
    (hm : (m : ZMod 3) = 0) (hn : (n : ZMod 3) ≠ 0)
    (hcover : orderTwentyFiveKummerCoverClearedNumerator m n u v = 0) :
    ((u : ZMod 3) = 0 ∧ (v : ZMod 3) ≠ 0) ∨
      ((u : ZMod 3) ≠ 0 ∧ (v : ZMod 3) = 0) := by
  have huv3 := huv.map (Int.castRingHom (ZMod 3))
  change IsCoprime (u : ZMod 3) (v : ZMod 3) at huv3
  rcases orderTwentyFiveKummerCoverClearedNumerator_mod_three
      m n u v hm hn hcover with hu | hv
  · left
    refine ⟨hu, ?_⟩
    intro hv
    rw [hu, hv] at huv3
    exact not_isCoprime_zero_zero huv3
  · right
    refine ⟨?_, hv⟩
    intro hu
    rw [hu, hv] at huv3
    exact not_isCoprime_zero_zero huv3

/-- Every noncuspidal rational point on the cover with a non-three-unit
parameter has primitive integer coordinates in the oriented chart.  This is
the exact arithmetic package consumed by the marked-point bridge below. -/
theorem orderTwentyFiveKummerCover_integralDescentData
    (k x : ℚ) (hk : k ≠ 0)
    (hkNotUnit : ¬orderTwentyFiveRatIsThreeUnit k)
    (hxZero : x ≠ 0) (hxOne : x ≠ 1)
    (hcover : orderTwentyFiveKummerCoverPolynomial k x = 0) :
    ∃ m n u v : ℤ,
      m ≠ 0 ∧ n ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      IsCoprime m n ∧ IsCoprime u v ∧
      (m : ZMod 3) = 0 ∧ (n : ZMod 3) ≠ 0 ∧
      (u : ℚ) / (v : ℚ) = x ∧ u ≠ v ∧
      orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) =
        orderTwentyFiveFifthPowerHauptmodul k ∧
      orderTwentyFiveKummerCoverClearedNumerator m n u v = 0 ∧
      (((u : ZMod 3) = 0 ∧ (v : ZMod 3) ≠ 0) ∨
        ((u : ZMod 3) ≠ 0 ∧ (v : ZMod 3) = 0)) := by
  obtain ⟨m, n, hmZero, hnZero, hmn, hm3, hn3, hhaupt, hroot⟩ :=
    orderTwentyFiveKummerCover_threeAdicOrientation
      k x hk hkNotUnit hcover
  have huZero : x.num ≠ 0 := Rat.num_ne_zero.mpr hxZero
  have hvZero : (x.den : ℤ) ≠ 0 := by
    exact_mod_cast x.den_nz
  have hxFraction :
      (x.num : ℚ) / ((x.den : ℤ) : ℚ) = x := by
    simpa only [Int.cast_natCast] using Rat.num_div_den x
  have huv : x.num ≠ (x.den : ℤ) := by
    intro huv
    apply hxOne
    calc
      x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := hxFraction.symm
      _ = ((x.den : ℤ) : ℚ) / ((x.den : ℤ) : ℚ) := by rw [huv]
      _ = 1 := div_self (by exact_mod_cast x.den_nz)
  have hrootFraction :
      orderTwentyFiveKummerCoverPolynomial
        ((m : ℚ) / (n : ℚ))
        ((x.num : ℚ) / ((x.den : ℤ) : ℚ)) = 0 := by
    rw [hxFraction]
    exact hroot
  have hcleared :=
    orderTwentyFiveKummerCoverClearedNumerator_eq_zero
      m n x.num (x.den : ℤ) hnZero hvZero hrootFraction
  have hsplit :=
    orderTwentyFiveKummerCoverClearedNumerator_primitive_mod_three
      m n x.num (x.den : ℤ) (Rat.isCoprime_num_den x)
      hm3 hn3 hcleared
  exact ⟨m, n, x.num, (x.den : ℤ), hmZero, hnZero,
    huZero, hvZero, hmn, Rat.isCoprime_num_den x, hm3, hn3,
    hxFraction, huv, hhaupt, hcleared, hsplit⟩

/-- A hypothetical generator-marked point of exact order twenty-five yields
the primitive, three-adically oriented integer equation used by the Kummer
descent.  It retains the modular Hauptmodul relation and the reciprocal
three-integrality condition. -/
theorem orderTwentyFive_integralKummerCover_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ m n u v : ℤ,
      m ≠ 0 ∧ n ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      IsCoprime m n ∧ IsCoprime u v ∧
      (m : ZMod 3) = 0 ∧ (n : ZMod 3) ≠ 0 ∧
      (u : ℚ) / (v : ℚ) = orderTwentyFiveBrunaultXZero b c ∧
      u ≠ v ∧
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) ∧
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ))) ∧
      orderTwentyFiveKummerCoverClearedNumerator m n u v = 0 ∧
      (((u : ZMod 3) = 0 ∧ (v : ZMod 3) ≠ 0) ∨
        ((u : ZMod 3) ≠ 0 ∧ (v : ZMod 3) = 0)) := by
  obtain ⟨k, hk, -, hkParameter, hkNotUnit, hreciprocal,
      hxZero, hxOne, hcover⟩ :=
    orderTwentyFive_kummerCover_of_marked_order
      b c hb h00 horder
  obtain ⟨m, n, u, v, hmZero, hnZero, huZero, hvZero,
      hmn, huv, hm3, hn3, hxFraction, huNeV, hhaupt,
      hcleared, hsplit⟩ :=
    orderTwentyFiveKummerCover_integralDescentData
      k (orderTwentyFiveBrunaultXZero b c) hk hkNotUnit
      hxZero hxOne hcover
  refine ⟨m, n, u, v, hmZero, hnZero, huZero, hvZero,
    hmn, huv, hm3, hn3, hxFraction, huNeV, ?_, ?_,
    hcleared, hsplit⟩
  · calc
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
          orderTwentyFiveFifthPowerHauptmodul k := hkParameter
      _ = orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) := hhaupt.symm
  · simpa only [hhaupt] using hreciprocal

end MazurTorsion.Kubert
