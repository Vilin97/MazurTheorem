/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultIntegrality
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitValuation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# Three-adic valuations of the order-twenty-five Brunault orbit

This file connects the rational Lécacheux orbit equations to their
integer-linear tropicalization.  A vanishing sum of four nonzero rational
terms has a repeated least `p`-adic valuation.  Applying that fact to the
five cyclic equations, and applying additivity to the norm-one equation,
supplies exactly the hypotheses of the checked cusp-ray classifier.

The result does not exclude the nonzero cusp rays.  Its final consumer makes
the remaining arithmetic boundary precise: one valuation-zero orbit
coordinate would force all five coordinates to have valuation zero.
-/

namespace MazurTorsion.Kubert

/-- For a nonzero rational number, being a three-adic unit in the explicit
numerator/denominator sense used by the finite-field bridge is equivalent to
having three-adic valuation zero. -/
theorem orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero
    (q : ℚ) (hq : q ≠ 0) :
    orderTwentyFiveRatIsThreeUnit q ↔ padicValRat 3 q = 0 := by
  constructor
  · intro hunit
    have hnumNotDvd : ¬ (3 : ℤ) ∣ q.num := by
      intro hdiv
      exact hunit.2
        ((ZMod.intCast_zmod_eq_zero_iff_dvd q.num 3).mpr hdiv)
    have hdenNotDvd : ¬ 3 ∣ q.den := by
      intro hdiv
      exact hunit.1
        ((ZMod.natCast_eq_zero_iff q.den 3).mpr hdiv)
    rw [padicValRat_def,
      padicValInt.eq_zero_of_not_dvd hnumNotDvd,
      padicValNat.eq_zero_of_not_dvd hdenNotDvd]
    norm_num
  · intro hval
    have hvals : padicValInt 3 q.num = padicValNat 3 q.den := by
      have hvalsInt :
          (padicValInt 3 q.num : ℤ) = (padicValNat 3 q.den : ℤ) :=
        sub_eq_zero.mp (by simpa only [padicValRat_def] using hval)
      exact_mod_cast hvalsInt
    have hcoprime : IsCoprime q.num (q.den : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime]
      simpa using q.reduced
    have hcoprime3 := hcoprime.map (Int.castRingHom (ZMod 3))
    change IsCoprime (q.num : ZMod 3) (q.den : ZMod 3) at hcoprime3
    have hden3 : (q.den : ZMod 3) ≠ 0 := by
      intro hden0
      have hnum3 : (q.num : ZMod 3) ≠ 0 := by
        intro hnum0
        rw [hnum0, hden0] at hcoprime3
        exact not_isCoprime_zero_zero hcoprime3
      have hnumNotDvd : ¬ (3 : ℤ) ∣ q.num := by
        intro hdiv
        exact hnum3
          ((ZMod.intCast_zmod_eq_zero_iff_dvd q.num 3).mpr hdiv)
      have hnumVal : padicValInt 3 q.num = 0 :=
        padicValInt.eq_zero_of_not_dvd hnumNotDvd
      have hdenVal : padicValNat 3 q.den = 0 := hvals.symm.trans hnumVal
      have hdenDvd : 3 ∣ q.den :=
        (ZMod.natCast_eq_zero_iff q.den 3).mp hden0
      exact (dvd_iff_padicValNat_ne_zero q.den_ne_zero).mp hdenDvd hdenVal
    have hnum3 : (q.num : ZMod 3) ≠ 0 := by
      intro hnum0
      have hdenNotDvd : ¬ 3 ∣ q.den := by
        intro hdiv
        exact hden3 ((ZMod.natCast_eq_zero_iff q.den 3).mpr hdiv)
      have hdenVal : padicValNat 3 q.den = 0 :=
        padicValNat.eq_zero_of_not_dvd hdenNotDvd
      have hnumVal : padicValInt 3 q.num = 0 := hvals.trans hdenVal
      have hnumDvd : (3 : ℤ) ∣ q.num :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd q.num 3).mp hnum0
      have hnumValNe : padicValInt 3 q.num ≠ 0 := by
        rw [Ne, padicValInt.eq_zero_iff]
        simp [Rat.num_ne_zero.mpr hq, hnumDvd]
      exact hnumValNe hnumVal
    exact ⟨hden3, hnum3⟩

private theorem padicValRat_not_unique_min_four
    (p : ℕ) [Fact p.Prime]
    (q₀ q₁ q₂ q₃ : ℚ)
    (hq₀ : q₀ ≠ 0) (_hq₁ : q₁ ≠ 0) (_hq₂ : q₂ ≠ 0) (_hq₃ : q₃ ≠ 0)
    (hsum : q₀ + q₁ + q₂ + q₃ = 0)
    (h₀₁ : padicValRat p q₀ < padicValRat p q₁)
    (h₀₂ : padicValRat p q₀ < padicValRat p q₂)
    (h₀₃ : padicValRat p q₀ < padicValRat p q₃) :
    False := by
  by_cases hq₁₂ : q₁ + q₂ = 0
  · have hq₀₃ : q₀ + q₃ = 0 := by linarith
    have hq₃eq : q₃ = -q₀ := by linarith
    rw [hq₃eq, padicValRat.neg] at h₀₃
    exact (lt_irrefl _ h₀₃)
  · have h₀₁₂ :
        padicValRat p q₀ < padicValRat p (q₁ + q₂) :=
      lt_of_lt_of_le (lt_min h₀₁ h₀₂)
        (padicValRat.min_le_padicValRat_add hq₁₂)
    have hrest : (q₁ + q₂) + q₃ = -q₀ := by linarith
    have hrest0 : (q₁ + q₂) + q₃ ≠ 0 := by
      rw [hrest]
      exact neg_ne_zero.mpr hq₀
    have hlt := padicValRat.lt_add_of_lt hrest0 h₀₁₂ h₀₃
    rw [hrest, padicValRat.neg] at hlt
    exact (lt_irrefl _ hlt)

/-- In a vanishing sum of four nonzero rationals, the least `p`-adic
valuation occurs at least twice. -/
theorem orderTwentyFiveRepeatedMinFour_padicValRat
    (p : ℕ) [Fact p.Prime]
    (q₀ q₁ q₂ q₃ : ℚ)
    (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0) (hq₃ : q₃ ≠ 0)
    (hsum : q₀ + q₁ + q₂ + q₃ = 0) :
    orderTwentyFiveRepeatedMinFour
      (padicValRat p q₀) (padicValRat p q₁)
      (padicValRat p q₂) (padicValRat p q₃) := by
  have hmin :
      (padicValRat p q₀ ≤ padicValRat p q₁ ∧
          padicValRat p q₀ ≤ padicValRat p q₂ ∧
          padicValRat p q₀ ≤ padicValRat p q₃) ∨
        (padicValRat p q₁ ≤ padicValRat p q₀ ∧
          padicValRat p q₁ ≤ padicValRat p q₂ ∧
          padicValRat p q₁ ≤ padicValRat p q₃) ∨
        (padicValRat p q₂ ≤ padicValRat p q₀ ∧
          padicValRat p q₂ ≤ padicValRat p q₁ ∧
          padicValRat p q₂ ≤ padicValRat p q₃) ∨
        (padicValRat p q₃ ≤ padicValRat p q₀ ∧
          padicValRat p q₃ ≤ padicValRat p q₁ ∧
          padicValRat p q₃ ≤ padicValRat p q₂) := by
    omega
  rcases hmin with h₀ | h₁ | h₂ | h₃
  · by_cases h₀₁ : padicValRat p q₀ = padicValRat p q₁
    · exact Or.inl ⟨h₀₁, by omega, by omega⟩
    by_cases h₀₂ : padicValRat p q₀ = padicValRat p q₂
    · exact Or.inr (Or.inl ⟨h₀₂, by omega, by omega⟩)
    by_cases h₀₃ : padicValRat p q₀ = padicValRat p q₃
    · exact Or.inr (Or.inr (Or.inl ⟨h₀₃, by omega, by omega⟩))
    exact (padicValRat_not_unique_min_four p q₀ q₁ q₂ q₃
      hq₀ hq₁ hq₂ hq₃ hsum (by omega) (by omega) (by omega)).elim
  · by_cases h₁₀ : padicValRat p q₁ = padicValRat p q₀
    · exact Or.inl ⟨h₁₀.symm, by omega, by omega⟩
    by_cases h₁₂ : padicValRat p q₁ = padicValRat p q₂
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁₂, by omega, by omega⟩)))
    by_cases h₁₃ : padicValRat p q₁ = padicValRat p q₃
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h₁₃, by omega, by omega⟩))))
    exact (padicValRat_not_unique_min_four p q₁ q₀ q₂ q₃
      hq₁ hq₀ hq₂ hq₃ (by linarith)
      (by omega) (by omega) (by omega)).elim
  · by_cases h₂₀ : padicValRat p q₂ = padicValRat p q₀
    · exact Or.inr (Or.inl ⟨h₂₀.symm, by omega, by omega⟩)
    by_cases h₂₁ : padicValRat p q₂ = padicValRat p q₁
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h₂₁.symm, by omega, by omega⟩)))
    by_cases h₂₃ : padicValRat p q₂ = padicValRat p q₃
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h₂₃, by omega, by omega⟩))))
    exact (padicValRat_not_unique_min_four p q₂ q₀ q₁ q₃
      hq₂ hq₀ hq₁ hq₃ (by linarith)
      (by omega) (by omega) (by omega)).elim
  · by_cases h₃₀ : padicValRat p q₃ = padicValRat p q₀
    · exact Or.inr (Or.inr (Or.inl ⟨h₃₀.symm, by omega, by omega⟩))
    by_cases h₃₁ : padicValRat p q₃ = padicValRat p q₁
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h₃₁.symm, by omega, by omega⟩))))
    by_cases h₃₂ : padicValRat p q₃ = padicValRat p q₂
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h₃₂.symm, by omega, by omega⟩))))
    exact (padicValRat_not_unique_min_four p q₃ q₀ q₁ q₂
      hq₃ hq₀ hq₁ hq₂ (by linarith)
      (by omega) (by omega) (by omega)).elim

private theorem orderTwentyFiveOrbitRelationZero_repeatedMin
    (a b c d e : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h₀ : orderTwentyFiveOrbitRelationZero a b c d e = 0) :
    orderTwentyFiveRepeatedMinFour
      (padicValRat 3 a) (padicValRat 3 c)
      (padicValRat 3 a + padicValRat 3 b)
      (padicValRat 3 a + padicValRat 3 d) := by
  have hsum : a + (-c) + (-(a * b)) + a * d = 0 := by
    simp only [orderTwentyFiveOrbitRelationZero] at h₀
    linear_combination h₀
  have hrep := orderTwentyFiveRepeatedMinFour_padicValRat 3
    a (-c) (-(a * b)) (a * d) ha (neg_ne_zero.mpr hc)
    (neg_ne_zero.mpr (mul_ne_zero ha hb)) (mul_ne_zero ha hd) hsum
  simpa only [padicValRat.neg, padicValRat.mul ha hb,
    padicValRat.mul ha hd] using hrep

private theorem orderTwentyFiveOrbitRelationFive_valuation_sum
    (a b c d e : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    padicValRat 3 a + padicValRat 3 b + padicValRat 3 c +
        padicValRat 3 d + padicValRat 3 e = 0 := by
  have hproduct : a * b * c * d * e = 1 := by
    exact sub_eq_zero.mp h₅
  have hvaluation := congrArg (padicValRat 3) hproduct
  simpa only [padicValRat.mul ha hb, padicValRat.mul (mul_ne_zero ha hb) hc,
    padicValRat.mul (mul_ne_zero (mul_ne_zero ha hb) hc) hd,
    padicValRat.mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd) he,
    padicValRat.one, add_assoc] using hvaluation

/-- Five nonzero rational orbit coordinates satisfying Lécacheux's cyclic
relations and norm-one relation have either zero three-adic valuation vector
or one of the five checked cusp-ray valuation vectors. -/
theorem orderTwentyFiveOrbit_padicValuation_classification
    (a b c d e : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (h₀ : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h₁ : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h₂ : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h₃ : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h₄ : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    (padicValRat 3 a = 0 ∧ padicValRat 3 b = 0 ∧
        padicValRat 3 c = 0 ∧ padicValRat 3 d = 0 ∧
        padicValRat 3 e = 0) ∨
      ∃ t : ℤ, 0 < t ∧
        ((padicValRat 3 a = 3 * t ∧ padicValRat 3 b = -t ∧
            padicValRat 3 c = t ∧ padicValRat 3 d = -2 * t ∧
            padicValRat 3 e = -t) ∨
          (padicValRat 3 a = -t ∧ padicValRat 3 b = t ∧
            padicValRat 3 c = -2 * t ∧ padicValRat 3 d = -t ∧
            padicValRat 3 e = 3 * t) ∨
          (padicValRat 3 a = t ∧ padicValRat 3 b = -2 * t ∧
            padicValRat 3 c = -t ∧ padicValRat 3 d = 3 * t ∧
            padicValRat 3 e = -t) ∨
          (padicValRat 3 a = -2 * t ∧ padicValRat 3 b = -t ∧
            padicValRat 3 c = 3 * t ∧ padicValRat 3 d = -t ∧
            padicValRat 3 e = t) ∨
          (padicValRat 3 a = -t ∧ padicValRat 3 b = 3 * t ∧
            padicValRat 3 c = -t ∧ padicValRat 3 d = t ∧
            padicValRat 3 e = -2 * t)) := by
  have hrep₀ := orderTwentyFiveOrbitRelationZero_repeatedMin
    a b c d e ha hb hc hd h₀
  have hrep₁ := orderTwentyFiveOrbitRelationZero_repeatedMin
    b c d e a hb hc hd he h₁
  have hrep₂ := orderTwentyFiveOrbitRelationZero_repeatedMin
    c d e a b hc hd he ha h₂
  have hrep₃ := orderTwentyFiveOrbitRelationZero_repeatedMin
    d e a b c hd he ha hb h₃
  have hrep₄ := orderTwentyFiveOrbitRelationZero_repeatedMin
    e a b c d he ha hb hc h₄
  exact orderTwentyFiveOrbitValuation_classification
    (padicValRat 3 a) (padicValRat 3 b) (padicValRat 3 c)
    (padicValRat 3 d) (padicValRat 3 e)
    hrep₀ hrep₁ hrep₂ hrep₃ hrep₄
    (orderTwentyFiveOrbitRelationFive_valuation_sum
      a b c d e ha hb hc hd he h₅)

/-- Under the same rational orbit equations, one valuation-zero coordinate
excludes every nonzero cusp ray and forces all five coordinates to have
three-adic valuation zero. -/
theorem orderTwentyFiveOrbit_padicValuations_eq_zero_of_first_eq_zero
    (a b c d e : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (h₀ : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h₁ : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h₂ : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h₃ : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h₄ : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0)
    (haVal : padicValRat 3 a = 0) :
    padicValRat 3 a = 0 ∧ padicValRat 3 b = 0 ∧
      padicValRat 3 c = 0 ∧ padicValRat 3 d = 0 ∧
      padicValRat 3 e = 0 := by
  have hrep₀ := orderTwentyFiveOrbitRelationZero_repeatedMin
    a b c d e ha hb hc hd h₀
  have hrep₁ := orderTwentyFiveOrbitRelationZero_repeatedMin
    b c d e a hb hc hd he h₁
  have hrep₂ := orderTwentyFiveOrbitRelationZero_repeatedMin
    c d e a b hc hd he ha h₂
  have hrep₃ := orderTwentyFiveOrbitRelationZero_repeatedMin
    d e a b c hd he ha hb h₃
  have hrep₄ := orderTwentyFiveOrbitRelationZero_repeatedMin
    e a b c d he ha hb hc h₄
  exact orderTwentyFiveOrbitValuation_eq_zero_of_first_eq_zero
    (padicValRat 3 a) (padicValRat 3 b) (padicValRat 3 c)
    (padicValRat 3 d) (padicValRat 3 e)
    hrep₀ hrep₁ hrep₂ hrep₃ hrep₄
    (orderTwentyFiveOrbitRelationFive_valuation_sum
      a b c d e ha hb hc hd he h₅) haVal

/-- If one coordinate has valuation zero, the cyclic and norm-one equations
upgrade all five nonzero rational orbit coordinates to explicit three-adic
units.  In particular, every canonical reduction modulo three is defined and
nonzero. -/
theorem orderTwentyFiveOrbit_threeUnits_of_first_padicVal_eq_zero
    (a b c d e : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (h₀ : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h₁ : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h₂ : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h₃ : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h₄ : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0)
    (haVal : padicValRat 3 a = 0) :
    orderTwentyFiveRatIsThreeUnit a ∧
      orderTwentyFiveRatIsThreeUnit b ∧
      orderTwentyFiveRatIsThreeUnit c ∧
      orderTwentyFiveRatIsThreeUnit d ∧
      orderTwentyFiveRatIsThreeUnit e := by
  obtain ⟨haVal, hbVal, hcVal, hdVal, heVal⟩ :=
    orderTwentyFiveOrbit_padicValuations_eq_zero_of_first_eq_zero
      a b c d e ha hb hc hd he h₀ h₁ h₂ h₃ h₄ h₅ haVal
  exact
    ⟨(orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero a ha).mpr haVal,
      (orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero b hb).mpr hbVal,
      (orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero c hc).mpr hcVal,
      (orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero d hd).mpr hdVal,
      (orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero e he).mpr heVal⟩

end MazurTorsion.Kubert
