/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerDeckTransform
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The 3-adic Newton polygon of Lehmer's order-twenty-five quintic

For an oriented Kummer parameter of positive 3-adic valuation \(a\), the
pulled-back Lehmer parameter has valuation \(-a\).  This file computes the
valuations of Lehmer's coefficients and proves directly, using the
ultrametric inequality, that every rational root has valuation
\(3a\), \(a\), \(-a\), or \(-2a\).

The final theorem is the marked-point consumer.  It uses one common oriented
parameter and one common positive scale for all five cyclic deck iterates,
while retaining the Hauptmodul and reciprocal-integrality data needed by the
global Kummer descent.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

private theorem val_add_eq_left_of_lt
    (q r : ℚ) (hq : q ≠ 0)
    (hval : padicValRat 3 q < padicValRat 3 r) :
    q + r ≠ 0 ∧ padicValRat 3 (q + r) = padicValRat 3 q := by
  by_cases hr : r = 0
  · simp [hr, hq]
  · have hsum : q + r ≠ 0 := by
      intro hzero
      have hneg : r = -q := eq_neg_of_add_eq_zero_right hzero
      rw [hneg, padicValRat.neg] at hval
      exact (lt_irrefl _ hval)
    exact ⟨hsum, padicValRat.add_eq_of_lt hsum hq hr hval⟩

private theorem val_nat_mul_pow
    (c : ℚ) (n : ℚ) (j : ℕ) (hc : c ≠ 0) (hn : n ≠ 0) :
    padicValRat 3 (c * n ^ j) =
      padicValRat 3 c + j * padicValRat 3 n := by
  rw [padicValRat.mul hc (pow_ne_zero j hn), padicValRat.pow]

private theorem val_int_unit (z : ℤ) (hz : ¬(3 : ℤ) ∣ z) :
    padicValRat 3 (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  norm_num

/-- When the Lehmer parameter has valuation `-a < 0`, its four
nonconstant, nonmonic coefficients have valuations prescribed by the lower
Newton polygon. -/
theorem orderTwentyFiveLehmerCoefficient_threeAdicValuations
    (n : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a) :
    padicValRat 3 (-n ^ 2) = -2 * a ∧
      padicValRat 3
        (2 * (n ^ 3 - 3 * n ^ 2 + 5 * n - 5)) = -3 * a ∧
      padicValRat 3
        (-(n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5)) =
          -4 * a ∧
      padicValRat 3 (-n ^ 3 + 4 * n ^ 2 - 10 * n + 10) =
          -3 * a := by
  have hn0 : n ≠ 0 := by
    intro hnz
    rw [hnz, padicValRat.zero] at hn
    omega
  have hpow (j : ℕ) :
      padicValRat 3 (n ^ j) = -(j : ℤ) * a := by
    rw [padicValRat.pow, hn]
    ring
  have hv2 : padicValRat 3 (2 : ℚ) = 0 :=
    val_int_unit 2 (by norm_num)
  have hv3 : padicValRat 3 (3 : ℚ) = 1 := by
    change padicValRat 3 ((3 : ℤ) : ℚ) = 1
    rw [padicValRat.of_int]
    exact_mod_cast (padicValInt_self (p := 3))
  have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
    val_int_unit 4 (by norm_num)
  have hv5 : padicValRat 3 (5 : ℚ) = 0 :=
    val_int_unit 5 (by norm_num)
  have hv10 : padicValRat 3 (10 : ℚ) = 0 :=
    val_int_unit 10 (by norm_num)
  have hv11 : padicValRat 3 (11 : ℚ) = 0 :=
    val_int_unit 11 (by norm_num)
  have hv15 : padicValRat 3 (15 : ℚ) = 1 := by
    rw [show (15 : ℚ) = 3 * 5 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv5]
    norm_num
  have hmul (c : ℚ) (j : ℕ) (hc : c ≠ 0) :
      padicValRat 3 (c * n ^ j) =
        padicValRat 3 c - (j : ℤ) * a := by
    rw [val_nat_mul_pow c n j hc hn0, hn]
    ring
  have hc4 : padicValRat 3 (-n ^ 2) = -2 * a := by
    rw [padicValRat.neg, hpow]
    norm_num
  have h3p0 : padicValRat 3 (n ^ 3) = -3 * a := by
    simpa using hpow 3
  have h3p1 : padicValRat 3 (-(3 * n ^ 2)) = 1 - 2 * a := by
    rw [padicValRat.neg, hmul 3 2 (by norm_num), hv3]
    norm_num
  have h3p2 : padicValRat 3 (5 * n) = -a := by
    rw [padicValRat.mul (by norm_num) hn0, hv5, hn]
    omega
  have h3p3 : padicValRat 3 (-5 : ℚ) = 0 := by
    rw [padicValRat.neg, hv5]
  have h3s1 := val_add_eq_left_of_lt (n ^ 3) (-(3 * n ^ 2))
    (pow_ne_zero 3 hn0) (by rw [h3p0, h3p1]; omega)
  have h3s2 := val_add_eq_left_of_lt
    (n ^ 3 + -(3 * n ^ 2)) (5 * n) h3s1.1
    (by rw [h3s1.2, h3p0, h3p2]; omega)
  have h3s3 := val_add_eq_left_of_lt
    (n ^ 3 + -(3 * n ^ 2) + 5 * n) (-5) h3s2.1
    (by rw [h3s2.2, h3s1.2, h3p0, h3p3]; omega)
  have h3inner :
      padicValRat 3 (n ^ 3 - 3 * n ^ 2 + 5 * n - 5) =
        -3 * a := by
    calc
      padicValRat 3 (n ^ 3 - 3 * n ^ 2 + 5 * n - 5) =
          padicValRat 3 (n ^ 3 + -(3 * n ^ 2) + 5 * n + -5) := by
            congr 1
            ring
      _ = padicValRat 3 (n ^ 3 + -(3 * n ^ 2) + 5 * n) := h3s3.2
      _ = padicValRat 3 (n ^ 3 + -(3 * n ^ 2)) := h3s2.2
      _ = padicValRat 3 (n ^ 3) := h3s1.2
      _ = -3 * a := h3p0
  have h3inner0 : n ^ 3 - 3 * n ^ 2 + 5 * n - 5 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at h3inner
    omega
  have hc3 :
      padicValRat 3 (2 * (n ^ 3 - 3 * n ^ 2 + 5 * n - 5)) =
        -3 * a := by
    rw [padicValRat.mul (by norm_num) h3inner0, hv2, h3inner]
    omega
  have h2p0 : padicValRat 3 (n ^ 4) = -4 * a := by
    simpa using hpow 4
  have h2p1 : padicValRat 3 (-(5 * n ^ 3)) = -3 * a := by
    rw [padicValRat.neg, hmul 5 3 (by norm_num), hv5]
    omega
  have h2p2 : padicValRat 3 (11 * n ^ 2) = -2 * a := by
    rw [hmul 11 2 (by norm_num), hv11]
    omega
  have h2p3 : padicValRat 3 (-(15 * n)) = 1 - a := by
    rw [padicValRat.neg, padicValRat.mul (by norm_num) hn0, hv15, hn]
    omega
  have h2p4 : padicValRat 3 (5 : ℚ) = 0 := hv5
  have h2s1 := val_add_eq_left_of_lt (n ^ 4) (-(5 * n ^ 3))
    (pow_ne_zero 4 hn0) (by rw [h2p0, h2p1]; omega)
  have h2s2 := val_add_eq_left_of_lt
    (n ^ 4 + -(5 * n ^ 3)) (11 * n ^ 2) h2s1.1
    (by rw [h2s1.2, h2p0, h2p2]; omega)
  have h2s3 := val_add_eq_left_of_lt
    (n ^ 4 + -(5 * n ^ 3) + 11 * n ^ 2) (-(15 * n)) h2s2.1
    (by rw [h2s2.2, h2s1.2, h2p0, h2p3]; omega)
  have h2s4 := val_add_eq_left_of_lt
    (n ^ 4 + -(5 * n ^ 3) + 11 * n ^ 2 + -(15 * n)) 5 h2s3.1
    (by rw [h2s3.2, h2s2.2, h2s1.2, h2p0, h2p4]; omega)
  have h2inner :
      padicValRat 3
          (n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5) =
        -4 * a := by
    calc
      padicValRat 3
          (n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5) =
          padicValRat 3
            (n ^ 4 + -(5 * n ^ 3) + 11 * n ^ 2 + -(15 * n) + 5) := by
              congr 1
              ring
      _ = padicValRat 3
          (n ^ 4 + -(5 * n ^ 3) + 11 * n ^ 2 + -(15 * n)) := h2s4.2
      _ = padicValRat 3
          (n ^ 4 + -(5 * n ^ 3) + 11 * n ^ 2) := h2s3.2
      _ = padicValRat 3 (n ^ 4 + -(5 * n ^ 3)) := h2s2.2
      _ = padicValRat 3 (n ^ 4) := h2s1.2
      _ = -4 * a := h2p0
  have hc2 :
      padicValRat 3
          (-(n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5)) =
        -4 * a := by
    rw [padicValRat.neg, h2inner]
  have h1p0 : padicValRat 3 (-n ^ 3) = -3 * a := by
    rw [padicValRat.neg, hpow]
    norm_num
  have h1p1 : padicValRat 3 (4 * n ^ 2) = -2 * a := by
    rw [hmul 4 2 (by norm_num), hv4]
    omega
  have h1p2 : padicValRat 3 (-(10 * n)) = -a := by
    rw [padicValRat.neg, padicValRat.mul (by norm_num) hn0, hv10, hn]
    omega
  have h1p3 : padicValRat 3 (10 : ℚ) = 0 := hv10
  have h1s1 := val_add_eq_left_of_lt (-n ^ 3) (4 * n ^ 2)
    (neg_ne_zero.mpr (pow_ne_zero 3 hn0)) (by rw [h1p0, h1p1]; omega)
  have h1s2 := val_add_eq_left_of_lt
    (-n ^ 3 + 4 * n ^ 2) (-(10 * n)) h1s1.1
    (by rw [h1s1.2, h1p0, h1p2]; omega)
  have h1s3 := val_add_eq_left_of_lt
    (-n ^ 3 + 4 * n ^ 2 + -(10 * n)) 10 h1s2.1
    (by rw [h1s2.2, h1s1.2, h1p0, h1p3]; omega)
  have hc1 :
      padicValRat 3 (-n ^ 3 + 4 * n ^ 2 - 10 * n + 10) =
        -3 * a := by
    calc
      padicValRat 3 (-n ^ 3 + 4 * n ^ 2 - 10 * n + 10) =
          padicValRat 3 (-n ^ 3 + 4 * n ^ 2 + -(10 * n) + 10) := by
            congr 1
            ring
      _ = padicValRat 3 (-n ^ 3 + 4 * n ^ 2 + -(10 * n)) := h1s3.2
      _ = padicValRat 3 (-n ^ 3 + 4 * n ^ 2) := h1s2.2
      _ = padicValRat 3 (-n ^ 3) := h1s1.2
      _ = -3 * a := h1p0
  exact ⟨hc4, hc3, hc2, hc1⟩

private theorem six_term_sum_ne_zero_of_first_strictly_small
    (q0 q1 q2 q3 q4 q5 : ℚ) (hq0 : q0 ≠ 0)
    (h01 : padicValRat 3 q0 < padicValRat 3 q1)
    (h02 : padicValRat 3 q0 < padicValRat 3 q2)
    (h03 : padicValRat 3 q0 < padicValRat 3 q3)
    (h04 : padicValRat 3 q0 < padicValRat 3 q4)
    (h05 : padicValRat 3 q0 < padicValRat 3 q5) :
    q0 + q1 + q2 + q3 + q4 + q5 ≠ 0 := by
  obtain ⟨hs1, hv1⟩ := val_add_eq_left_of_lt q0 q1 hq0 h01
  obtain ⟨hs2, hv2⟩ := val_add_eq_left_of_lt (q0 + q1) q2 hs1 (by
    rw [hv1]
    exact h02)
  obtain ⟨hs3, hv3⟩ := val_add_eq_left_of_lt (q0 + q1 + q2) q3 hs2 (by
    rw [hv2, hv1]
    exact h03)
  obtain ⟨hs4, hv4⟩ := val_add_eq_left_of_lt
    (q0 + q1 + q2 + q3) q4 hs3 (by
      rw [hv3, hv2, hv1]
      exact h04)
  exact (val_add_eq_left_of_lt
    (q0 + q1 + q2 + q3 + q4) q5 hs4 (by
      rw [hv4, hv3, hv2, hv1]
      exact h05)).1

/-- A positive-valuation Kummer parameter gives a negative-valuation
Lehmer parameter.  The term `-1 / k` is uniquely dominant in the pulled-back
Hauptmodul. -/
theorem orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation
    (k : ℚ) (a : ℤ) (ha : 0 < a)
    (hk : padicValRat 3 k = a) :
    padicValRat 3 (-orderTwentyFiveFifthPowerHauptmodul k) = -a := by
  have hk0 : k ≠ 0 := by
    intro hkz
    rw [hkz, padicValRat.zero] at hk
    omega
  let q : ℚ := -(1 / k)
  have hq0 : q ≠ 0 := by simp [q, hk0]
  have hq : padicValRat 3 q = -a := by
    simp only [q, padicValRat.neg, one_div, padicValRat.inv, hk]
  have hvOne : padicValRat 3 (-1 : ℚ) = 0 := by simp
  obtain ⟨hs1, hv1⟩ := val_add_eq_left_of_lt q k hq0 (by
    rw [hq, hk]
    omega)
  obtain ⟨-, hv2⟩ := val_add_eq_left_of_lt (q + k) (-1) hs1 (by
    rw [hv1, hq, hvOne]
    omega)
  rw [orderTwentyFiveFifthPowerHauptmodul, padicValRat.neg]
  calc
    padicValRat 3 (k - 1 / k - 1) = padicValRat 3 (q + k + -1) := by
      congr 1
      dsimp only [q]
      ring
    _ = padicValRat 3 (q + k) := hv2
    _ = padicValRat 3 q := hv1
    _ = -a := hq

/-- A nonzero integer fraction whose numerator, but not denominator,
vanishes modulo three has strictly positive 3-adic valuation. -/
theorem orderTwentyFiveOrientedFraction_threeAdicValuation
    (m n : ℤ) (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (hm3 : (m : ZMod 3) = 0) (hn3 : (n : ZMod 3) ≠ 0) :
    ∃ a : ℤ, 0 < a ∧
      padicValRat 3 ((m : ℚ) / (n : ℚ)) = a := by
  have hmDvd : (3 : ℤ) ∣ m :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd m 3).mp hm3
  have hnDvd : ¬(3 : ℤ) ∣ n := by
    intro hdiv
    exact hn3 ((ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mpr hdiv)
  have hmVal0 : padicValInt 3 m ≠ 0 := by
    intro hzero
    rcases (padicValInt.eq_zero_iff.mp hzero) with hp | hm | hnot
    · norm_num at hp
    · exact hm0 hm
    · exact hnot hmDvd
  let a : ℤ := padicValInt 3 m
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast Nat.pos_of_ne_zero hmVal0
  refine ⟨a, ha, ?_⟩
  have hmRat : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hnRat : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  rw [padicValRat.div hmRat hnRat, padicValRat.of_int,
    padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnDvd]
  simp [a]

private theorem orderTwentyFiveLehmer_root_threeAdicValuation_aux (n x : ℚ) (a z : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hz : padicValRat 3 x = z)
    (hx : orderTwentyFiveLehmerPolynomial n x = 0) :
    z = 3 * a ∨ z = a ∨ z = -a ∨ z = -2 * a := by
  have hn0 : n ≠ 0 := by
    intro hnz
    rw [hnz, padicValRat.zero] at hn
    omega
  have hx0 : x ≠ 0 := by
    intro hxz
    simp [orderTwentyFiveLehmerPolynomial, hxz] at hx
  have hcoeff := orderTwentyFiveLehmerCoefficient_threeAdicValuations n a ha hn
  have hc4 := hcoeff.1
  have hc3 := hcoeff.2.1
  have hc2 := hcoeff.2.2.1
  have hc1 := hcoeff.2.2.2
  let c4 : ℚ := -n ^ 2
  let c3 : ℚ := 2 * (n ^ 3 - 3 * n ^ 2 + 5 * n - 5)
  let c2 : ℚ :=
    -(n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5)
  let c1 : ℚ := -n ^ 3 + 4 * n ^ 2 - 10 * n + 10
  have hc4v : padicValRat 3 c4 = -2 * a := by simpa [c4] using hc4
  have hc3v : padicValRat 3 c3 = -3 * a := by simpa [c3] using hc3
  have hc2v : padicValRat 3 c2 = -4 * a := by simpa [c2] using hc2
  have hc1v : padicValRat 3 c1 = -3 * a := by simpa [c1] using hc1
  have hc4z : c4 ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hc4v
    omega
  have hc3z : c3 ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hc3v
    omega
  have hc2z : c2 ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hc2v
    omega
  have hc1z : c1 ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hc1v
    omega
  let t5 : ℚ := x ^ 5
  let t4 : ℚ := c4 * x ^ 4
  let t3 : ℚ := c3 * x ^ 3
  let t2 : ℚ := c2 * x ^ 2
  let t1 : ℚ := c1 * x
  let t0 : ℚ := -1
  have ht5 : padicValRat 3 t5 = 5 * z := by
    dsimp only [t5]
    rw [padicValRat.pow, hz]
    norm_num
  have ht4 : padicValRat 3 t4 = -2 * a + 4 * z := by
    dsimp only [t4]
    rw [padicValRat.mul hc4z (pow_ne_zero 4 hx0), hc4v,
      padicValRat.pow, hz]
    norm_num
  have ht3 : padicValRat 3 t3 = -3 * a + 3 * z := by
    dsimp only [t3]
    rw [padicValRat.mul hc3z (pow_ne_zero 3 hx0), hc3v,
      padicValRat.pow, hz]
    norm_num
  have ht2 : padicValRat 3 t2 = -4 * a + 2 * z := by
    dsimp only [t2]
    rw [padicValRat.mul hc2z (pow_ne_zero 2 hx0), hc2v,
      padicValRat.pow, hz]
    norm_num
  have ht1 : padicValRat 3 t1 = -3 * a + z := by
    dsimp only [t1]
    rw [padicValRat.mul hc1z hx0, hc1v, hz]
  have ht0 : padicValRat 3 t0 = 0 := by simp [t0]
  have ht5z : t5 ≠ 0 := by simp [t5, hx0]
  have ht4z : t4 ≠ 0 := mul_ne_zero hc4z (pow_ne_zero 4 hx0)
  have ht2z : t2 ≠ 0 := mul_ne_zero hc2z (pow_ne_zero 2 hx0)
  have ht1z : t1 ≠ 0 := mul_ne_zero hc1z hx0
  have ht0z : t0 ≠ 0 := by simp [t0]
  have hsum : t5 + t4 + t3 + t2 + t1 + t0 = 0 := by
    dsimp only [t5, t4, t3, t2, t1, t0, c4, c3, c2, c1]
    simp only [orderTwentyFiveLehmerPolynomial] at hx
    linear_combination hx
  by_cases hz3 : z = 3 * a
  · exact Or.inl hz3
  by_cases hz1 : z = a
  · exact Or.inr (Or.inl hz1)
  by_cases hzn1 : z = -a
  · exact Or.inr (Or.inr (Or.inl hzn1))
  by_cases hzn2 : z = -2 * a
  · exact Or.inr (Or.inr (Or.inr hzn2))
  by_cases hltN2 : z < -2 * a
  · exfalso
    exact (six_term_sum_ne_zero_of_first_strictly_small
      t5 t4 t3 t2 t1 t0 ht5z
      (by rw [ht5, ht4]; omega)
      (by rw [ht5, ht3]; omega)
      (by rw [ht5, ht2]; omega)
      (by rw [ht5, ht1]; omega)
      (by rw [ht5, ht0]; omega)) hsum
  by_cases hltN1 : z < -a
  · exfalso
    have hne := six_term_sum_ne_zero_of_first_strictly_small
      t4 t5 t3 t2 t1 t0 ht4z
      (by rw [ht4, ht5]; omega)
      (by rw [ht4, ht3]; omega)
      (by rw [ht4, ht2]; omega)
      (by rw [ht4, ht1]; omega)
      (by rw [ht4, ht0]; omega)
    apply hne
    calc
      t4 + t5 + t3 + t2 + t1 + t0 =
          t5 + t4 + t3 + t2 + t1 + t0 := by ring
      _ = 0 := hsum
  by_cases hlt1 : z < a
  · exfalso
    have hne := six_term_sum_ne_zero_of_first_strictly_small
      t2 t5 t4 t3 t1 t0 ht2z
      (by rw [ht2, ht5]; omega)
      (by rw [ht2, ht4]; omega)
      (by rw [ht2, ht3]; omega)
      (by rw [ht2, ht1]; omega)
      (by rw [ht2, ht0]; omega)
    apply hne
    calc
      t2 + t5 + t4 + t3 + t1 + t0 =
          t5 + t4 + t3 + t2 + t1 + t0 := by ring
      _ = 0 := hsum
  by_cases hlt3 : z < 3 * a
  · exfalso
    have hne := six_term_sum_ne_zero_of_first_strictly_small
      t1 t5 t4 t3 t2 t0 ht1z
      (by rw [ht1, ht5]; omega)
      (by rw [ht1, ht4]; omega)
      (by rw [ht1, ht3]; omega)
      (by rw [ht1, ht2]; omega)
      (by rw [ht1, ht0]; omega)
    apply hne
    calc
      t1 + t5 + t4 + t3 + t2 + t0 =
          t5 + t4 + t3 + t2 + t1 + t0 := by ring
      _ = 0 := hsum
  · exfalso
    have hne := six_term_sum_ne_zero_of_first_strictly_small
      t0 t5 t4 t3 t2 t1 ht0z
      (by rw [ht0, ht5]; omega)
      (by rw [ht0, ht4]; omega)
      (by rw [ht0, ht3]; omega)
      (by rw [ht0, ht2]; omega)
      (by rw [ht0, ht1]; omega)
    apply hne
    calc
      t0 + t5 + t4 + t3 + t2 + t1 =
          t5 + t4 + t3 + t2 + t1 + t0 := by ring
      _ = 0 := hsum

/-- A rational root of Lehmer's quintic at a parameter of valuation
`-a < 0` lies on one of the four slopes of its 3-adic Newton polygon. -/
theorem orderTwentyFiveLehmer_root_threeAdicValuation
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hx : orderTwentyFiveLehmerPolynomial n x = 0) :
    padicValRat 3 x = 3 * a ∨
      padicValRat 3 x = a ∨
      padicValRat 3 x = -a ∨
      padicValRat 3 x = -2 * a := by
  exact orderTwentyFiveLehmer_root_threeAdicValuation_aux n x a (padicValRat 3 x) ha hn rfl hx

/-- Pulling Lehmer's valuation alternatives back along the Kummer
parameter gives the four possible valuations of every cover root. -/
theorem orderTwentyFiveKummerCover_root_threeAdicValuation
    (k x : ℚ) (a : ℤ) (ha : 0 < a)
    (hk : padicValRat 3 k = a)
    (hx : orderTwentyFiveKummerCoverPolynomial k x = 0) :
    padicValRat 3 x = 3 * a ∨
      padicValRat 3 x = a ∨
      padicValRat 3 x = -a ∨
      padicValRat 3 x = -2 * a := by
  have hk0 : k ≠ 0 := by
    intro hkz
    rw [hkz, padicValRat.zero] at hk
    omega
  have hidentity :=
    orderTwentyFiveKummerCoverPolynomial_eq_clearedLehmer k x hk0
  rw [hidentity] at hx
  have hroot :
      orderTwentyFiveLehmerPolynomial
          (-orderTwentyFiveFifthPowerHauptmodul k) x = 0 :=
    (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 4 hk0)
  exact orderTwentyFiveLehmer_root_threeAdicValuation
    (-orderTwentyFiveFifthPowerHauptmodul k) x a ha
    (orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation k a ha hk) hroot

/-- Every cyclic deck iterate of a Kummer-cover root has one of the four
Newton-polygon valuations for the same positive integer `a`. -/
theorem orderTwentyFiveKummerCover_deckIterate_threeAdicValuation
    (j : ℕ) (k x : ℚ) (a : ℤ) (ha : 0 < a)
    (hk : padicValRat 3 k = a)
    (hx : orderTwentyFiveKummerCoverPolynomial k x = 0) :
    let y :=
      ((orderTwentyFiveLehmerDeckTransform
        (-orderTwentyFiveFifthPowerHauptmodul k))^[j] x)
    padicValRat 3 y = 3 * a ∨
      padicValRat 3 y = a ∨
      padicValRat 3 y = -a ∨
      padicValRat 3 y = -2 * a := by
  dsimp only
  have hk0 : k ≠ 0 := by
    intro hkz
    rw [hkz, padicValRat.zero] at hk
    omega
  exact orderTwentyFiveKummerCover_root_threeAdicValuation k _ a ha hk
    (orderTwentyFiveKummerCoverPolynomial_deckIterate j k x hk0 hx)

/-- A hypothetical generator-marked point of exact order twenty-five
supplies one oriented parameter and one positive valuation scale `a` for
which all five cyclic cover roots lie on the four Newton-polygon slopes.
The orbit Hauptmodul identity and reciprocal integrality condition are
retained for the global descent. -/
theorem orderTwentyFive_threeAdicRootValuations_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ IsCoprime m n ∧
      (m : ZMod 3) = 0 ∧ (n : ZMod 3) ≠ 0 ∧
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
      ∃ a : ℤ, 0 < a ∧
        padicValRat 3 ((m : ℚ) / (n : ℚ)) = a ∧
        ∀ j : Fin 5,
          let y :=
            ((orderTwentyFiveLehmerDeckTransform
              (-orderTwentyFiveFifthPowerHauptmodul
                ((m : ℚ) / (n : ℚ))))^[j.val]
              (orderTwentyFiveBrunaultXZero b c))
          padicValRat 3 y = 3 * a ∨
            padicValRat 3 y = a ∨
            padicValRat 3 y = -a ∨
            padicValRat 3 y = -2 * a := by
  obtain ⟨k, hk, -, hkParameter, hkNotUnit, hreciprocal,
      hxZero, -, hcover⟩ :=
    orderTwentyFive_kummerCover_of_marked_order b c hb h00 horder
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hhaupt, hroot⟩ :=
    orderTwentyFiveKummerCover_threeAdicOrientation
      k (orderTwentyFiveBrunaultXZero b c) hk hkNotUnit hcover
  obtain ⟨a, ha, hval⟩ :=
    orderTwentyFiveOrientedFraction_threeAdicValuation
      m n hm0 hn0 hm3 hn3
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, ?_, ?_, a, ha, hval, ?_⟩
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
  · intro j
    exact orderTwentyFiveKummerCover_deckIterate_threeAdicValuation
      j.val ((m : ℚ) / (n : ℚ))
      (orderTwentyFiveBrunaultXZero b c) a ha hval hroot

end MazurTorsion.Kubert
