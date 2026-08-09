/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPositivePell

/-!
# Coprime power allocation for the `X₁(13)` Pell cover

This file isolates the unique-factorization step used after two positive
even factors have been divided by their forced scalar two. Positive coprime
factors whose product is a thirty-eighth power are themselves thirty-eighth
powers, with positive coprime roots whose product is the original base.

For the undivided factors, separation at the odd primes is not enough: the
checked counterexample `4 * 2^38 = 4 * 2^38` has no allocation on the first
factor. The theorem `thirtyEightPower_factor_allocation` therefore includes
the exact missing condition at two, namely that the two even factors are not
both divisible by four.
-/

namespace MazurTorsion.XOneThirteenDescent

/-- Positive coprime integral factors of a positive thirty-eighth power are
separately thirty-eighth powers, with positive coprime roots whose product is
the original base. -/
theorem positive_coprime_thirtyEightPower_allocation
    (u v b : ℤ) (hu : 0 < u) (hv : 0 < v) (hb : 0 < b)
    (hcop : IsCoprime u v) (hprod : u * v = b ^ 38) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ IsCoprime r s ∧
      u = r ^ 38 ∧ v = s ^ 38 ∧ b = r * s := by
  have hcopNat : u.natAbs.Coprime v.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcop
  have hprodNat : u.natAbs * v.natAbs = b.natAbs ^ 38 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using
      congrArg Int.natAbs hprod
  have hunitGcd : IsUnit (GCDMonoid.gcd u.natAbs v.natAbs) := by
    rw [show GCDMonoid.gcd u.natAbs v.natAbs = 1 from
      hcopNat.gcd_eq_one]
    exact isUnit_one
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hunitGcd hprodNat
  have hunitGcd' : IsUnit (GCDMonoid.gcd v.natAbs u.natAbs) := by
    rw [gcd_comm, show GCDMonoid.gcd u.natAbs v.natAbs = 1 from
      hcopNat.gcd_eq_one]
    exact isUnit_one
  obtain ⟨s, hs⟩ :=
    exists_eq_pow_of_mul_eq_pow hunitGcd'
      (mul_comm v.natAbs u.natAbs ▸ hprodNat)
  have hrPos : 0 < r := by
    by_contra hrZero
    have : r = 0 := Nat.eq_zero_of_not_pos hrZero
    rw [this, zero_pow (by norm_num : (38 : ℕ) ≠ 0)] at hr
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hu)) hr
  have hsPos : 0 < s := by
    by_contra hsZero
    have : s = 0 := Nat.eq_zero_of_not_pos hsZero
    rw [this, zero_pow (by norm_num : (38 : ℕ) ≠ 0)] at hs
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hv)) hs
  have hrsNat : r.Coprime s := by
    have hpowers : (r ^ 38).Coprime (s ^ 38) := by
      simpa only [← hr, ← hs] using hcopNat
    have hleft : r.Coprime (s ^ 38) :=
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 38) r (s ^ 38)).mp
        hpowers
    exact (Nat.coprime_pow_right_iff (by norm_num : 0 < 38) r s).mp
      hleft
  have hrsEq : r * s = b.natAbs := by
    apply Nat.pow_left_injective (by norm_num : (38 : ℕ) ≠ 0)
    change (r * s) ^ 38 = b.natAbs ^ 38
    rw [mul_pow, ← hr, ← hs, hprodNat]
  refine ⟨r, s, by exact_mod_cast hrPos, by exact_mod_cast hsPos, ?_, ?_, ?_, ?_⟩
  · apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hrsNat
  · have huCast : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu.le
    rw [← huCast, hr]
    norm_num
  · have hvCast : (v.natAbs : ℤ) = v := Int.natAbs_of_nonneg hv.le
    rw [← hvCast, hs]
    norm_num
  · have hbCast : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb.le
    rw [← hbCast, ← hrsEq]
    norm_num

/-- Odd-prime separation and evenness alone do not force the required power
allocation. Here `F = 4`, `G = 2^38`, and `b = 2` satisfy every hypothesis
of `thirtyEightPower_factor_allocation` except the two-adic separation, but
`F / 2 = 2` is not a thirty-eighth power. -/
theorem odd_prime_separated_even_factors_counterexample :
    0 < (4 : ℤ) ∧ 0 < (2 : ℤ) ^ 38 ∧ 0 < (2 : ℤ) ∧
      Even (4 : ℤ) ∧ Even ((2 : ℤ) ^ 38) ∧
      (4 : ℤ) * 2 ^ 38 = 4 * (2 : ℤ) ^ 38 ∧
      (∀ p : ℕ, p.Prime → Odd p →
        ¬((p : ℤ) ∣ (4 : ℤ) ∧ (p : ℤ) ∣ (2 : ℤ) ^ 38)) ∧
      ((4 : ℤ) ∣ (4 : ℤ) ∧ (4 : ℤ) ∣ (2 : ℤ) ^ 38) ∧
      ¬∃ r s : ℤ,
        0 < r ∧ 0 < s ∧ IsCoprime r s ∧
        (4 : ℤ) = 2 * r ^ 38 ∧
        (2 : ℤ) ^ 38 = 2 * s ^ 38 ∧ 2 = r * s := by
  refine ⟨by norm_num, by positivity, by norm_num, ⟨2, by norm_num⟩,
    ⟨2 ^ 37, by ring⟩, rfl, ?_, ⟨⟨1, by norm_num⟩, ⟨2 ^ 36, by ring⟩⟩, ?_⟩
  · intro p hp hpOdd
    rintro ⟨hpFour, _⟩
    have hpFourNat : p ∣ 4 := Int.natCast_dvd.mp hpFour
    have hpTwo : p ∣ 2 := by
      have hpMul : p ∣ 2 * 2 := by simpa using hpFourNat
      rcases hp.dvd_mul.mp hpMul with hpTwo | hpTwo
      · exact hpTwo
      · exact hpTwo
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpOne | rfl
    · exact hp.ne_one hpOne
    · exact Nat.not_even_iff_odd.mpr hpOdd (by decide)
  · rintro ⟨r, _s, hr, _hs, _hrs, hfactor, _⟩
    have hrPow : r ^ 38 = 2 := by nlinarith
    have hrDvd : r ∣ 2 := by
      refine ⟨r ^ 37, ?_⟩
      calc
        2 = r ^ 38 := hrPow.symm
        _ = r * r ^ 37 := by ring
    have hrUpper : r ≤ 2 := Int.le_of_dvd (by norm_num) hrDvd
    interval_cases r <;> norm_num at hrPow

/-- Exact factor allocation for two positive even integers. Odd primes are
excluded by `hodd`; the separate `htwo` branch says that after removing the
forced scalar two, the two halves do not retain a common factor two. Both
branches are used to prove coprimality before unique factorization is applied.
-/
theorem thirtyEightPower_factor_allocation
    (F G b : ℤ)
    (hF : 0 < F) (hG : 0 < G) (hb : 0 < b)
    (hFEven : Even F) (hGEven : Even G)
    (hprod : F * G = 4 * b ^ 38)
    (hodd : ∀ p : ℕ, p.Prime → Odd p →
      ¬((p : ℤ) ∣ F ∧ (p : ℤ) ∣ G))
    (htwo : ¬((4 : ℤ) ∣ F ∧ (4 : ℤ) ∣ G)) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ IsCoprime r s ∧
      F = 2 * r ^ 38 ∧ G = 2 * s ^ 38 ∧ b = r * s := by
  let u : ℤ := F / 2
  let v : ℤ := G / 2
  have huScale : 2 * u = F :=
    Int.two_mul_ediv_two_of_even hFEven
  have hvScale : 2 * v = G :=
    Int.two_mul_ediv_two_of_even hGEven
  have huPos : 0 < u :=
    Int.ediv_pos_of_pos_of_dvd hF (by norm_num)
      (even_iff_two_dvd.mp hFEven)
  have hvPos : 0 < v :=
    Int.ediv_pos_of_pos_of_dvd hG (by norm_num)
      (even_iff_two_dvd.mp hGEven)
  have huv : u * v = b ^ 38 := by
    apply Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    calc
      4 * (u * v) = (2 * u) * (2 * v) := by ring
      _ = F * G := by rw [huScale, hvScale]
      _ = 4 * b ^ 38 := hprod
  have hcopNat : u.natAbs.Coprime v.natAbs := by
    apply Nat.coprime_of_dvd
    intro p hp hpU hpV
    have hpUi : (p : ℤ) ∣ u := Int.natCast_dvd.mpr hpU
    have hpVi : (p : ℤ) ∣ v := Int.natCast_dvd.mpr hpV
    rcases hp.eq_two_or_odd' with rfl | hpOdd
    · apply htwo
      constructor
      · rcases hpUi with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [← huScale, hx]
        ring
      · rcases hpVi with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [← hvScale, hx]
        ring
    · apply hodd p hp hpOdd
      constructor
      · rw [← huScale]
        exact dvd_mul_of_dvd_right hpUi 2
      · rw [← hvScale]
        exact dvd_mul_of_dvd_right hpVi 2
  have hcop : IsCoprime u v :=
    Int.isCoprime_iff_nat_coprime.mpr hcopNat
  obtain ⟨r, s, hr, hs, hrs, huPow, hvPow, hbSplit⟩ :=
    positive_coprime_thirtyEightPower_allocation
      u v b huPos hvPos hb hcop huv
  refine ⟨r, s, hr, hs, hrs, ?_, ?_, hbSplit⟩
  · rw [← huScale, huPow]
  · rw [← hvScale, hvPow]

end MazurTorsion.XOneThirteenDescent
