/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerBounds

/-!
# Unique-factorization allocation for the `X₁(13)` Pell cover

This file isolates the unique-factorization step used after the two positive
Pell factors have been divided by their forced scalar two.  Positive coprime
factors whose product is a thirty-eighth power are themselves thirty-eighth
powers, with positive coprime roots whose product is the original base.

For the undivided factors, separation at the odd primes is not enough: the
checked counterexample `4 * 2^38 = 4 * 2^38` has no allocation on the first
factor.  The theorem `thirtyEightPower_factor_allocation` therefore includes
the exact missing condition at two, namely that the two even factors are not
both divisible by four.  Its Pell specialization derives this condition from
the established primitive homogeneous parity and coprimality lemmas.
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
allocation.  Here `F = 4`, `G = 2^38`, and `b = 2` satisfy every hypothesis
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

/-- Exact factor allocation for two positive even integers.  Odd primes are
excluded by `hodd`; the separate `htwo` branch says that after removing the
forced scalar two, the two halves do not retain a common factor two.  Both
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

/-- After removing the forced scalar two, the two homogeneous Pell factors
have product exactly `b ^ 38`. -/
theorem positive_pell_half_factor_product
    (a b c : ℤ) (hab : IsCoprime a b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    (positivePellFactor a b c / 2) *
        (negativePellFactorMagnitude a b c / 2) = b ^ 38 := by
  have heven := positive_pell_factors_even a b c hab hcurve
  have huScale :
      2 * (positivePellFactor a b c / 2) =
        positivePellFactor a b c :=
    Int.two_mul_ediv_two_of_even heven.1
  have hvScale :
      2 * (negativePellFactorMagnitude a b c / 2) =
        negativePellFactorMagnitude a b c :=
    Int.two_mul_ediv_two_of_even heven.2
  apply Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
  calc
    4 * ((positivePellFactor a b c / 2) *
        (negativePellFactorMagnitude a b c / 2)) =
        (2 * (positivePellFactor a b c / 2)) *
          (2 * (negativePellFactorMagnitude a b c / 2)) := by ring
    _ = positivePellFactor a b c *
        negativePellFactorMagnitude a b c := by rw [huScale, hvScale]
    _ = 4 * b ^ 38 := positive_pell_factorization a b c hcurve

/-- Complete integer two-adic split of the positive Pell factors after the
forced scalar two is removed.  For odd `b`, both halves are odd.  For even
`b`, exactly one half is even; the hypotheses do not choose its orientation.
-/
theorem positive_pell_half_factors_two_adic_split
    (a b c : ℤ) (hab : IsCoprime a b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    (Odd b ∧ Odd (positivePellFactor a b c / 2) ∧
        Odd (negativePellFactorMagnitude a b c / 2)) ∨
      (Even b ∧
        ((Even (positivePellFactor a b c / 2) ∧
            Odd (negativePellFactorMagnitude a b c / 2)) ∨
          (Odd (positivePellFactor a b c / 2) ∧
            Even (negativePellFactorMagnitude a b c / 2)))) := by
  let u : ℤ := positivePellFactor a b c / 2
  let v : ℤ := negativePellFactorMagnitude a b c / 2
  have huv : u * v = b ^ 38 := by
    simpa only [u, v] using
      positive_pell_half_factor_product a b c hab hcurve
  have hcop : IsCoprime u v := by
    exact positive_pell_half_factors_isCoprime a b c hab hcurve
  rcases Int.even_or_odd b with hbEven | hbOdd
  · right
    refine ⟨hbEven, ?_⟩
    have huvEven : Even (u * v) := by
      rw [huv]
      exact Int.even_pow.mpr ⟨hbEven, by norm_num⟩
    rcases Int.even_mul.mp huvEven with huEven | hvEven
    · left
      refine ⟨huEven, Int.not_even_iff_odd.mp ?_⟩
      intro hvEven
      have hunit := hcop.isUnit_of_dvd'
        (even_iff_two_dvd.mp huEven) (even_iff_two_dvd.mp hvEven)
      exact Int.prime_two.not_unit hunit
    · right
      refine ⟨Int.not_even_iff_odd.mp ?_, hvEven⟩
      intro huEven
      have hunit := hcop.isUnit_of_dvd'
        (even_iff_two_dvd.mp huEven) (even_iff_two_dvd.mp hvEven)
      exact Int.prime_two.not_unit hunit
  · left
    have huvOdd : Odd (u * v) := by
      rw [huv]
      exact hbOdd.pow
    exact ⟨hbOdd, (Int.odd_mul.mp huvOdd).1,
      (Int.odd_mul.mp huvOdd).2⟩

/-- The abstract allocation theorem specialized to the established
homogeneous `X₁(13)` Pell factors.  The odd-prime hypothesis comes from
primitive prime support, while the full prime-two case comes from the checked
coprimality of the two halves.  Unlike
`positive_pell_factor_power_split`, its proof factors through the abstract
odd/prime-two allocation interface above. -/
theorem positive_pell_factor_allocation
    (a b c : ℤ) (hab : IsCoprime a b) (hb : 0 < b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b)
    (hplus : 0 < positivePellFactor a b c)
    (hminus : 0 < negativePellFactorMagnitude a b c) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ IsCoprime r s ∧
      positivePellFactor a b c = 2 * r ^ 38 ∧
      negativePellFactorMagnitude a b c = 2 * s ^ 38 ∧
      b = r * s := by
  have heven := positive_pell_factors_even a b c hab hcurve
  have htwoSplit :=
    positive_pell_half_factors_two_adic_split a b c hab hcurve
  apply thirtyEightPower_factor_allocation
    (positivePellFactor a b c) (negativePellFactorMagnitude a b c) b
    hplus hminus hb heven.1 heven.2
    (positive_pell_factorization a b c hcurve)
  · intro p hp hpOdd
    apply odd_prime_not_common_pell_factor
      a b c p hab (Nat.prime_iff_prime_int.mp hp)
    · intro hpTwo
      have hpTwoNat : p ∣ 2 := by exact_mod_cast hpTwo
      rcases (Nat.dvd_prime Nat.prime_two).mp hpTwoNat with hpOne | rfl
      · exact hp.ne_one hpOne
      · exact Nat.not_even_iff_odd.mpr hpOdd (by decide)
    · exact hcurve
  · rintro ⟨hfourPlus, hfourMinus⟩
    have htwoPlus : (2 : ℤ) ∣ positivePellFactor a b c / 2 := by
      rcases hfourPlus with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
      rw [Int.two_mul_ediv_two_of_even heven.1, hk]
      ring
    have htwoMinus : (2 : ℤ) ∣
        negativePellFactorMagnitude a b c / 2 := by
      rcases hfourMinus with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
      rw [Int.two_mul_ediv_two_of_even heven.2, hk]
      ring
    have hplusEven : Even (positivePellFactor a b c / 2) :=
      even_iff_two_dvd.mpr htwoPlus
    have hminusEven : Even (negativePellFactorMagnitude a b c / 2) :=
      even_iff_two_dvd.mpr htwoMinus
    rcases htwoSplit with ⟨_, hplusOdd, _⟩ | ⟨_, hparity⟩
    · exact Int.not_even_iff_odd.mpr hplusOdd hplusEven
    · rcases hparity with ⟨_, hminusOdd⟩ | ⟨hplusOdd, _⟩
      · exact Int.not_even_iff_odd.mpr hminusOdd hminusEven
      · exact Int.not_even_iff_odd.mpr hplusOdd hplusEven

/-- A real fixed-cover consumer: allocate the homogeneous Pell factors and
immediately feed the resulting coordinates into the strict archimedean cover
bounds. -/
theorem positive_pell_factor_allocation_strict_bounds
    (a b c : ℤ) (hab : IsCoprime a b)
    (ha : 0 < a) (hb : 0 < b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b)
    (hplus : 0 < positivePellFactor a b c)
    (hminus : 0 < negativePellFactorMagnitude a b c) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ IsCoprime r s ∧
      positivePellFactor a b c = 2 * r ^ 38 ∧
      negativePellFactorMagnitude a b c = 2 * s ^ 38 ∧
      b = r * s ∧
      s < r ∧ a < r ^ 2 ∧ r ^ 2 < a + b := by
  obtain ⟨r, s, hr, hs, hrs, hfactorPlus, hfactorMinus, hbSplit⟩ :=
    positive_pell_factor_allocation
      a b c hab hb hcurve hplus hminus
  have hbounds := pell_power_split_strict_bounds
    a b c r s ha hb hr hs hfactorPlus hfactorMinus hbSplit
  exact ⟨r, s, hr, hs, hrs, hfactorPlus, hfactorMinus, hbSplit,
    hbounds.1, hbounds.2.1, hbounds.2.2⟩

end MazurTorsion.XOneThirteenDescent
