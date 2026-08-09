/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCoprimePowerAllocation
import MazurTorsion.NumberTheory.XOneThirteenPellPowerBounds

/-!
# Pell factor allocation and bounds for the `X₁(13)` cover

This file specializes the lower coprime power-allocation interface to the
established homogeneous Pell factors. It proves the complete integer two-adic
split of their halves, allocates the two factors as scalar-two times positive
thirty-eighth powers, and feeds those witnesses into the strict fixed-cover
bounds.
-/

namespace MazurTorsion.XOneThirteenDescent

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
