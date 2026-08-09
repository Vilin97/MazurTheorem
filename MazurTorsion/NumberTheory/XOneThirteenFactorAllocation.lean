/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerBounds

/-!
# Pell factor allocation and bounds for the `X₁(13)` cover

This file records the complete integer two-adic split of the homogeneous Pell
factor halves and feeds the canonical power-split witnesses into the strict
fixed-cover bounds.
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

/-- A real fixed-cover consumer: feed the canonical homogeneous Pell power
split into the strict archimedean cover bounds. -/
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
    positive_pell_factor_power_split
      a b c hab hb hcurve hplus hminus
  have hbounds := pell_power_split_strict_bounds
    a b c r s ha hb hr hs hfactorPlus hfactorMinus hbSplit
  exact ⟨r, s, hr, hs, hrs, hfactorPlus, hfactorMinus, hbSplit,
    hbounds.1, hbounds.2.1, hbounds.2.2⟩

end MazurTorsion.XOneThirteenDescent
