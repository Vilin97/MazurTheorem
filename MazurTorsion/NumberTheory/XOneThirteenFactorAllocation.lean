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

The theorem here is independent of the parity argument that proves the Pell
halves are coprime.
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

end MazurTorsion.XOneThirteenDescent
