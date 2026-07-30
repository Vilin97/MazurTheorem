/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Roots of unity in the rational numbers

The Weil pairing turns a full rational level structure on an elliptic curve into a primitive
rational root of unity. This file records the elementary ordered-field obstruction: a nonzero-order
root of unity in `ℚ` is `1` or `-1`, so a primitive one has order at most two.
-/

@[expose] public section

namespace MazurTorsion

/-- A rational number whose nonzero natural power is one equals `1` or `-1`. -/
theorem rat_eq_one_or_neg_one_of_pow_eq_one {q : ℚ} {n : ℕ} (hn : n ≠ 0)
    (hq : q ^ n = 1) : q = 1 ∨ q = -1 := by
  have habs_pow : |q| ^ n = 1 := by
    rw [← abs_pow, hq, abs_one]
  have habs : |q| = 1 :=
    (pow_eq_one_iff_of_nonneg (abs_nonneg q) hn).mp habs_pow
  exact eq_or_eq_neg_of_abs_eq habs

/-- A primitive root of unity in `ℚ` of nonzero order has order at most two. -/
theorem rational_primitiveRoot_order_le_two {q : ℚ} {n : ℕ} (hn : n ≠ 0)
    (hq : IsPrimitiveRoot q n) : n ≤ 2 := by
  have hq_sq : q ^ 2 = 1 := by
    rcases rat_eq_one_or_neg_one_of_pow_eq_one hn hq.pow_eq_one with h | h
    · simp [h]
    · simp [h]
  exact Nat.le_of_dvd (by omega) (hq.dvd_of_pow_eq_one 2 hq_sq)

end MazurTorsion
