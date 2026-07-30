/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/ForMathlib/PadicValNat.lean`).

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Order.Filter.AtTopBot.Tendsto

public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# The gap `n - v_p(n)` grows

The `p`-adic valuation (and, more crudely, `Nat.log p`) grows slower than the identity, so
`n - v_p(n) → ∞`. This is the coefficient-decay estimate behind convergence of the formal
logarithm on `(pO)^n`.
-/


open Filter

/-- `Nat.log` increases by at most one when its argument does. -/
theorem Nat.log_succ_le (b n : ℕ) : Nat.log b (n + 1) ≤ Nat.log b n + 1 := by
  by_cases hb : 1 < b
  · rcases Nat.eq_zero_or_pos (Nat.log b (n + 1)) with h0 | hL
    · lia
    set L := Nat.log b (n + 1) with hLdef
    have hpL : b ^ L ≤ n + 1 := Nat.pow_log_le_self b (Nat.succ_ne_zero n)
    have hone : 1 ≤ b ^ (L - 1) := Nat.one_le_pow _ _ (by lia)
    have h2 : 2 * b ^ (L - 1) ≤ b ^ L := by
      have he : b ^ L = b ^ (L - 1) * b := by rw [← pow_succ]; congr 1; lia
      rw [he, mul_comm]
      exact Nat.mul_le_mul_left _ hb
    have h4 : b ^ (L - 1) ≤ n := by lia
    have := Nat.le_log_of_pow_le hb h4
    lia
  · simp [Nat.log_of_left_le_one (by lia : b ≤ 1)]

/-- `n - Nat.log p n → ∞`: the base-`p` logarithm is sublinear. -/
theorem tendsto_sub_log_atTop {p : ℕ} (hp : 1 < p) :
    Tendsto (fun n ↦ n - Nat.log p n) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    have h1 : Nat.log p (n + 1) ≤ Nat.log p n + 1 := Nat.log_succ_le p n
    have h2 : Nat.log p n ≤ Nat.log p (n + 1) := Nat.log_mono_right (Nat.le_succ n)
    lia
  · intro B
    refine ⟨p ^ (B + 1), ?_⟩
    rw [Nat.log_pow hp]
    have hk : B + 1 ≤ 2 ^ B := Nat.lt_two_pow_self
    have h2 : 2 ^ (B + 1) ≤ p ^ (B + 1) := Nat.pow_le_pow_left (by lia) (B + 1)
    have h3 : 2 * (B + 1) ≤ 2 ^ (B + 1) := by rw [pow_succ]; lia
    lia

/-- `n - v_p(n) → ∞`: the `p`-adic valuation is sublinear. -/
theorem tendsto_sub_padicValNat_atTop {p : ℕ} (hp : 1 < p) :
    Tendsto (fun n ↦ n - padicValNat p n) atTop atTop :=
  tendsto_atTop_mono (fun n ↦ Nat.sub_le_sub_left (padicValNat_le_nat_log n) n)
    (tendsto_sub_log_atTop hp)

end
