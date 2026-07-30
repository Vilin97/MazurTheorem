/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in PORTING.md.
-/
module

public import EllipticCurves.WeierstrassFormalGroup.Eval
import all EllipticCurves.WeierstrassFormalGroup.Eval

@[expose] public section

/-!
# Valuation estimates for the integral model of a Weierstrass curve

This file specializes the formal-group evaluation layer to `O = 𝒪_v` (the valuation ring of an
adic completion) and collects the technical estimates on which the geometric results rest: the
valuation-integrality bookkeeping for the coordinates and coefficients of an integral model, the
parameter-level vanishing of torsion in the kernel of reduction (`points_eq_zero_of_nsmul_*`, via
the scaled formal logarithm), and the compactness and finite-quotient facts used downstream for
the finite-index statements.
-/

open ChabautyColeman IsLocalRing MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
  {t : v.adicCompletionIntegers K}

private lemma algebraMap_eq_coe (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x =
      (x : v.adicCompletion K) := rfl

private lemma valued_coe_le_one (x : v.adicCompletionIntegers K) :
    Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 := x.2

/-- The valuation of (the coercion of) a unit of `𝒪_v` is `1`. -/
private lemma valued_coe_isUnit {a : v.adicCompletionIntegers K} (ha : IsUnit a) :
    Valued.v ((a : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
  (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp ha

/-- Membership in the maximal ideal of `𝒪_v` is the valuation bound `exp (-1)`. -/
private lemma mem_maximalIdeal_iff {x : v.adicCompletionIntegers K} :
    x ∈ maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v ((x : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ exp (-1 : ℤ) := by
  have h := mem_maximalIdeal_pow_iff (K := K) (x := x) (n := 1)
  rwa [pow_one] at h

/-- An element within distance `exp (-n)` of an integral element is integral. -/
private lemma valued_le_one_of_sub {a b : v.adicCompletion K} {n : ℕ}
    (h : Valued.v (a - b) ≤ exp (-(n : ℤ))) (hb : Valued.v b ≤ 1) : Valued.v a ≤ 1 := by
  rw [show a = (a - b) + b by ring]
  refine le_trans (Valued.v.map_add _ _) (max_le (h.trans ?_) hb)
  rw [← exp_zero, exp_le_exp]
  lia

private lemma coe_wEval_ne_zero {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (h0 : t ≠ 0) :
    ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact W₀.wEval_ne_zero hm h0

private lemma coe_duEval_ne_zero {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact (W₀.isUnit_duEval hm).ne_zero

private lemma valued_lhs_eq_rhs {x y : v.adicCompletion K} (hxy : W.Equation x y) :
    Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) =
      Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) :=
  congrArg Valued.v (by linear_combination (W.equation_iff x y).mp hxy)

private lemma coe_iotaEval_eq {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.iotaEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      -((t : v.adicCompletion K) *
        ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.iotaEval_eq hm)
  push_cast at h
  exact h

private lemma coe_wEval_iotaEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.wEval (W₀.iotaEval t) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      -(((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_iotaEval hm)
  push_cast at h
  exact h

private lemma coe_uEval_mul_duEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.uEval t : v.adicCompletionIntegers K) : v.adicCompletion K) *
      ((W₀.duEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.uEval_mul_duEval hm)
  push_cast at h
  exact h

section

include hW

private lemma coe_a₁ : ((W₀.a₁ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₁ := by
  rw [← hW, WeierstrassCurve.map_a₁, algebraMap_eq_coe]

private lemma coe_a₂ : ((W₀.a₂ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₂ := by
  rw [← hW, WeierstrassCurve.map_a₂, algebraMap_eq_coe]

private lemma coe_a₃ : ((W₀.a₃ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₃ := by
  rw [← hW, WeierstrassCurve.map_a₃, algebraMap_eq_coe]

private lemma coe_a₄ : ((W₀.a₄ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₄ := by
  rw [← hW, WeierstrassCurve.map_a₄, algebraMap_eq_coe]

private lemma coe_a₆ : ((W₀.a₆ : v.adicCompletionIntegers K) : v.adicCompletion K) = W.a₆ := by
  rw [← hW, WeierstrassCurve.map_a₆, algebraMap_eq_coe]

lemma valued_a₁ : Valued.v W.a₁ ≤ 1 := coe_a₁ hW ▸ valued_coe_le_one W₀.a₁
lemma valued_a₂ : Valued.v W.a₂ ≤ 1 := coe_a₂ hW ▸ valued_coe_le_one W₀.a₂
lemma valued_a₃ : Valued.v W.a₃ ≤ 1 := coe_a₃ hW ▸ valued_coe_le_one W₀.a₃
lemma valued_a₄ : Valued.v W.a₄ ≤ 1 := coe_a₄ hW ▸ valued_coe_le_one W₀.a₄
private lemma valued_a₆ : Valued.v W.a₆ ≤ 1 := coe_a₆ hW ▸ valued_coe_le_one W₀.a₆

/-- For `v(x) > 1`, the right-hand side of the Weierstrass equation has valuation `v(x)³`. -/
private lemma valued_rhs_eq {x : v.adicCompletion K} (hA1 : 1 < Valued.v x) :
    Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = Valued.v x ^ 3 := by
  set A := Valued.v x
  have h1 : Valued.v (W.a₂ * x ^ 2) ≤ A ^ 2 := by
    rw [map_mul, map_pow]
    exact (mul_le_mul' (valued_a₂ hW) le_rfl).trans_eq (one_mul _)
  have h2 : Valued.v (W.a₄ * x) ≤ A ^ 2 := by
    rw [map_mul]
    exact ((mul_le_mul' (valued_a₄ hW) le_rfl).trans_eq (one_mul _)).trans
      (le_self_pow hA1.le (by lia))
  have h3 : Valued.v W.a₆ ≤ A ^ 2 :=
    (valued_a₆ hW).trans (hA1.le.trans (le_self_pow hA1.le (by lia)))
  have hlow : Valued.v (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) < A ^ 3 :=
    lt_of_le_of_lt ((Valued.v.map_add _ _).trans
      (max_le h1 ((Valued.v.map_add _ _).trans (max_le h2 h3))))
      (pow_lt_pow_right₀ hA1 (by lia))
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hlow), map_pow]

/-- For integral `x`, the right-hand side of the Weierstrass equation is integral. -/
private lemma valued_rhs_le {x : v.adicCompletion K} (hA1 : Valued.v x ≤ 1) :
    Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) ≤ 1 := by
  refine le_trans (Valued.v.map_add _ _) (max_le ?_ (le_trans (Valued.v.map_add _ _)
    (max_le ?_ (le_trans (Valued.v.map_add _ _) (max_le ?_ (valued_a₆ hW))))))
  · rw [map_pow]
    exact pow_le_one' hA1 3
  · rw [map_mul, map_pow]
    exact mul_le_one' (valued_a₂ hW) (pow_le_one' hA1 2)
  · rw [map_mul]
    exact mul_le_one' (valued_a₄ hW) hA1

/-- When `v(y)` dominates `v(x)` and exceeds `1`, the left-hand side of the Weierstrass
equation has valuation `v(y)²`. -/
private lemma valued_lhs_eq {x y : v.adicCompletion K} (hAB : Valued.v x < Valued.v y)
    (hB1 : 1 < Valued.v y) :
    Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) = Valued.v y ^ 2 := by
  set B := Valued.v y
  have h2 : Valued.v (W.a₁ * x * y) < B ^ 2 := by
    rw [map_mul, map_mul]
    calc Valued.v W.a₁ * Valued.v x * B ≤ 1 * Valued.v x * B :=
        mul_le_mul' (mul_le_mul' (valued_a₁ hW) le_rfl) le_rfl
      _ = Valued.v x * B := by rw [one_mul]
      _ < B * B := mul_lt_mul_of_pos_right hAB (zero_lt_one.trans hB1)
      _ = B ^ 2 := (sq B).symm
  have h3 : Valued.v (W.a₃ * y) < B ^ 2 := by
    rw [map_mul]
    calc Valued.v W.a₃ * B ≤ 1 * B := mul_le_mul' (valued_a₃ hW) le_rfl
      _ = B ^ 1 := by rw [one_mul, pow_one]
      _ < B ^ 2 := pow_lt_pow_right₀ hB1 (by lia)
  rw [Valuation.map_add_eq_of_lt_left _
    (by rw [map_pow]; exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt h2 h3)), map_pow]

/-- A common bound `C ≥ 1` on `v(x)` and `v(y)` bounds the left-hand side of the
Weierstrass equation by `C²`. -/
private lemma valued_lhs_le {x y : v.adicCompletion K} {C : ℤᵐ⁰} (hxC : Valued.v x ≤ C)
    (hyC : Valued.v y ≤ C) (h1C : 1 ≤ C) :
    Valued.v (y ^ 2 + (W.a₁ * x * y + W.a₃ * y)) ≤ C ^ 2 := by
  refine le_trans (Valued.v.map_add _ _) (max_le ?_ (le_trans (Valued.v.map_add _ _)
    (max_le ?_ ?_)))
  · rw [map_pow]
    exact pow_le_pow_left' hyC 2
  · rw [map_mul, map_mul]
    calc Valued.v W.a₁ * Valued.v x * Valued.v y ≤ 1 * C * C :=
        mul_le_mul' (mul_le_mul' (valued_a₁ hW) hxC) hyC
      _ = C ^ 2 := by rw [one_mul, sq]
  · rw [map_mul]
    calc Valued.v W.a₃ * Valued.v y ≤ 1 * C := mul_le_mul' (valued_a₃ hW) hyC
      _ = C := one_mul C
      _ ≤ C ^ 2 := le_self_pow h1C (by lia)

/-- No point on the curve has `v(x) = exp 1`: an `x`-pole has even order. -/
private lemma valued_ne_exp_one {x y : v.adicCompletion K} (hxy : W.Equation x y) :
    Valued.v x ≠ exp (1 : ℤ) := by
  intro hA1
  have hval := valued_lhs_eq_rhs hxy
  have hRHS : Valued.v (x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆))) = exp (3 : ℤ) := by
    rw [valued_rhs_eq hW (by rw [hA1, ← exp_zero, exp_lt_exp]; lia), hA1, ← exp_nsmul,
      nsmul_eq_mul]
    norm_num
  rcases le_or_gt (Valued.v y) (exp 1) with hB1 | hB1
  · -- `v(y) ≤ exp 1` bounds the left-hand side by `exp 2 < exp 3`
    have hle := valued_lhs_le hW hA1.le hB1 (by rw [← exp_zero, exp_le_exp]; lia)
    rw [hval, hRHS, show (exp 1 : ℤᵐ⁰) ^ 2 = exp (2 : ℤ) by
      rw [← exp_nsmul, nsmul_eq_mul]; norm_num, exp_le_exp] at hle
    lia
  · -- `v(y) > exp 1` gives `v(y)² = exp 3`, impossible by parity
    have hB3 : Valued.v y ^ 2 = exp (3 : ℤ) := by
      rw [← valued_lhs_eq hW (hA1 ▸ hB1) ((by rw [← exp_zero, exp_lt_exp]; lia :
        (1 : ℤᵐ⁰) < exp (1 : ℤ)).trans hB1), hval, hRHS]
    obtain ⟨b, hb⟩ : ∃ b : ℤ, Valued.v y = exp b :=
      ⟨_, (exp_log (exp_pos.trans hB1).ne').symm⟩
    rw [hb, ← exp_nsmul, exp_inj, nsmul_eq_mul] at hB3
    push_cast at hB3
    lia

/-- On an affine point of the kernel of reduction, `v(y)² = v(x)³`; in particular `y ≠ 0`,
and the parameter `-x/y` and the value `-1/y` lie in the maximal ideal. -/
private lemma valued_of_mem {x y : v.adicCompletion K} (hxy : W.Equation x y)
    (hx : exp (2 : ℤ) ≤ Valued.v x) :
    y ≠ 0 ∧ Valued.v (-x / y) ≤ exp (-1 : ℤ) ∧ Valued.v (-1 / y) ≤ exp (-1 : ℤ) := by
  have hA1 : (1 : ℤᵐ⁰) < Valued.v x :=
    lt_of_lt_of_le (by rw [← exp_zero]; exact exp_lt_exp.mpr (by lia)) hx
  have hval := valued_lhs_eq_rhs hxy
  have hRHS := valued_rhs_eq hW hA1
  -- `v(y) ≤ v(x)` would bound the left-hand side by `v(x)² < v(x)³`
  have hBA : Valued.v x < Valued.v y := by
    by_contra hle
    push Not at hle
    have h := valued_lhs_le hW le_rfl hle hA1.le
    rw [hval, hRHS] at h
    exact absurd h (not_le.mpr (pow_lt_pow_right₀ hA1 (by lia)))
  have hB1 : (1 : ℤᵐ⁰) < Valued.v y := hA1.trans hBA
  have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hB1
  have hBA3 : Valued.v y ^ 2 = Valued.v x ^ 3 := by
    rw [← valued_lhs_eq hW hBA hB1, hval, hRHS]
  -- pass to exponents
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v x = exp a :=
    ⟨_, (exp_log (zero_lt_one.trans hA1).ne').symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, Valued.v y = exp b :=
    ⟨_, (exp_log (zero_lt_one.trans hB1).ne').symm⟩
  have h2a : (2 : ℤ) ≤ a := by rwa [ha, exp_le_exp] at hx
  have h23 : 2 * b = 3 * a := by
    rw [ha, hb, ← exp_nsmul, ← exp_nsmul, exp_inj] at hBA3
    push_cast [nsmul_eq_mul] at hBA3
    exact hBA3
  refine ⟨hy0, ?_, ?_⟩
  · rw [map_div₀, Valuation.map_neg, ha, hb, ← exp_sub, exp_le_exp]
    lia
  · rw [map_div₀, Valuation.map_neg, map_one, hb, ← exp_zero, ← exp_sub, exp_le_exp]
    lia

/-- An affine point outside the kernel of reduction has integral coordinates: the only
poles on a Weierstrass curve with integral coefficients have even order at `x`. -/
lemma integral_of_not_mem {x y : v.adicCompletion K} (hxy : W.Equation x y)
    (hx : ¬ exp (2 : ℤ) ≤ Valued.v x) :
    Valued.v x ≤ 1 ∧ Valued.v y ≤ 1 := by
  have hA1 : Valued.v x ≤ 1 := by
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact h0 ▸ zero_le
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v x = exp a := ⟨_, (exp_log h0).symm⟩
      have ha1 : a ≤ 1 := by
        by_contra hlt
        exact hx (ha ▸ exp_le_exp.mpr (by lia))
      rcases eq_or_lt_of_le ha1 with h1 | h1
      · exact absurd (by rw [ha, h1]) (valued_ne_exp_one hW hxy)
      · rw [ha, ← exp_zero, exp_le_exp]
        lia
  refine ⟨hA1, ?_⟩
  by_contra hB1
  push Not at hB1
  have h := valued_rhs_le hW hA1
  rw [← valued_lhs_eq_rhs hxy, valued_lhs_eq hW (hA1.trans_lt hB1) hB1] at h
  exact absurd h (not_le.mpr (one_lt_pow₀ hB1 (by lia)))

/-- The coerced Weierstrass fixed-point equation for the value of `w`. -/
private lemma coe_wEval_eq {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (t : v.adicCompletion K) ^ 3 +
        W.a₁ * t * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) +
        W.a₂ * (t : v.adicCompletion K) ^ 2 *
          ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) +
        W.a₃ * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 +
        W.a₄ * t * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 +
        W.a₆ * ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 3 := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_eq hm)
  rw [wPoly] at h
  push_cast at h
  rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW] at h
  exact h

/-- The coerced form of the evaluated `u`-series. -/
private lemma coe_uEval_eq {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ((W₀.uEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      1 - W.a₁ * t - W.a₃ *
        ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.uEval_eq hm)
  push_cast at h
  rw [coe_a₁ hW, coe_a₃ hW] at h
  exact h

/-- The coerced chord-cubic leading coefficient does not vanish. -/
private lemma coe_chordCoeff_ne_zero {Λ : v.adicCompletionIntegers K}
    (hΛ : Λ ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    (1 : v.adicCompletion K) +
      W.a₂ * ((Λ : v.adicCompletionIntegers K) : v.adicCompletion K) +
      W.a₄ * ((Λ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 +
      W.a₆ * ((Λ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 3 ≠ 0 := by
  intro hc
  apply (W₀.isUnit_chordCoeff hΛ).ne_zero
  refine Subtype.coe_injective ?_
  push_cast
  rw [coe_a₂ hW, coe_a₄ hW, coe_a₆ hW]
  exact hc

/-- Near a `2`-torsion base point `(x₀, y₀)`, the second factor of the finite-difference
identity `(y - negY x₀ y₀) * (y - y₀) = (x - x₀) * (…)` is congruent to the negative of the
partial derivative in `x` at the base point, hence has the same valuation `exp c`. -/
private lemma valued_num_of_two_torsion {x₀ y₀ x y : v.adicCompletion K} {c : ℤ} {s : ℕ}
    (hx₀ : Valued.v x₀ ≤ 1)
    (hc : Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = exp c)
    (hsc : 1 - c ≤ (s : ℤ)) (hx : Valued.v (x - x₀) ≤ exp (-(s : ℤ)))
    (hy : Valued.v (y - y₀) ≤ exp (-(s : ℤ))) :
    Valued.v (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) = exp c := by
  have hdiff : Valued.v ((x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
      -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))) ≤ exp (-(s : ℤ)) := by
    rw [show (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
        -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) =
        (x - x₀) * (x + 2 * x₀ + W.a₂) - W.a₁ * (y - y₀) by ring]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [map_mul]
      refine le_trans (mul_le_mul' hx ?_) (by rw [mul_one])
      refine le_trans (Valued.v.map_add _ _) (max_le (le_trans (Valued.v.map_add _ _)
        (max_le (valued_le_one_of_sub hx hx₀) ?_)) (valued_a₂ hW))
      calc Valued.v (2 * x₀) ≤ Valued.v 2 * Valued.v x₀ := le_of_eq (map_mul _ _ _)
        _ ≤ 1 * 1 := mul_le_mul' (valued_coe_le_one 2) hx₀
        _ = 1 := one_mul 1
    · rw [map_mul]
      exact le_trans (mul_le_mul' (valued_a₁ hW) hy) (by rw [one_mul])
  rw [show x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y =
      -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) +
      ((x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
        -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))) by ring,
    Valuation.map_add_eq_of_lt_left, Valuation.map_neg, hc]
  refine lt_of_le_of_lt hdiff ?_
  rw [Valuation.map_neg, hc, exp_lt_exp]
  lia

end

/-- Lower bound for the valuation of the chord slope towards the negative of the base
point, from the product form of the numerator valuation supplied by the finite-difference
identity. -/
private lemma exp_one_le_valued_slope {x₀ y₀ x y : v.adicCompletion K} {c : ℤ} {s : ℕ}
    (hxx : x ≠ x₀) (hsc : 1 - c ≤ (s : ℤ)) (hy : Valued.v (y - y₀) ≤ exp (-(s : ℤ)))
    (hprod : Valued.v (y - W.negY x₀ y₀) * Valued.v (y - y₀) = Valued.v (x - x₀) * exp c) :
    exp (1 : ℤ) ≤ Valued.v ((y - W.negY x₀ y₀) / (x - x₀)) := by
  obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
    ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
  obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, Valued.v (y - y₀) = exp dy := by
    refine ⟨_, (exp_log fun h0 ↦ ?_).symm⟩
    rw [h0, mul_zero, hdx] at hprod
    exact mul_ne_zero exp_ne_zero exp_ne_zero hprod.symm
  obtain ⟨nv, hnv⟩ : ∃ nv : ℤ, Valued.v (y - W.negY x₀ y₀) = exp nv := by
    refine ⟨_, (exp_log fun h0 ↦ ?_).symm⟩
    rw [h0, zero_mul, hdx] at hprod
    exact mul_ne_zero exp_ne_zero exp_ne_zero hprod.symm
  rw [hnv, hdy, hdx, ← exp_add, ← exp_add, exp_inj] at hprod
  have hdy' : dy ≤ -(s : ℤ) := by rwa [hdy, exp_le_exp] at hy
  rw [map_div₀, hnv, hdx, ← exp_sub, exp_le_exp]
  lia

/-- The formal inverse preserves the valuation of the parameter. -/
private lemma valued_iotaEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((W₀.iotaEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      Valued.v (t : v.adicCompletion K) := by
  rw [coe_iotaEval_eq hm, Valuation.map_neg, map_mul,
    valued_coe_isUnit (W₀.isUnit_duEval hm), mul_one]

/-- The valuation of (the coercion of) `w(t)` is `v(t)³`. -/
private lemma valued_coe_wEval {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    Valued.v ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      Valued.v (t : v.adicCompletion K) ^ 3 := by
  have h := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_eq_cube_mul hm)
  push_cast at h
  rw [h, map_mul, map_pow, valued_coe_isUnit (W₀.isUnit_vEval hm), mul_one]

private lemma ne_of_valued_lt {a b : v.adicCompletionIntegers K}
    (h : Valued.v (a : v.adicCompletion K) < Valued.v (b : v.adicCompletion K)) : a ≠ b :=
  fun he ↦ h.ne (by rw [he])

/-- A parameter of valuation smaller than that of `2` is not its own formal inverse. -/
private lemma ne_iotaEval_self {s : v.adicCompletionIntegers K}
    (hsm : s ∈ maximalIdeal (v.adicCompletionIntegers K)) (hs0 : s ≠ 0)
    (h2 : Valued.v (s : v.adicCompletion K) <
      Valued.v ((2 : v.adicCompletionIntegers K) : v.adicCompletion K)) :
    s ≠ W₀.iotaEval s := by
  intro h
  have hws_le : Valued.v ((W₀.wEval s : v.adicCompletionIntegers K) : v.adicCompletion K) ≤
      Valued.v (s : v.adicCompletion K) := by
    rw [valued_coe_wEval hsm]
    calc Valued.v (s : v.adicCompletion K) ^ 3
        = Valued.v (s : v.adicCompletion K) * Valued.v (s : v.adicCompletion K) ^ 2 :=
          pow_succ' _ 2
      _ ≤ Valued.v (s : v.adicCompletion K) * 1 :=
          mul_le_mul' le_rfl (pow_le_one' (valued_coe_le_one s) 2)
      _ = Valued.v (s : v.adicCompletion K) := mul_one _
  have hcoe2 := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.eq_two_of_iotaEval_self hsm hs0 h)
  push_cast at hcoe2
  have hval2 : Valued.v ((2 : v.adicCompletionIntegers K) : v.adicCompletion K) ≤
      Valued.v (s : v.adicCompletion K) := by
    rw [← hcoe2]
    refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)
    · rw [map_mul]
      exact (mul_le_mul' (valued_coe_le_one _) le_rfl).trans_eq (one_mul _)
    · rw [map_mul]
      calc Valued.v (W₀.a₃ : v.adicCompletion K) *
            Valued.v ((W₀.wEval s : v.adicCompletionIntegers K) : v.adicCompletion K)
          ≤ 1 * Valued.v (s : v.adicCompletion K) :=
            mul_le_mul' (valued_coe_le_one _) hws_le
        _ = Valued.v (s : v.adicCompletion K) := one_mul _
  exact absurd (lt_of_le_of_lt hval2 h2) (lt_irrefl _)

/-- An auxiliary parameter in `𝔪` avoiding a given nonzero parameter, its formal inverse,
and its own formal inverse: any high enough power of a uniformizer works. -/
private lemma exists_aux_param [CharZero K] {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (h0 : t ≠ 0) :
    ∃ s : v.adicCompletionIntegers K, s ∈ maximalIdeal (v.adicCompletionIntegers K) ∧
      s ≠ 0 ∧ s ≠ t ∧ s ≠ W₀.iotaEval t ∧ s ≠ W₀.iotaEval s := by
  have hchar : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have h20 : ((2 : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    exact_mod_cast (two_ne_zero : (2 : v.adicCompletion K) ≠ 0)
  -- an auxiliary parameter `s = π^k` of very small valuation
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπv : Valued.v ((π : v.adicCompletionIntegers K) : v.adicCompletion K) = exp (-1) := by
    have h := v.valued_irreducible_adicCompletionIntegers hπ
    rwa [algebraMap_eq_coe] at h
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact h0
  obtain ⟨m, htv⟩ : ∃ m : ℤ, Valued.v (t :
      v.adicCompletion K) = exp m := ⟨_, (exp_log ht0').symm⟩
  have hm1 : m ≤ -1 := by
    have h := mem_maximalIdeal_iff.mp hm
    rwa [htv, exp_le_exp] at h
  obtain ⟨c, h2v⟩ : ∃ c : ℤ, Valued.v ((2 : v.adicCompletionIntegers K) :
      v.adicCompletion K) = exp c := ⟨_, (exp_log (by simp [h20])).symm⟩
  have hc0 : c ≤ 0 := by
    have h := valued_coe_le_one (2 : v.adicCompletionIntegers K)
    rwa [h2v, ← exp_zero, exp_le_exp] at h
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, (k : ℤ) = max (-m) (-c) + 1 :=
    ⟨(max (-m) (-c) + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨s, hsdef⟩ : ∃ s : v.adicCompletionIntegers K, s = π ^ k := ⟨_, rfl⟩
  have hsv : Valued.v ((s : v.adicCompletionIntegers K) : v.adicCompletion K) =
      exp (-(k : ℤ)) := by
    rw [hsdef]
    push_cast
    rw [map_pow, hπv, ← exp_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have hks : -(k : ℤ) < m := by omega
  have hkc : -(k : ℤ) < c := by omega
  have hsm : s ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    mem_maximalIdeal_iff.mpr (by rw [hsv, exp_le_exp]; lia)
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    exact pow_ne_zero _ hπ.ne_zero
  refine ⟨s, hsm, hs0, ?_, ?_, ?_⟩
  · exact ne_of_valued_lt (by rw [hsv, htv, exp_lt_exp]; exact hks)
  · refine ne_of_valued_lt ?_
    rw [valued_iotaEval hm, hsv, htv, exp_lt_exp]
    exact hks
  · exact ne_iotaEval_self hsm hs0 (by rw [hsv, h2v, exp_lt_exp]; exact hkc)

private lemma ne_of_coe_ne {z z' : W₀.formalGroupLaw.Points}
    (h : (z () : v.adicCompletionIntegers K) ≠ (z' () : v.adicCompletionIntegers K)) :
    z ≠ z' :=
  fun h' ↦ h (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h')

/-- An auxiliary point of the formal group avoiding a given nonzero point `z`, its formal
inverse, and its own formal inverse (so that all sums involved in doubling `z` are chord
cases). -/
private lemma exists_aux_point [CharZero K] {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0) :
    ∃ u : W₀.formalGroupLaw.Points, (u () : v.adicCompletionIntegers K) ≠ 0 ∧
      u ≠ z ∧ u ≠ W₀.negPoint z ∧ W₀.negPoint u ≠ z ∧ W₀.negPoint u ≠ W₀.negPoint z ∧
      (u () : v.adicCompletionIntegers K) ≠ W₀.iotaEval (u ()) := by
  obtain ⟨s, hsm, hs0, hst, hsιt, hsιs⟩ := exists_aux_param (z ()).2 h0
  refine ⟨fun _ ↦ ⟨s, hsm⟩, hs0, ne_of_coe_ne hst, ne_of_coe_ne ?_, ne_of_coe_ne ?_,
    ne_of_coe_ne ?_, hsιs⟩
  · rw [W₀.negPoint_apply_coe]
    exact hsιt
  · rw [W₀.negPoint_apply_coe]
    exact fun h ↦ hsιt ((W₀.iotaEval_iotaEval hsm).symm.trans (congrArg _ h))
  · rw [W₀.negPoint_apply_coe, W₀.negPoint_apply_coe]
    exact fun h ↦ hst (((W₀.iotaEval_iotaEval hsm).symm.trans (congrArg _ h)).trans
      (W₀.iotaEval_iotaEval (z ()).2))

/-- The valuation of the `x`-coordinate `t/w(t)` is `v(t)⁻²`. -/
theorem valued_formalPoint_x
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (ht0 : t ≠ 0) :
    Valued.v ((t : v.adicCompletion K) / (W₀.wEval t : v.adicCompletion K)) =
      (Valued.v (t : v.adicCompletion K))⁻¹ ^ 2 := by
  have hvE : Valued.v ((W₀.vEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
    valued_coe_isUnit (W₀.isUnit_vEval ht)
  have hw : ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (t : v.adicCompletion K) ^ 3 * ((W₀.vEval t : v.adicCompletionIntegers K) :
        v.adicCompletion K) := by
    rw [W₀.wEval_eq_cube_mul ht]
    push_cast
    rfl
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact ht0
  rw [map_div₀, hw, map_mul, map_pow, hvE, mul_one, inv_pow, pow_succ',
    div_mul_eq_div_div, div_self ht0', one_div]

/-- The parameter of a sum of `𝔪`-points lies in every `𝔪`-power containing both
parameters (evaluation of the addition series preserves the level). -/
private lemma add_param_mem_pow {z z' : W₀.formalGroupLaw.Points} {n : ℕ}
    (hz : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1))
    (hz' : (z' () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1)) :
    ((z + z') () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) := by
  rw [W₀.add_apply_coe_eq_addEval]
  refine MvPSeries.eval_mem_maximalIdeal_pow (hasEval_pairElim (z ()).2 (z' ()).2)
    (by rintro (j | j) <;> assumption) W₀.addSeries ?_
  rw [W₀.constantCoeff_addSeries]
  exact zero_mem _

/-- For a nonzero parameter `t ∈ 𝔪`, membership in `𝔪^(n+1)` is the pole condition on
the `x`-coordinate of the associated point. -/
private lemma exists_pi_pow_factor {π t : v.adicCompletionIntegers K} {n : ℕ}
    (hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1)) :
    ∃ s ∈ maximalIdeal (v.adicCompletionIntegers K), t = π ^ n * s := by
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ht
  obtain ⟨u, hu⟩ := ht
  refine ⟨π * u, ?_, by rw [hu, pow_succ]; ring⟩
  rw [hmax]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right ..)

private lemma points_ne_zero_param {z : W₀.formalGroupLaw.Points} (hz0 : z ≠ 0) :
    (z () : v.adicCompletionIntegers K) ≠ 0 :=
  fun h ↦ hz0 (funext fun i ↦ by cases i; exact Subtype.ext h)

/-- A point of the formal group killed by a prime different from the residue
characteristic is trivial. -/
private lemma points_eq_zero_of_nsmul_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hqp : q ≠ p) {z : W₀.formalGroupLaw.Points} (hz : q • z = 0) : z = 0 := by
  by_contra hz0
  obtain ⟨k, hk1, hkv⟩ := ChabautyColeman.exists_valued_eq_exp_neg (z ()).2
    (points_ne_zero_param hz0)
  have htk : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ k :=
    (v.mem_maximalIdeal_pow_iff (K := K)).mpr hkv.le
  have hcong := (W₀.nsmul_apply_coe_mem_and_sub_mem (Nat.one_le_iff_ne_zero.mp hk1) htk q).2
  rw [hz, FormalGroupLaw.zero_apply_coe, zero_sub, nsmul_eq_mul] at hcong
  obtain ⟨u, hu⟩ := (isUnit_natCast_of_not_dvd hp hpmem
    fun hdvd ↦ hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd).symm).exists_left_inv
  have ht2k : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (2 * k) := by
    rw [show (z () : v.adicCompletionIntegers K) = u * ((q : v.adicCompletionIntegers K) *
      (z () : v.adicCompletionIntegers K)) by rw [← mul_assoc, hu, one_mul]]
    exact Ideal.mul_mem_left _ _ (by simpa using neg_mem hcong)
  have hle := (v.mem_maximalIdeal_pow_iff (K := K)).mp ht2k
  rw [hkv, exp_le_exp] at hle
  push_cast at hle
  lia

/-- The multiplication-by-`p` series splits as `p·X + A + B` with `A` supported in
degrees `≥ 2` prime to `p` with coefficients divisible by `p`, and `B` supported in
degrees divisible by `p`. -/
private lemma exists_mulSeries_split [CharZero K] {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ∃ A B : MvPowerSeries Unit (v.adicCompletionIntegers K),
      W₀.formalGroupLaw.mulSeries p = MvPowerSeries.C (p : v.adicCompletionIntegers K) *
          MvPowerSeries.X () + (A + B) ∧
      (∀ d : Unit →₀ ℕ, MvPowerSeries.coeff d A ∈
        Ideal.span {(p : v.adicCompletionIntegers K)}) ∧
      (∀ d : Unit →₀ ℕ, d.degree < 2 → MvPowerSeries.coeff d A = 0) ∧
      (∀ d : Unit →₀ ℕ, d.degree < p → MvPowerSeries.coeff d B = 0) := by
  obtain ⟨A, hA⟩ : ∃ A : MvPowerSeries Unit (v.adicCompletionIntegers K),
      ∀ d : Unit →₀ ℕ, MvPowerSeries.coeff d A = if 2 ≤ d () ∧ ¬ p ∣ d () then
        MvPowerSeries.coeff d (W₀.formalGroupLaw.mulSeries p) else 0 :=
    ⟨fun d ↦ if 2 ≤ d () ∧ ¬ p ∣ d () then
      MvPowerSeries.coeff d (W₀.formalGroupLaw.mulSeries p) else 0, fun _ ↦ rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : MvPowerSeries Unit (v.adicCompletionIntegers K),
      ∀ d : Unit →₀ ℕ, MvPowerSeries.coeff d B = if 2 ≤ d () ∧ p ∣ d () then
        MvPowerSeries.coeff d (W₀.formalGroupLaw.mulSeries p) else 0 :=
    ⟨fun d ↦ if 2 ≤ d () ∧ p ∣ d () then
      MvPowerSeries.coeff d (W₀.formalGroupLaw.mulSeries p) else 0, fun _ ↦ rfl⟩
  have hdeg : ∀ d : Unit →₀ ℕ, d.degree = d () := fun d ↦ by
    rw [show d = Finsupp.single () (d ()) from Finsupp.ext fun i ↦ by cases i; simp,
      Finsupp.degree_single, Finsupp.single_eq_same]
  refine ⟨A, B, ?_, ?_, ?_, ?_⟩
  · refine MvPowerSeries.ext fun d ↦ ?_
    have hd : d = Finsupp.single () (d ()) := Finsupp.ext fun i ↦ by cases i; simp
    rw [map_add, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, hA, hB]
    rcases Nat.lt_or_ge (d ()) 2 with h2 | h2
    · rcases (show d () = 0 ∨ d () = 1 by lia) with h0 | h1
      · have hd0 : d = 0 := hd.trans (by rw [h0, Finsupp.single_zero])
        subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          W₀.formalGroupLaw.constantCoeff_mulSeries p,
          if_neg (show ¬((0 : Unit →₀ ℕ) = Finsupp.single () 1) from fun hc ↦
            one_ne_zero (Finsupp.single_eq_zero.mp hc.symm)),
          if_neg (show ¬(2 ≤ (0 : Unit →₀ ℕ) () ∧ ¬ p ∣ (0 : Unit →₀ ℕ) ()) from by simp),
          if_neg (show ¬(2 ≤ (0 : Unit →₀ ℕ) () ∧ p ∣ (0 : Unit →₀ ℕ) ()) from by simp)]
        ring
      · have hd1 : d = Finsupp.single () 1 := hd.trans (by rw [h1])
        subst hd1
        rw [ChabautyColeman.coeff_single_mulSeries, if_pos rfl,
          if_neg (show ¬(2 ≤ (Finsupp.single () 1 : Unit →₀ ℕ) () ∧
            ¬ p ∣ (Finsupp.single () 1 : Unit →₀ ℕ) ()) from by simp),
          if_neg (show ¬(2 ≤ (Finsupp.single () 1 : Unit →₀ ℕ) () ∧
            p ∣ (Finsupp.single () 1 : Unit →₀ ℕ) ()) from by simp)]
        ring
    · rw [if_neg (show ¬(d = Finsupp.single () 1) from fun hc ↦ by
        rw [hc, Finsupp.single_eq_same] at h2; lia), mul_zero]
      rcases Classical.em (p ∣ d ()) with hdvd | hdvd
      · rw [if_neg (show ¬(2 ≤ d () ∧ ¬ p ∣ d ()) from by tauto),
          if_pos (⟨h2, hdvd⟩ : 2 ≤ d () ∧ p ∣ d ())]
        ring
      · rw [if_pos (⟨h2, hdvd⟩ : 2 ≤ d () ∧ ¬ p ∣ d ()),
          if_neg (show ¬(2 ≤ d () ∧ p ∣ d ()) from by tauto)]
        ring
  · intro d
    rw [hA]
    split_ifs with h
    · exact ChabautyColeman.coeff_mulSeries_mem_span W₀.formalGroupLaw hp hpmem h.2
    · exact zero_mem _
  · intro d hlow
    rw [hdeg] at hlow
    rw [hA, if_neg fun hc ↦ absurd hc.1 (by omega)]
  · intro d hlow
    rw [hdeg] at hlow
    rw [hB, if_neg fun hc ↦ absurd (Nat.le_of_dvd (by omega) hc.2) (by omega)]

/-- The absolute ramification index of the residue characteristic: `v(p) = exp(-e)` with
`1 ≤ e`, and `e ≤ p - 2` under the ramification condition `p ∉ 𝔪^(p-1)`. -/
private lemma exists_ramificationBound [CharZero K] {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1)) :
    ∃ e : ℕ, 1 ≤ e ∧ e ≤ p - 2 ∧
      Valued.v (((p : v.adicCompletionIntegers K) : v.adicCompletionIntegers K) :
        v.adicCompletion K) = exp (-(e : ℤ)) ∧
      (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K) ^ e := by
  have hp0 : (p : v.adicCompletionIntegers K) ≠ 0 := fun h ↦ hp.ne_zero (by
    have hchar : CharZero (v.adicCompletion K) :=
      charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
    have h' := congrArg (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) h
    rw [map_natCast, map_zero] at h'
    exact_mod_cast h')
  obtain ⟨e, he1, hev⟩ := ChabautyColeman.exists_valued_eq_exp_neg hpmem hp0
  refine ⟨e, he1, ?_, hev, (v.mem_maximalIdeal_pow_iff (K := K)).mpr hev.le⟩
  by_contra hlt
  exact hpram ((v.mem_maximalIdeal_pow_iff (K := K)).mpr (by
    rw [hev, exp_le_exp]
    have := hp.two_le
    omega))

/-- A point of the formal group killed by the residue characteristic `p` is trivial
under the ramification condition `p ∉ 𝔪^(p-1)` (that is, `e < p − 1`): the value
`ψ_p(t) = p·t + A(t) + B(t)` cannot vanish, since `v(p·t)` beats both tails. -/
private lemma points_eq_zero_of_nsmul_residueChar [CharZero K] {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {z : W₀.formalGroupLaw.Points} (hz : p • z = 0) : z = 0 := by
  by_contra hz0
  obtain ⟨k, hk1, hkv⟩ := ChabautyColeman.exists_valued_eq_exp_neg (z ()).2
    (points_ne_zero_param hz0)
  have htk : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ k :=
    (v.mem_maximalIdeal_pow_iff (K := K)).mpr hkv.le
  obtain ⟨e, he1, hele, hev, hpe⟩ := exists_ramificationBound hp hpmem hpram
  -- the vanishing of `ψ_p(t)` and the two tail estimates
  have h0 : MvPSeries.eval (fun _ : Unit ↦ (z () : v.adicCompletionIntegers K))
      (W₀.formalGroupLaw.mulSeries p) = 0 := by
    rw [← W₀.nsmul_apply_coe_eq_eval, hz, FormalGroupLaw.zero_apply_coe]
  obtain ⟨A, B, hsplit, hAmem, hAlow, hBlow⟩ := exists_mulSeries_split (W₀ := W₀) hp hpmem
  have hE : MvPowerSeries.HasEval (fun _ : Unit ↦ (z () : v.adicCompletionIntegers K)) :=
    MvPSeries.hasEval_of_mem fun _ ↦ (z ()).2
  have hevalA := MvPSeries.eval_mem_maximalIdeal_pow_add_mul hE (a := e) (c := 2)
    (fun _ ↦ htk) A (fun d ↦ SetLike.le_def.mp
      ((Ideal.span_singleton_le_iff_mem _).mpr hpe) (hAmem d)) hAlow
  have hevalB := MvPSeries.eval_mem_maximalIdeal_pow_mul hE (c := p) (fun _ ↦ htk) B hBlow
  -- hence `p·t` lies one level too deep
  have hpt : (p : v.adicCompletionIntegers K) * (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (e + k + 1) := by
    have hple : maximalIdeal (v.adicCompletionIntegers K) ^ (p * k) ≤
        maximalIdeal (v.adicCompletionIntegers K) ^ (e + k + 1) :=
      Ideal.pow_le_pow_right (by
        have h2 := hp.two_le
        have hmul : p - 1 ≤ (p - 1) * k := Nat.le_mul_of_pos_right _ (by omega)
        have hdist : (p - 1) * k = p * k - k := by rw [Nat.sub_mul, one_mul]
        omega)
    have hale : maximalIdeal (v.adicCompletionIntegers K) ^ (e + 2 * k) ≤
        maximalIdeal (v.adicCompletionIntegers K) ^ (e + k + 1) :=
      Ideal.pow_le_pow_right (by omega)
    have hsum := congrArg (MvPSeries.eval
      (fun _ : Unit ↦ (z () : v.adicCompletionIntegers K))) hsplit
    rw [h0, MvPSeries.eval_add hE, MvPSeries.eval_add hE, MvPSeries.eval_mul hE,
      MvPSeries.eval_C, MvPSeries.eval_X] at hsum
    rw [show (p : v.adicCompletionIntegers K) * (z () : v.adicCompletionIntegers K)
      = -(MvPSeries.eval (fun _ : Unit ↦ (z () : v.adicCompletionIntegers K)) A
        + MvPSeries.eval (fun _ : Unit ↦ (z () : v.adicCompletionIntegers K)) B) by
      linear_combination -hsum]
    exact neg_mem (add_mem (hale hevalA) (hple hevalB))
  -- contradiction with the exact valuation `v(p·t) = exp (-(e+k))`
  have hle := (v.mem_maximalIdeal_pow_iff (K := K)).mp hpt
  rw [MulMemClass.coe_mul, map_mul, hev, hkv, ← exp_add, exp_le_exp] at hle
  push_cast at hle
  omega

/-- Division by a uniformizer: the maximal ideal of `𝒪_v` is additively isomorphic to
`𝒪_v` itself. -/
private lemma maximalIdeal_addEquiv {π : v.adicCompletionIntegers K} (hπ0 : π ≠ 0)
    (hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π}) :
    Nonempty (maximalIdeal (v.adicCompletionIntegers K) ≃+ v.adicCompletionIntegers K) :=
  ⟨((LinearEquiv.ofEq _ _ (by rw [hmax])).trans
    (LinearEquiv.toSpanNonzeroSingleton _ _ π hπ0).symm).toAddEquiv⟩

private lemma param_pow_iff {t : v.adicCompletionIntegers K}
    (hm : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (h0 : t ≠ 0) (n : ℕ) :
    t ∈ maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
      exp (2 * (n + 1) : ℤ) ≤ Valued.v ((t : v.adicCompletion K) /
        ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
  rw [valued_formalPoint_x hm h0, mem_maximalIdeal_pow_iff]
  have ht0' : Valued.v (t : v.adicCompletion K) ≠ 0 := by
    simp only [ne_eq, _root_.map_eq_zero, ZeroMemClass.coe_eq_zero]
    exact h0
  obtain ⟨m, hmv⟩ : ∃ m : ℤ, Valued.v (t : v.adicCompletion K) = exp m :=
    ⟨_, (exp_log ht0').symm⟩
  rw [hmv, ← exp_neg, ← exp_nsmul, exp_le_exp, exp_le_exp, nsmul_eq_mul]
  push_cast
  constructor <;> intro h <;> lia

/-- The parameter map modulo `𝔪^(k+2)` is additive on parameters in `𝔪^(k+1)`. -/
private lemma mk_add_param {k : ℕ} {z z' : W₀.formalGroupLaw.Points}
    (hz : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1))
    (hz' : (z' () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1)) :
    Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
        (((z + z') ()) : v.adicCompletionIntegers K) =
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)) (z ()) +
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)) (z' ()) := by
  rw [← map_add
    (Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)))
    ((z () : v.adicCompletionIntegers K)) ((z' () : v.adicCompletionIntegers K))]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [W₀.add_apply_coe_eq_addEval]
  refine SetLike.le_def.mp
    (Ideal.pow_le_pow_right (m := k + 2) (n := 2 * (k + 1)) (by lia)) ?_
  exact W₀.addEval_sub_add_mem (Nat.succ_ne_zero k) hz hz'

private lemma finite_quotient_pow [Finite (R ⧸ v.asIdeal)] (m : ℕ) :
    Finite (v.adicCompletionIntegers K ⧸
      (maximalIdeal (v.adicCompletionIntegers K) ^ m)) := by
  have hfin : Finite (v.adicCompletionIntegers K ⧸
      maximalIdeal (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m

/-- Closed balls (with nonzero radius) in the completion are open. -/
private lemma isOpen_le_ball (a : v.adicCompletion K) (m : ℤ) :
    IsOpen {b : v.adicCompletion K | Valued.v (b - a) ≤ exp m} := by
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp m)
  have hr0 : Valued.v.restrict z ≠ 0 := fun h0 ↦ exp_ne_zero (hz ▸ (by
    rw [← Valuation.embedding_restrict, h0, map_zero] : Valued.v z = 0))
  have hset : {b : v.adicCompletion K | Valued.v (b - a) ≤ exp m} = (fun b ↦ b - a) ⁻¹'
      {y | Valued.v.restrict y ≤ Valued.v.restrict z} := by
    ext b
    rw [Set.mem_preimage, Set.mem_setOf, Set.mem_setOf,
      Valuation.restrict_le_iff_le_embedding, Valuation.embedding_restrict, hz]
  rw [hset]
  exact (Valued.isOpen_closedBall _ hr0).preimage (continuous_id.sub continuous_const)

/-- The valuation ring inside the completion is a compact subset: it is closed, and totally
bounded because the quotients `𝒪_v/𝔪^n` are finite. -/
private lemma isCompact_integerSet [Finite (R ⧸ v.asIdeal)] :
    IsCompact {a : v.adicCompletion K | Valued.v a ≤ 1} := by
  rw [isCompact_iff_totallyBounded_isComplete]
  constructor
  · -- totally bounded: cover by cosets of `𝔪^n`
    rw [(Valued.hasBasis_uniformity _ _).totallyBounded_iff]
    intro γ _
    obtain ⟨m, hm⟩ : ∃ m : ℤ,
        exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
      obtain ⟨a, ha⟩ :=
        WithZero.ne_zero_iff_exists.mp (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
      refine ⟨Multiplicative.toAdd a - 1, ?_⟩
      rw [← ha, show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl]
      exact exp_lt_exp.mpr (by lia)
    set n : ℕ := (-m).toNat with hn
    have hfq : Finite (v.adicCompletionIntegers K ⧸
        (maximalIdeal (v.adicCompletionIntegers K) ^ n)) := finite_quotient_pow n
    refine ⟨Set.range (fun c : v.adicCompletionIntegers K ⧸
        (maximalIdeal (v.adicCompletionIntegers K) ^ n) ↦
        ((Quotient.out c : v.adicCompletionIntegers K) : v.adicCompletion K)),
      Set.finite_range _, fun x hx ↦ ?_⟩
    have hxm : Valued.v x ≤ 1 := hx
    obtain ⟨c, hc⟩ : ∃ c, c = Ideal.Quotient.mk
        (maximalIdeal (v.adicCompletionIntegers K) ^ n) ⟨x, hxm⟩ := ⟨_, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨((Quotient.out c : v.adicCompletionIntegers K) :
      v.adicCompletion K), Set.mem_range_self c, ?_⟩
    have hsub : (⟨x, hxm⟩ - Quotient.out c : v.adicCompletionIntegers K) ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ n := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hc]
      exact (Quotient.out_eq c).symm
    have hval : Valued.v (((Quotient.out c : v.adicCompletionIntegers K) :
        v.adicCompletion K) - x) ≤ exp (-(n : ℤ)) := by
      have h1 := (v.mem_maximalIdeal_pow_iff (K := K)).mp hsub
      rw [show ((⟨x, hxm⟩ - Quotient.out c : v.adicCompletionIntegers K) :
        v.adicCompletion K) = x - ((Quotient.out c : v.adicCompletionIntegers K) :
          v.adicCompletion K) from rfl] at h1
      rwa [← Valuation.map_sub_swap] at h1
    refine Set.mem_setOf.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
      (lt_of_le_of_lt hval ?_))
    refine lt_of_le_of_lt (exp_le_exp.mpr ?_) hm
    rw [hn]
    lia
  · -- complete: the valuation ring is closed in the complete field
    have hset : {a : v.adicCompletion K | Valued.v a ≤ 1} =
        (((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring :
          ValuationSubring (v.adicCompletion K)) : Set (v.adicCompletion K)) := rfl
    rw [hset]
    exact (Valued.isClosed_valuationSubring _).isComplete

/-- The set of integral points of a Weierstrass curve over `K_v` is compact. -/
private lemma isCompact_integralPoints [Finite (R ⧸ v.asIdeal)] :
    IsCompact {p : (v.adicCompletion K) × (v.adicCompletion K) |
      W.Equation p.1 p.2 ∧ Valued.v p.1 ≤ 1 ∧ Valued.v p.2 ≤ 1} := by
  have hcl : IsClosed {p : (v.adicCompletion K) × (v.adicCompletion K) |
      W.Equation p.1 p.2} := by
    have hset : {p : (v.adicCompletion K) × (v.adicCompletion K) | W.Equation p.1 p.2} =
        {p : (v.adicCompletion K) × (v.adicCompletion K) |
          p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 =
            p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆} := by
      ext p
      rw [Set.mem_setOf, Set.mem_setOf, W.equation_iff]
    rw [hset]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hZeq : {p : (v.adicCompletion K) × (v.adicCompletion K) |
      W.Equation p.1 p.2 ∧ Valued.v p.1 ≤ 1 ∧ Valued.v p.2 ≤ 1} =
      ({a : v.adicCompletion K | Valued.v a ≤ 1} ×ˢ
        {a : v.adicCompletion K | Valued.v a ≤ 1}) ∩
      {p : (v.adicCompletion K) × (v.adicCompletion K) | W.Equation p.1 p.2} := by
    ext p
    simp only [Set.mem_setOf, Set.mem_inter_iff, Set.mem_prod]
    tauto
  rw [hZeq]
  exact (isCompact_integerSet.prod isCompact_integerSet).inter_right hcl

end WeierstrassCurve.Affine

end
