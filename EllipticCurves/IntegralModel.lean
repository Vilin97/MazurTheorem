/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
-/
module

public import Mathlib

@[expose] public section

/-!
# Integral models of Weierstrass curves over a local field

Let `K` be the fraction field of a Dedekind domain, `v` a height-one prime, and `K_v` the
completion. `WeierstrassCurve.Affine.exists_variableChange_map_eq` shows that every Weierstrass
curve over `K_v` has an integral model: after an admissible change of variables its coefficients
lie in `𝒪_v`.

This feeds the structure theorem
`WeierstrassCurve.Affine.exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers` (the group
`E(K_v)` has a finite-index subgroup isomorphic to `(𝒪_v, +)`), which lives in
`EllipticCurves.WeierstrassFormalGroup`.
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

open WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

section IntegralModel

variable (W : Affine (v.adicCompletion K))

private lemma pow_mul_mem_adicCompletionIntegers {z : v.adicCompletion K}
    (hz : Valued.v z = exp (-1)) {N i : ℕ} (hi : 1 ≤ i) {a : v.adicCompletion K}
    (ha : log (Valued.v a) ≤ (N : ℤ)) :
    (z ^ N) ^ i * a ∈ v.adicCompletionIntegers K := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  refine (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mpr ?_
  have hva : Valued.v a = exp (log (Valued.v a)) :=
    (exp_log ((Valuation.ne_zero_iff _).mpr ha0)).symm
  rw [map_mul, map_pow, map_pow, hz, ← exp_nsmul, ← exp_nsmul, hva, ← exp_add, ← exp_zero]
  refine exp_le_exp.mpr ?_
  have h2 : (N : ℤ) ≤ ((i * N : ℕ) : ℤ) := by exact_mod_cast Nat.le_mul_of_pos_left N hi
  push_cast at h2 ⊢
  lia

/-- Every Weierstrass curve over `K_v` has an integral model: after an admissible change of
variables, the coefficients lie in `𝒪_v`. -/
theorem exists_variableChange_map_eq :
    ∃ (C : VariableChange (v.adicCompletion K))
      (W₀ : WeierstrassCurve (v.adicCompletionIntegers K)),
      W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = C • W := by
  -- an element of valuation `exp (-1)`
  obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp (-1))
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact exp_ne_zero hz.symm
  set w : (v.adicCompletion K)ˣ := Units.mk0 z hz0 with hw
  -- a bound for the valuations of the coefficients
  set M : ℤ := log (Valued.v W.a₁) ⊔ log (Valued.v W.a₂) ⊔ log (Valued.v W.a₃) ⊔
    log (Valued.v W.a₄) ⊔ log (Valued.v W.a₆) ⊔ 0
  set N : ℕ := M.toNat
  -- scaling a coefficient by `z ^ (N * i)` lands in the ring of integers
  have key (a : v.adicCompletion K) (ha : log (Valued.v a) ≤ M) {i : ℕ} (hi : 1 ≤ i) :
      (z ^ N) ^ i * a ∈ v.adicCompletionIntegers K :=
    pow_mul_mem_adicCompletionIntegers v hz hi (ha.trans (Int.self_le_toNat M))
  -- the change of variables by `u = w⁻¹ ^ N`
  set C : VariableChange (v.adicCompletion K) := ⟨w⁻¹ ^ N, 0, 0, 0⟩ with hC
  have hu (i : ℕ) : ((C.u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ i =
      (z ^ N) ^ i := by
    simp [hC, hw]
  have hb₁ : log (Valued.v W.a₁) ≤ M :=
    le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans le_sup_left
  have hb₂ : log (Valued.v W.a₂) ≤ M :=
    le_sup_right.trans <| le_sup_left.trans <| le_sup_left.trans <| le_sup_left.trans le_sup_left
  have hb₃ : log (Valued.v W.a₃) ≤ M :=
    le_sup_right.trans <| le_sup_left.trans <| le_sup_left.trans le_sup_left
  have hb₄ : log (Valued.v W.a₄) ≤ M := le_sup_right.trans <| le_sup_left.trans le_sup_left
  have hb₆ : log (Valued.v W.a₆) ≤ M := le_sup_right.trans le_sup_left
  refine ⟨C, ⟨⟨_, key W.a₁ hb₁ le_rfl⟩, ⟨_, key W.a₂ hb₂ one_le_two⟩,
    ⟨_, key W.a₃ hb₃ (i := 3) (by lia)⟩, ⟨_, key W.a₄ hb₄ (i := 4) (by lia)⟩,
    ⟨_, key W.a₆ hb₆ (i := 6) (by lia)⟩⟩, ?_⟩
  ext : 1
  · change (z ^ N) ^ 1 * W.a₁ = (C • W).a₁
    rw [variableChange_a₁, ← hu 1]
    ring
  · change (z ^ N) ^ 2 * W.a₂ = (C • W).a₂
    rw [variableChange_a₂, ← hu 2]
    ring
  · change (z ^ N) ^ 3 * W.a₃ = (C • W).a₃
    rw [variableChange_a₃, ← hu 3]
    ring
  · change (z ^ N) ^ 4 * W.a₄ = (C • W).a₄
    rw [variableChange_a₄, ← hu 4]
    ring
  · change (z ^ N) ^ 6 * W.a₆ = (C • W).a₆
    rw [variableChange_a₆, ← hu 6]
    ring

end IntegralModel

end WeierstrassCurve.Affine

end
