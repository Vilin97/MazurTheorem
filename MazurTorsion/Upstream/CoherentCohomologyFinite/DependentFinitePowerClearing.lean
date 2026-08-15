/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FinitePowerClearing

/-!
# Clearing powers in a dependent finite family

In projective-chart arguments both the scalar ring and the module of
sections depend on the chosen chart.  The elementary finite-maximum
argument still gives one exponent for the whole family.
-/

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- If every member of a finite dependent family is killed by a power of
its chosen scalar, then one exponent kills all members simultaneously. -/
theorem exists_uniform_pow_smul_eq_zero_dependent
    {ι : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommSemiring (R i)]
    (M : ι → Type*) [∀ i, AddCommMonoid (M i)]
    [∀ i, Module (R i) (M i)]
    (f : ∀ i, R i) (x : ∀ i, M i)
    (h : ∀ i, ∃ n : ℕ, f i ^ n • x i = 0) :
    ∃ N : ℕ, ∀ i, f i ^ N • x i = 0 := by
  choose n hn using h
  let N : ℕ := ⨆ i, n i
  refine ⟨N, fun i => ?_⟩
  have hni : n i ≤ N :=
    le_ciSup (Finite.bddAbove_range n) i
  rw [show N = (N - n i) + n i by
      exact (Nat.sub_add_cancel hni).symm,
    pow_add, mul_smul, hn, smul_zero]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
