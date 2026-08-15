/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Uniform bounds for finite families of eventual statements

If every member of a finite family holds above some natural-number
bound, the family has one common bound.
-/

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- Finitely many eventual upper-tail properties have one common
natural-number bound. -/
theorem exists_uniform_eventual_bound
    {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop)
    (hP :
      ∀ i, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → P i n) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ i, P i n := by
  classical
  choose bound hbound using hP
  let b := Finset.univ.sup bound
  refine ⟨b, fun n hn i => hbound i n ?_⟩
  exact
    (Finset.le_sup
      (f := bound)
      (Finset.mem_univ i)).trans hn

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
