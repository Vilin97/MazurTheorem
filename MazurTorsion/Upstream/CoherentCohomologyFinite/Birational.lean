/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Birational schemes via a common dense open

This is the form of birationality naturally produced by graph closures:
two schemes contain the same scheme as a dense open subscheme.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- Two schemes are birational when they share a common dense open
subscheme. -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (U : Scheme.{u}) (jX : U ⟶ X) (jY : U ⟶ Y),
    IsOpenImmersion jX ∧
    IsOpenImmersion jY ∧
    Dense (Set.range jX.base) ∧
    Dense (Set.range jY.base)

/-- Birationality is reflexive. -/
theorem isBirational_refl (X : Scheme.{u}) :
    IsBirational X X := by
  refine ⟨X, 𝟙 X, 𝟙 X, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Set.range_eq_univ.mpr
      (ConcreteCategory.bijective_of_isIso
        (𝟙 X : X ⟶ X).base).surjective]
    exact dense_univ
  · rw [Set.range_eq_univ.mpr
      (ConcreteCategory.bijective_of_isIso
        (𝟙 X : X ⟶ X).base).surjective]
    exact dense_univ

/-- Birationality is symmetric. -/
theorem IsBirational.symm
    {X Y : Scheme.{u}} (h : IsBirational X Y) :
    IsBirational Y X := by
  obtain ⟨U, jX, jY, hjX, hjY, hdX, hdY⟩ := h
  exact ⟨U, jY, jX, hjY, hjX, hdY, hdX⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
