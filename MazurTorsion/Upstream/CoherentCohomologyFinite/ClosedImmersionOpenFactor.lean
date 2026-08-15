/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Restricting a closed-then-open factorization

If a morphism factors as a closed immersion followed by an open
immersion, then restricting its target to the range of the open
immersion recovers a closed immersion.  This is the categorical local
fact used for graphs that are closed over their domain of definition.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- A factorization through a monomorphism identifies the source with
the corresponding pullback. -/
theorem isIso_pullbackLift_of_comp_mono
    {X U Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ U) (j : U ⟶ Y)
    [Mono j] (h : f = g ≫ j) :
    IsIso
      (pullback.lift (𝟙 X) g (by simpa [h])) := by
  apply IsIso.mk
  refine ⟨pullback.fst f j, ?_, ?_⟩
  · exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd,
        Category.id_comp]
      rw [← cancel_mono j, Category.assoc, ← h,
        pullback.condition]

/-- If `f = g ≫ j`, with `g` closed and `j` open, then the restriction
of `f` to the range of `j` is a closed immersion. -/
theorem isClosedImmersion_morphismRestrict_opensRange_of_factor
    {X U Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ U) (j : U ⟶ Y)
    [IsClosedImmersion g] [IsOpenImmersion j]
    (h : f = g ≫ j) :
    IsClosedImmersion (f ∣_ j.opensRange) := by
  let t : X ⟶ pullback f j :=
    pullback.lift (𝟙 X) g (by simpa [h])
  letI : IsIso t :=
    isIso_pullbackLift_of_comp_mono f g j h
  have hsnd :
      IsClosedImmersion (pullback.snd f j) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso
      @IsClosedImmersion t]
    have ht : t ≫ pullback.snd f j = g := by
      exact pullback.lift_snd _ _ _
    rw [ht]
    infer_instance
  rw [MorphismProperty.arrow_mk_iso_iff
    @IsClosedImmersion (morphismRestrictOpensRange f j)]
  exact hsnd

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
