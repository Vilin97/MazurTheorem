/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Separatedness descent through finite surjections

A finite surjective cover of the source detects separatedness when the
composite is proper.  The proof descends universal closedness of the
diagonal along the finite surjective product cover.  No flatness hypothesis
is needed.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian

open _root_.AlgebraicGeometry

/-- If `X ⟶ Y` is finite and surjective and `X ⟶ S` is proper, then
`Y ⟶ S` is separated.  This is the separatedness part of proper descent
through a finite surjection. -/
theorem isSeparated_of_finite_surjective_comp_isProper
    {X Y S : Scheme.{u}} (q : X ⟶ Y) (p : Y ⟶ S)
    [IsFinite q] [Surjective q] [IsProper (q ≫ p)] : IsSeparated p := by
  let r := pullback.mapDesc q q p
  let c := pullback.map (q ≫ p) (q ≫ p) p p q q (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)
  let d := pullback.diagonal p
  let sR := pullback.fst q q ≫ (q ≫ p)
  let sT := pullback.fst (q ≫ p) (q ≫ p) ≫ (q ≫ p)
  letI : IsProper sR := by
    dsimp only [sR]
    infer_instance
  letI : IsProper sT := by
    dsimp only [sT]
    infer_instance
  have hrs : r ≫ sT = sR := by
    dsimp only [r, sT, sR, pullback.mapDesc, pullback.map]
    simp only [Category.assoc, pullback.lift_fst_assoc, Category.id_comp]
  letI : IsProper (r ≫ sT) := by
    rw [hrs]
    infer_instance
  letI : IsSeparated sT := IsProper.toIsSeparated
  letI : IsProper r := IsProper.of_comp r sT
  letI : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Surjective : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  letI : MorphismProperty.RespectsIso
      (@UniversallyClosed : MorphismProperty Scheme.{u}) :=
    universallyClosed_respectsIso
  have hcSurjective : Surjective c := by
    dsimp only [c]
    exact MorphismProperty.pullbackMap (P := @Surjective)
      (inferInstanceAs (Surjective q)) (inferInstanceAs (Surjective q)) rfl rfl
  have hcFinite : IsFinite c := by
    dsimp only [c]
    exact MorphismProperty.pullbackMap (P := @IsFinite)
      (inferInstanceAs (IsFinite q)) (inferInstanceAs (IsFinite q)) rfl rfl
  letI : Surjective c := hcSurjective
  letI : IsFinite c := hcFinite
  have hpb : IsPullback (pullback.fst q q ≫ q) r d c := by
    simpa only [r, c, d] using pullback_map_diagonal_isPullback q q p
  have hbaseChange : UniversallyClosed (pullback.fst c d) := by
    exact (MorphismProperty.cancel_left_of_respectsIso @UniversallyClosed
      hpb.flip.isoPullback.hom (pullback.fst c d)).mp
        (by simpa only [hpb.flip.isoPullback_hom_fst] using
          (inferInstance : UniversallyClosed r))
  letI : UniversallyClosed (pullback.fst c d) := hbaseChange
  letI : UniversallyClosed c := inferInstance
  letI : Surjective (pullback.snd c d) := by
    dsimp only [d]
    infer_instance
  have hcomp : UniversallyClosed (pullback.snd c d ≫ d) := by
    have heq : pullback.snd c d ≫ d = pullback.fst c d ≫ c :=
      (pullback.condition (f := c) (g := d)).symm
    rw [heq]
    infer_instance
  letI : UniversallyClosed (pullback.snd c d ≫ d) := hcomp
  letI : UniversallyClosed d :=
    UniversallyClosed.of_comp_surjective (pullback.snd c d) d
  haveI : IsPreimmersion d := by
    dsimp only [d]
    infer_instance
  haveI : IsClosedImmersion d :=
    IsClosedImmersion.of_isPreimmersion d d.isClosedMap.isClosed_range
  exact ⟨inferInstance⟩

end MazurTorsion.AlgebraicGeometry.Jacobian
