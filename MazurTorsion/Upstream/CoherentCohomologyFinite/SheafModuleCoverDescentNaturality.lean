/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescent

/-!
# Naturality of canonical cover descent

The canonical overlap comparison obtained by restricting a global module
is natural in the global module.  This is the chartwise compatibility
needed when cover descent is modified by scalar transition functions.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{u})

/-- A global module morphism commutes with the canonical transition
isomorphisms on every overlap. -/
lemma coverRestrictionTransition_naturality
    {W Z : D.glued.Modules} (φ : W ⟶ Z)
    (i j : D.J) :
    (pullback (D.f i j)).map
        ((pullback (D.ι i)).map φ) ≫
      (coverRestrictionTransition D Z i j).hom =
      (coverRestrictionTransition D W i j).hom ≫
      (pullback (D.t i j ≫ D.f j i)).map
        ((pullback (D.ι j)).map φ) := by
    change
      (pullback (D.ι i) ⋙ pullback (D.f i j)).map φ ≫
          (pullbackComp (D.f i j) (D.ι i)).hom.app Z ≫
          (pullbackCongr
            (show D.f i j ≫ D.ι i =
                (D.t i j ≫ D.f j i) ≫ D.ι j by
              rw [Category.assoc]
              exact (D.glue_condition i j).symm)).hom.app Z ≫
          (pullbackComp
            (D.t i j ≫ D.f j i) (D.ι j)).inv.app Z =
        (pullbackComp (D.f i j) (D.ι i)).hom.app W ≫
          (pullbackCongr
            (show D.f i j ≫ D.ι i =
                (D.t i j ≫ D.f j i) ≫ D.ι j by
              rw [Category.assoc]
              exact (D.glue_condition i j).symm)).hom.app W ≫
          (pullbackComp
            (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
          (pullback (D.ι j) ⋙
            pullback (D.t i j ≫ D.f j i)).map φ
    slice_lhs 1 2 =>
      rw [(pullbackComp
        (D.f i j) (D.ι i)).hom.naturality φ]
    slice_lhs 2 3 =>
      rw [(pullbackCongr
        (show D.f i j ≫ D.ι i =
            (D.t i j ≫ D.f j i) ≫ D.ι j by
          rw [Category.assoc]
          exact (D.glue_condition i j).symm)).hom.naturality φ]
    slice_lhs 3 4 =>
      rw [(pullbackComp
        (D.t i j ≫ D.f j i) (D.ι j)).inv.naturality φ]

end AlgebraicGeometry.Scheme.Modules
