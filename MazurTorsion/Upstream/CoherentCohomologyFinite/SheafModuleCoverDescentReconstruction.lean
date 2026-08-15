/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverEpimorphism

/-!
# Reconstructing a module from its cover descent datum

The canonical restrictions of a module to the charts of a scheme glue
datum, equipped with their canonical overlap transitions, descend back to
the original module.  This records the reconstruction morphism and proves
that it is an isomorphism by checking on the gluing charts.
-/

open CategoryTheory Limits


noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

/-- The canonical morphism from a module to the descent gluing of all
its chart restrictions. -/
noncomputable def coverRestrictionGlueUnit
    (W : D.glued.Modules) :
    W ⟶
      glue D
        (coverRestriction D W)
        (coverRestrictionTransition D W)
        (coverRestrictionTransition_self D W)
        (coverRestrictionTransition_cocycle D W) :=
  glueLift D
    (coverRestriction D W)
    (coverRestrictionTransition D W)
    (coverRestrictionTransition_self D W)
    (coverRestrictionTransition_cocycle D W)
    (fun i =>
      (pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _
        (𝟙 ((pullback (D.ι i)).obj W)))
    (by
      intro p
      apply
        (glueLift_cond_iff D
          (coverRestriction D W)
          (coverRestrictionTransition D W)
          (fun i => 𝟙 ((pullback (D.ι i)).obj W))
          p.1 p.2).2
      let P :=
        (pullbackComp
          (D.f p.1 p.2) (D.ι p.1)).app W
      let Q :
          (pullback
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj
              ((pullback (D.ι p.2)).obj W) ≅
            (pullback
              ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫
                D.ι p.2)).obj W :=
        (pullbackComp
          (D.t p.1 p.2 ≫ D.f p.2 p.1)
          (D.ι p.2)).app W
      let C :=
        (pullbackCongr
          (show
            (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 =
              D.f p.1 p.2 ≫ D.ι p.1 by
            rw [Category.assoc]
            exact D.glue_condition p.1 p.2)).app W
      have hleft :
          P.inv ≫
              (pullback (D.f p.1 p.2)).map
                (𝟙 ((pullback (D.ι p.1)).obj W)) =
            P.inv := by
        exact
          (congrArg (fun z => P.inv ≫ z)
            ((pullback (D.f p.1 p.2)).map_id
              ((pullback (D.ι p.1)).obj W))).trans
            (Category.comp_id _)
      have hright :
          C.inv ≫ Q.inv ≫
              (pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).map
                  (𝟙 ((pullback (D.ι p.2)).obj W)) ≫
              (coverRestrictionTransition D W p.1 p.2).inv =
          C.inv ≫ Q.inv ≫
              (coverRestrictionTransition D W p.1 p.2).inv := by
        have hmap :
            (pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).map
                (𝟙 ((pullback (D.ι p.2)).obj W)) =
              𝟙 ((pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj
                  ((pullback (D.ι p.2)).obj W)) := by
          exact
            (pullback
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).map_id
                ((pullback (D.ι p.2)).obj W)
        rw [hmap]
        simp only [Category.id_comp]
      have hcore :
          P.inv =
            C.inv ≫ Q.inv ≫
              (coverRestrictionTransition D W p.1 p.2).inv := by
        have hg :
            coverRestrictionTransition D W p.1 p.2 =
              P ≪≫ C.symm ≪≫ Q.symm := by
          rfl
        rw [hg]
        simp
      exact hleft.trans (hcore.trans hright.symm))

/-- On a chart, the reconstruction morphism followed by the effective
descent restriction is the identity. -/
lemma pullback_map_coverRestrictionGlueUnit
    (W : D.glued.Modules) (i : D.J) :
    (pullback (D.ι i)).map
        (coverRestrictionGlueUnit D W) ≫
      glueRestrictionHom D
        (coverRestriction D W)
        (coverRestrictionTransition D W)
        (coverRestrictionTransition_self D W)
        (coverRestrictionTransition_cocycle D W) i =
      𝟙 (coverRestriction D W i) := by
  unfold coverRestrictionGlueUnit
  rw [pullback_map_glueLift_glueRestrictionHom]
  exact Equiv.symm_apply_apply _ _

/-- The canonical cover-descent reconstruction morphism is invertible. -/
instance isIso_coverRestrictionGlueUnit
    (W : D.glued.Modules) :
    IsIso (coverRestrictionGlueUnit D W) := by
  apply isIso_of_pullback_isIso D
  intro i
  let r :=
    glueRestrictionHom D
      (coverRestriction D W)
      (coverRestrictionTransition D W)
      (coverRestrictionTransition_self D W)
      (coverRestrictionTransition_cocycle D W) i
  letI : IsIso r :=
    isIso_glueRestrictionHom D
      (coverRestriction D W)
      (coverRestrictionTransition D W)
      (coverRestrictionTransition_self D W)
      (coverRestrictionTransition_cocycle D W) i
  have hcomp :
      (pullback (D.ι i)).map
          (coverRestrictionGlueUnit D W) ≫ r =
        𝟙 (coverRestriction D W i) :=
    pullback_map_coverRestrictionGlueUnit D W i
  haveI :
      IsIso
        ((pullback (D.ι i)).map
          (coverRestrictionGlueUnit D W) ≫ r) := by
    rw [hcomp]
    infer_instance
  exact
    IsIso.of_isIso_comp_right
      ((pullback (D.ι i)).map
        (coverRestrictionGlueUnit D W)) r

/-- Canonical reconstruction of a module from its cover restrictions. -/
noncomputable def coverRestrictionGlueIso
    (W : D.glued.Modules) :
    W ≅
      glue D
        (coverRestriction D W)
        (coverRestrictionTransition D W)
        (coverRestrictionTransition_self D W)
        (coverRestrictionTransition_cocycle D W) :=
  asIso (coverRestrictionGlueUnit D W)

end AlgebraicGeometry.Scheme.Modules
