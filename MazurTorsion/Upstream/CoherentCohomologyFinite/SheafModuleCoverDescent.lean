/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleEffectiveDescent

/-!
# The canonical descent datum of a global module sheaf

A module sheaf on the glued scheme restricts to every chart of a glue
datum.  The two restrictions to an overlap are canonically isomorphic
because both are pullbacks of the original global sheaf.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{u})

/-- The chartwise restriction of a global module sheaf. -/
abbrev coverRestriction (W : D.glued.Modules) (i : D.J) :
    (D.U i).Modules :=
  (pullback (D.ι i)).obj W

/-- The two routes from an overlap into the glued scheme agree.  Naming
this equality keeps the proof term stable in later pullback-pasting
arguments. -/
theorem coverRestrictionComposite_eq (i j : D.J) :
    D.f i j ≫ D.ι i =
      (D.t i j ≫ D.f j i) ≫ D.ι j := by
  rw [Category.assoc]
  exact (D.glue_condition i j).symm

/-- The canonical transition isomorphism between the two overlap
restrictions of a global module sheaf. -/
def coverRestrictionTransition (W : D.glued.Modules) (i j : D.J) :
    (pullback (D.f i j)).obj (coverRestriction D W i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj
        (coverRestriction D W j) :=
  (pullbackComp (D.f i j) (D.ι i)).app W ≪≫
    (pullbackCongr
      (coverRestrictionComposite_eq D i j)).app W ≪≫
    (pullbackComp
      (D.t i j ≫ D.f j i) (D.ι j)).symm.app W

end AlgebraicGeometry.Scheme.Modules
