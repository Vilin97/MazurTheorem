/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Morphisms from the unit module and top sections

On an opens site, a section over the terminal open restricts canonically to
every open.  Through `SheafOfModules.unitHomEquiv`, this gives the associated
module morphism from the unit sheaf.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

variable {X : Scheme.{u}} (M : X.Modules)

/-- A section over the terminal open, restricted coherently to every open. -/
def sectionsOfTop (x : M.val.obj (op (⊤ : X.Opens))) :
    M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map
      (homOfLE (show V.unop ≤ (⊤ : X.Opens) from le_top)).op x)
    (by
      intro V W f
      change
        M.val.map f
            (M.val.map (homOfLE le_top).op x) =
          M.val.map (homOfLE le_top).op x
      have hcomp :
          M.val.map f
                (M.val.map (homOfLE le_top).op x) =
              M.val.map ((homOfLE le_top).op ≫ f) x :=
        (ConcreteCategory.congr_hom
          (M.val.map_comp (homOfLE le_top).op f) x).symm
      exact hcomp.trans (by congr 1))

/-- The morphism from the unit module determined by a top section. -/
def homOfTopSection (x : M.val.obj (op (⊤ : X.Opens))) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionsOfTop M x)

/-- The morphism associated to a top section sends `1` on an open to the
restriction of that section. -/
@[simp]
theorem homOfTopSection_app_one
    (x : M.val.obj (op (⊤ : X.Opens))) (V : X.Opens) :
    (homOfTopSection M x).val.app (op V)
        (1 : X.ringCatSheaf.obj.obj (op V)) =
      M.val.map (homOfLE le_top : V ⟶ (⊤ : X.Opens)).op x := by
  change
    (M.unitHomEquiv (M.unitHomEquiv.symm (sectionsOfTop M x))).val (op V) =
      _
  rw [Equiv.apply_symm_apply]
  rfl

/-- At the terminal open, the associated morphism sends `1` to the given
section itself. -/
@[simp]
theorem homOfTopSection_app_top_one
    (x : M.val.obj (op (⊤ : X.Opens))) :
    (homOfTopSection M x).val.app (op (⊤ : X.Opens))
        (1 : X.ringCatSheaf.obj.obj (op ⊤)) = x := by
  rw [homOfTopSection_app_one]
  exact ConcreteCategory.congr_hom (M.val.map_id _) x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom
