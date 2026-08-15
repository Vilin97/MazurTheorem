/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Morphisms from the unit module over an ambient open

A section of a module sheaf on an open `U` restricts coherently to every
object of the slice site `Over U`.  This file packages the corresponding
morphism from the unit module of the slice-site restriction.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- Restriction of a section on `U` to one object of the slice site. -/
def restrictOpenSection
    (x : M.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (M.over U).val.obj V :=
  (M.over U).val.map
    (Over.homMk V.unop.hom :
      V.unop ⟶ Over.mk (𝟙 U)).op x

lemma restrictOpenSection_naturality
    (x : M.val.obj (op U)) {V W : (Over U)ᵒᵖ}
    (f : V ⟶ W) :
    (M.over U).val.map f (restrictOpenSection M U x V) =
      restrictOpenSection M U x W := by
  change
    M.val.map f.unop.left.op
        (M.val.map V.unop.hom.op x) =
      M.val.map W.unop.hom.op x
  calc
    _ = M.val.map
          (V.unop.hom.op ≫ f.unop.left.op) x :=
      ConcreteCategory.congr_hom
        (M.val.map_comp
          V.unop.hom.op f.unop.left.op).symm x
    _ = M.val.map W.unop.hom.op x := by
      rw [← op_comp, f.unop.w]

/-- A section on `U`, regarded as a coherent section of `M.over U`. -/
def sectionsOfOpen (x : M.val.obj (op U)) :
    (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (restrictOpenSection M U x)
    (fun {V W} f =>
      restrictOpenSection_naturality
        (M := M) (U := U) x (V := V) (W := W) f)

/-- The slice-site morphism from the unit module determined by a section
on the ambient open `U`. -/
def homOfOpenSection (x : M.val.obj (op U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm (sectionsOfOpen M U x)

/-- The local morphism is multiplication by the restriction of its
defining section. -/
theorem homOfOpenSection_app
    (x : M.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (r : (X.ringCatSheaf.over U).obj.obj V) :
    (homOfOpenSection M U x).val.app V r =
      r • restrictOpenSection M U x V := by
  change
    ((LinearMap.ringLmapEquivSelf
      ((X.ringCatSheaf.over U).obj.obj V) ℤ
      ((M.over U).val.obj V)).symm
        (restrictOpenSection M U x V)) r = _
  rw [LinearMap.ringLmapEquivSelf_symm_apply,
    LinearMap.smulRight_apply]
  change r • restrictOpenSection M U x V =
    r • restrictOpenSection M U x V
  rfl

/-- On a subopen `V ≤ U`, the local morphism sends `1` to the restriction
of its defining section. -/
@[simp]
theorem homOfOpenSection_app_one
    (x : M.val.obj (op U)) (V : X.Opens) (hV : V ≤ U) :
    (homOfOpenSection M U x).val.app
        (op (Over.mk (homOfLE hV : V ⟶ U)))
        (1 : X.ringCatSheaf.obj.obj (op V)) =
      M.val.map (homOfLE hV).op x := by
  change
    ((M.over U).unitHomEquiv
      ((M.over U).unitHomEquiv.symm
        (sectionsOfOpen M U x))).val
          (op (Over.mk (homOfLE hV : V ⟶ U))) = _
  rw [Equiv.apply_symm_apply]
  change restrictOpenSection M U x
      (op (Over.mk (homOfLE hV : V ⟶ U))) = _
  unfold restrictOpenSection
  exact ConcreteCategory.congr_hom rfl x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
