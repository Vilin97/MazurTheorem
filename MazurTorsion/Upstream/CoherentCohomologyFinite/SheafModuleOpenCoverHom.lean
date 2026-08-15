/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Gluing morphisms of module sheaves over an open cover

The internal Hom between two sheaves is again a sheaf.  We use this to
glue morphisms of module sheaves from compatible morphisms on an open cover.
Linearity of the glued underlying additive morphism is checked locally.
-/

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenCoverHom

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (S M : X.Modules)
  {ι : Type u} (U : ι → X.Opens)

/-- The underlying internal-Hom section determined by a morphism on the
slice site over an open. -/
abbrev localUnderlying
    (i : ι) (f : S.over (U i) ⟶ M.over (U i)) :
    (CategoryTheory.presheafHom
      S.val.presheaf M.val.presheaf).obj (op (U i)) :=
  (PresheafOfModules.toPresheaf
    (X.ringCatSheaf.over (U i)).obj).map f.val

/-- Compatibility of local module morphisms, expressed in the internal-Hom
sheaf. -/
abbrev Compatible
    (f : ∀ i, S.over (U i) ⟶ M.over (U i)) : Prop :=
  TopCat.Presheaf.IsCompatible
    (CategoryTheory.presheafHom
      S.val.presheaf M.val.presheaf)
    U (fun i => localUnderlying S M U i (f i))

variable (f : ∀ i, S.over (U i) ⟶ M.over (U i))
  (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
  (hf : Compatible S M U f)

/-- The glued section of the internal-Hom sheaf over the terminal open. -/
def gluedUnderlyingOverTop :
    (CategoryTheory.presheafHom
      S.val.presheaf M.val.presheaf).obj (op (⊤ : X.Opens)) :=
  (TopCat.Sheaf.existsUnique_gluing'
    ⟨CategoryTheory.presheafHom S.val.presheaf M.val.presheaf,
      M.isSheaf.hom S.val.presheaf⟩
    U ⊤ (fun i => homOfLE le_top) hcover
    (fun i => localUnderlying S M U i (f i)) hf).choose

/-- The underlying additive presheaf morphism obtained from the glued
internal-Hom section. -/
def gluedUnderlying :
    S.val.presheaf ⟶ M.val.presheaf where
  app V :=
    (gluedUnderlyingOverTop S M U f hcover hf).app
      (op (Over.mk (homOfLE le_top : V.unop ⟶ (⊤ : X.Opens))))
  naturality := by
    intro V W g
    let a : Over.mk (homOfLE le_top : W.unop ⟶ (⊤ : X.Opens)) ⟶
        Over.mk (homOfLE le_top : V.unop ⟶ (⊤ : X.Opens)) :=
      Over.homMk g.unop
    exact
      (gluedUnderlyingOverTop S M U f hcover hf).naturality a.op

/-- On an open contained in a cover member, the glued underlying morphism
is the prescribed local morphism. -/
lemma gluedUnderlying_app_eq
    (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    (gluedUnderlying S M U f hcover hf).app (op V) =
      ((PresheafOfModules.toPresheaf
        (X.ringCatSheaf.over (U i)).obj).map
          (f i).val).app
            (op (Over.mk (homOfLE hV : V ⟶ U i))) := by
  have hglue :=
    (TopCat.Sheaf.existsUnique_gluing'
      ⟨CategoryTheory.presheafHom S.val.presheaf M.val.presheaf,
        M.isSheaf.hom S.val.presheaf⟩
      U ⊤ (fun i => homOfLE le_top) hcover
      (fun i => localUnderlying S M U i (f i)) hf).choose_spec.1 i
  change
    (CategoryTheory.presheafHom
      S.val.presheaf M.val.presheaf).map
        (homOfLE le_top : U i ⟶ (⊤ : X.Opens)).op
        (gluedUnderlyingOverTop S M U f hcover hf) =
      localUnderlying S M U i (f i) at hglue
  change
    (gluedUnderlyingOverTop S M U f hcover hf).app
        (op (Over.mk
          (homOfLE le_top : V ⟶ (⊤ : X.Opens)))) =
      (localUnderlying S M U i (f i)).app
        (op (Over.mk (homOfLE hV : V ⟶ U i)))
  rw [← hglue]
  exact
    (CategoryTheory.presheafHom_map_app
      (homOfLE hV : V ⟶ U i)
      (homOfLE le_top : U i ⟶ (⊤ : X.Opens))
      (homOfLE le_top : V ⟶ (⊤ : X.Opens))
      (Subsingleton.elim _ _)
      (gluedUnderlyingOverTop S M U f hcover hf)).symm

/-- The glued underlying additive morphism is linear. -/
lemma gluedUnderlying_smul
    (V : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj V)
    (x : S.val.obj V) :
    (gluedUnderlying S M U f hcover hf).app V (r • x) =
      r • (gluedUnderlying S M U f hcover hf).app V x := by
  apply M.isSheaf.section_ext
  intro p hp
  have hpU : p ∈ ⨆ i, U i :=
    hcover (show p ∈ (⊤ : X.Opens) by trivial)
  rw [Opens.mem_iSup] at hpU
  obtain ⟨i, hpi⟩ := hpU
  let W : X.Opens := V.unop ⊓ U i
  let hWV : W ≤ V.unop := inf_le_left
  let hWU : W ≤ U i := inf_le_right
  refine ⟨W, hWV, ⟨hp, hpi⟩, ?_⟩
  have hlocal :=
    gluedUnderlying_app_eq (S := S) (M := M)
      (U := U) (f := f) (hcover := hcover) (hf := hf)
      i W hWU
  have hnatx :
      (gluedUnderlying S M U f hcover hf).app (op W)
          (S.val.map (homOfLE hWV).op x) =
        M.val.map (homOfLE hWV).op
          ((gluedUnderlying S M U f hcover hf).app V x) := by
    exact congr($((gluedUnderlying S M U f hcover hf).naturality
      (homOfLE hWV).op) x)
  have hnats :
      (gluedUnderlying S M U f hcover hf).app (op W)
          (S.val.map (homOfLE hWV).op (r • x)) =
        M.val.map (homOfLE hWV).op
          ((gluedUnderlying S M U f hcover hf).app V (r • x)) := by
    exact congr($((gluedUnderlying S M U f hcover hf).naturality
      (homOfLE hWV).op) (r • x))
  change
    M.val.map (homOfLE hWV).op
        ((gluedUnderlying S M U f hcover hf).app V (r • x)) =
      M.val.map (homOfLE hWV).op
        (r • (gluedUnderlying S M U f hcover hf).app V x)
  rw [← hnats, S.val.map_smul, hlocal]
  let A : (Over (U i))ᵒᵖ :=
    op (Over.mk (homOfLE hWU : W ⟶ U i))
  let rW : (X.ringCatSheaf.over (U i)).obj.obj A :=
    X.ringCatSheaf.obj.map (homOfLE hWV).op r
  let sx : (S.over (U i)).val.obj A :=
    S.val.map (homOfLE hWV).op x
  let gx : (M.over (U i)).val.obj A :=
    (gluedUnderlying S M U f hcover hf).app (op W)
      (S.val.map (homOfLE hWV).op x)
  let mx : (M.over (U i)).val.obj A :=
    M.val.map (homOfLE hWV).op
      ((gluedUnderlying S M U f hcover hf).app V x)
  have hlocalx : (f i).val.app A sx = gx := by
    exact (ConcreteCategory.congr_hom hlocal _).symm
  have hnatx' : gx = mx := hnatx
  have hmapsmul :
      M.val.map (homOfLE hWV).op
          (r • (gluedUnderlying S M U f hcover hf).app V x) =
        rW • mx := by
    exact M.val.map_smul (homOfLE hWV).op r _
  change
    (f i).val.app A (rW • sx) =
      M.val.map (homOfLE hWV).op
        (r • (gluedUnderlying S M U f hcover hf).app V x)
  have hmain :
      (f i).val.app A (rW • sx) = rW • mx := by
    calc
      (f i).val.app A (rW • sx) =
          rW • (f i).val.app A sx :=
        map_smul ((f i).val.app A).hom rW sx
      _ = rW • gx := congrArg (fun z => rW • z) hlocalx
      _ = rW • mx := congrArg (fun z => rW • z) hnatx'
  exact hmain.trans hmapsmul.symm

/-- Glue compatible morphisms of module sheaves on an open cover. -/
def glue :
    S ⟶ M :=
  ⟨PresheafOfModules.homMk
    (gluedUnderlying S M U f hcover hf)
    (gluedUnderlying_smul (S := S) (M := M)
      (U := U) (f := f) (hcover := hcover) (hf := hf))⟩

/-- Restriction of the glued morphism to a cover member is the original
local morphism. -/
theorem glue_over (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map
        (glue S M U f hcover hf) =
      f i := by
  ext V
  exact ConcreteCategory.congr_hom
    (gluedUnderlying_app_eq (S := S) (M := M)
      (U := U) (f := f) (hcover := hcover) (hf := hf)
      i V.unop.left (leOfHom V.unop.hom)) _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenCoverHom
