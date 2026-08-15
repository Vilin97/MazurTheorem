/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionTransport

/-!
# Coproduct transport for open-section maps

This file packages the coproduct morphism obtained by applying the
open-slice equivalence to a family of top-section maps and proves that its
components are the expected ambient-open section maps.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- The coproduct of the top-section maps on an open subscheme. -/
def restrictedTopSectionCoproduct
    {ι : Type u}
    (s : ι → Γ(M.restrict U.ι, ⊤)) :
    SheafOfModules.free
        (R := (↑U : Scheme).ringCatSheaf) ι ⟶
      M.restrict U.ι :=
  Limits.Sigma.desc
    (fun a =>
      homOfTopSection (M.restrict U.ι) (s a))

/-- The coproduct map obtained by transporting top-section maps through
the open-slice equivalence. -/
def transportedTopSectionCoproduct
    {ι : Type u}
    (s : ι → Γ(M.restrict U.ι, ⊤)) :
    SheafOfModules.free
        (R := X.ringCatSheaf.over U) ι ⟶
      M.over U := by
  let F := (overEquivalence U).functor
  letI : Limits.PreservesColimitsOfSize.{u, u} F :=
    (overEquivalence U).toAdjunction.leftAdjoint_preservesColimits
  exact
    ((SheafOfModules.mapFreeIso F ι
        (unitOverIso U).symm).hom ≫
      F.map (restrictedTopSectionCoproduct M U s)) ≫
      (restrictOverIso U M).hom

/-- A transported coproduct component is the ambient-open section map. -/
theorem ι_transportedTopSectionCoproduct
    {ι : Type u}
    (s : ι → Γ(M.restrict U.ι, ⊤)) (a : ι) :
    Limits.Sigma.ι
          (fun _ : ι =>
            SheafOfModules.unit
              (X.ringCatSheaf.over U)) a ≫
        transportedTopSectionCoproduct M U s =
      homOfOpenSection M U
        ((eqToIso
          (congrArg (fun V => Γ(M, V))
            U.ι_image_top)).hom
          ((M.restrictAppIso U.ι ⊤).hom
            (s a))) := by
  let F := (overEquivalence U).functor
  letI : Limits.PreservesColimitsOfSize.{u, u} F :=
    (overEquivalence U).toAdjunction.leftAdjoint_preservesColimits
  let freeIso :
      SheafOfModules.free (R := X.ringCatSheaf.over U) ι ≅
        F.obj (SheafOfModules.free
          (R := (↑U : Scheme).ringCatSheaf) ι) :=
    SheafOfModules.mapFreeIso F ι (unitOverIso U).symm
  let localMap :
      SheafOfModules.free (R := (↑U : Scheme).ringCatSheaf) ι ⟶
        M.restrict U.ι :=
    restrictedTopSectionCoproduct M U s
  let sourceι :
      SheafOfModules.unit (↑U : Scheme).ringCatSheaf ⟶
        SheafOfModules.free (R := (↑U : Scheme).ringCatSheaf) ι :=
    Limits.Sigma.ι
      (fun _ : ι =>
        SheafOfModules.unit
          (↑U : Scheme).ringCatSheaf) a
  let targetι :
      SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
        SheafOfModules.free (R := X.ringCatSheaf.over U) ι :=
    Limits.Sigma.ι
      (fun _ : ι =>
        SheafOfModules.unit
          (X.ringCatSheaf.over U)) a
  let unitInv :
      SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
        F.obj (SheafOfModules.unit (↑U : Scheme).ringCatSheaf) :=
    (unitOverIso U).inv
  let cancelHom : F.obj (M.restrict U.ι) ⟶ M.over U :=
    (restrictOverIso U M).hom
  have hι :
      targetι ≫ freeIso.hom = unitInv ≫ F.map sourceι :=
    SheafOfModules.ιFree_mapFreeIso_hom
      F ι (unitOverIso U).symm a
  have hlocal :
      sourceι ≫ localMap = homOfTopSection (M.restrict U.ι) (s a) := by
    dsimp only [sourceι, localMap, restrictedTopSectionCoproduct]
    exact Limits.Sigma.ι_desc _ _
  have hassoc :
      targetι ≫ (freeIso.hom ≫ F.map localMap) =
        (targetι ≫ freeIso.hom) ≫ F.map localMap :=
    (Category.assoc _ _ _).symm
  have hmap : F.map (sourceι ≫ localMap) =
      F.map sourceι ≫ F.map localMap := F.map_comp _ _
  have hinner :
      (unitInv ≫ F.map sourceι) ≫ F.map localMap =
        unitInv ≫ F.map (sourceι ≫ localMap) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun q => unitInv ≫ q) hmap.symm)
  have hmain :
      targetι ≫ transportedTopSectionCoproduct M U s =
        (unitInv ≫ F.map
          (homOfTopSection (M.restrict U.ι) (s a))) ≫ cancelHom := by
    unfold transportedTopSectionCoproduct
    change targetι ≫ ((freeIso.hom ≫ F.map localMap) ≫ cancelHom) = _
    have h₁ :
        targetι ≫ ((freeIso.hom ≫ F.map localMap) ≫ cancelHom) =
          (targetι ≫ (freeIso.hom ≫ F.map localMap)) ≫ cancelHom :=
      (Category.assoc _ _ _).symm
    have h₂ :
        (targetι ≫ (freeIso.hom ≫ F.map localMap)) ≫ cancelHom =
          (((targetι ≫ freeIso.hom) ≫ F.map localMap) ≫ cancelHom) :=
      congrArg (fun q => q ≫ cancelHom) hassoc
    have h₃ :
        (((targetι ≫ freeIso.hom) ≫ F.map localMap) ≫ cancelHom) =
          (((unitInv ≫ F.map sourceι) ≫ F.map localMap) ≫ cancelHom) :=
      congrArg (fun q => (q ≫ F.map localMap) ≫ cancelHom) hι
    have h₄ :
        (((unitInv ≫ F.map sourceι) ≫ F.map localMap) ≫ cancelHom) =
          ((unitInv ≫ F.map (sourceι ≫ localMap)) ≫ cancelHom) :=
      congrArg (fun q => q ≫ cancelHom) hinner
    have h₅ :
        ((unitInv ≫ F.map (sourceι ≫ localMap)) ≫ cancelHom) =
          ((unitInv ≫ F.map
            (homOfTopSection (M.restrict U.ι) (s a))) ≫ cancelHom) :=
      congrArg (fun q => (unitInv ≫ F.map q) ≫ cancelHom) hlocal
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  change targetι ≫ transportedTopSectionCoproduct M U s = _
  rw [hmain]
  exact homOfTopSection_to_homOfOpenSection M U (s a)

/-- The transported coproduct is literally the coproduct of the
ambient-open section maps. -/
theorem transportedTopSectionCoproduct_eq_sigmaDesc
    {ι : Type u}
    (s : ι → Γ(M.restrict U.ι, ⊤)) :
    transportedTopSectionCoproduct M U s =
      Limits.Sigma.desc
        (fun a =>
          homOfOpenSection M U
            ((eqToIso
              (congrArg (fun V => Γ(M, V))
                U.ι_image_top)).hom
              ((M.restrictAppIso U.ι ⊤).hom
                (s a)))) := by
  apply Limits.Sigma.hom_ext
  intro a
  rw [ι_transportedTopSectionCoproduct]
  exact
    (Limits.Sigma.ι_desc
      (fun b : ι =>
        homOfOpenSection M U
          ((eqToIso
            (congrArg (fun V => Γ(M, V))
              U.ι_image_top)).hom
            ((M.restrictAppIso U.ι ⊤).hom
              (s b)))) a).symm

end AlgebraicGeometry.Scheme.Modules
