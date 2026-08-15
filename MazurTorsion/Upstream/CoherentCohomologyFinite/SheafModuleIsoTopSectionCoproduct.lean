/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionTransport

/-!
# Coproduct transport across a scheme isomorphism

The free morphism attached to a family of top sections can be transported
through restriction along a scheme isomorphism.  Its components are the
top-section maps attached to `isoTransportedTopSection`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)

/-- The coproduct map transported from `X` to `Y` through restriction
along the inverse of `e`. -/
def isoTransportedTopSectionCoproduct
    {ι : Type u}
    (s : ι → Γ(M.restrict e.hom, ⊤)) :
    SheafOfModules.free (R := Y.ringCatSheaf) ι ⟶ M := by
  letI : Limits.PreservesColimitsOfSize.{u, u}
      (restrictFunctor e.inv) :=
    restrictPreservesColimits e.inv
  letI : Limits.PreservesColimitsOfSize.{0, 0}
      (restrictFunctor e.inv) :=
    Limits.preservesColimitsOfSize_shrink _
  letI hpres :
      Limits.PreservesColimitsOfShape
        (Discrete ι) (restrictFunctor e.inv) := by
    infer_instance
  let freeIso :
      SheafOfModules.free (R := Y.ringCatSheaf) ι ≅
        (restrictFunctor e.inv).obj
          (SheafOfModules.free (R := X.ringCatSheaf) ι) :=
    @SheafOfModules.mapFreeIso
      _ _ _ _ _ _ _ _ _ _ _ _
      (restrictFunctor e.inv) ι hpres
      (restrictUnitIso e.inv).symm
  let localMap :
      SheafOfModules.free
          (R := X.ringCatSheaf) ι ⟶
        M.restrict e.hom :=
    Limits.Sigma.desc
      (fun a =>
        homOfTopSection
          (M.restrict e.hom) (s a))
  exact
    (freeIso.hom ≫
      (restrictFunctor e.inv).map localMap) ≫
      (restrictIsoOfIso e.symm M).hom

/-- Each component of the transported coproduct is the top-section map
defined by the corresponding transported section. -/
theorem ι_isoTransportedTopSectionCoproduct
    {ι : Type u}
    (s : ι → Γ(M.restrict e.hom, ⊤)) (a : ι) :
    Limits.Sigma.ι
          (fun _ : ι =>
            SheafOfModules.unit Y.ringCatSheaf) a ≫
        isoTransportedTopSectionCoproduct e M s =
      homOfTopSection M
        (isoTransportedTopSection e M (s a)) := by
  letI : Limits.PreservesColimitsOfSize.{u, u}
      (restrictFunctor e.inv) :=
    restrictPreservesColimits e.inv
  letI : Limits.PreservesColimitsOfSize.{0, 0}
      (restrictFunctor e.inv) :=
    Limits.preservesColimitsOfSize_shrink _
  letI hpres :
      Limits.PreservesColimitsOfShape
        (Discrete ι) (restrictFunctor e.inv) := by
    infer_instance
  let freeIso :
      SheafOfModules.free (R := Y.ringCatSheaf) ι ≅
        (restrictFunctor e.inv).obj
          (SheafOfModules.free (R := X.ringCatSheaf) ι) :=
    @SheafOfModules.mapFreeIso
      _ _ _ _ _ _ _ _ _ _ _ _
      (restrictFunctor e.inv) ι hpres
      (restrictUnitIso e.inv).symm
  let localMap :
      SheafOfModules.free
          (R := X.ringCatSheaf) ι ⟶
        M.restrict e.hom :=
    Limits.Sigma.desc
      (fun a =>
        homOfTopSection (M.restrict e.hom) (s a))
  let sourceι :
      SheafOfModules.unit X.ringCatSheaf ⟶
        SheafOfModules.free (R := X.ringCatSheaf) ι :=
    Limits.Sigma.ι
      (fun _ : ι =>
        SheafOfModules.unit X.ringCatSheaf) a
  let targetι :
      SheafOfModules.unit Y.ringCatSheaf ⟶
        SheafOfModules.free (R := Y.ringCatSheaf) ι :=
    Limits.Sigma.ι
      (fun _ : ι =>
        SheafOfModules.unit Y.ringCatSheaf) a
  let unitInv :
      SheafOfModules.unit Y.ringCatSheaf ⟶
        (restrictFunctor e.inv).obj
          (SheafOfModules.unit X.ringCatSheaf) :=
    (restrictUnitIso e.inv).inv
  let cancelHom :
      (restrictFunctor e.inv).obj (M.restrict e.hom) ⟶ M :=
    (restrictIsoOfIso e.symm M).hom
  have hι :
      targetι ≫ freeIso.hom =
        unitInv ≫
          (restrictFunctor e.inv).map sourceι :=
    @SheafOfModules.ιFree_mapFreeIso_hom
      _ _ _ _ _ _ _ _ _ _ _ _
      (restrictFunctor e.inv) ι hpres
      (restrictUnitIso e.inv).symm a
  have hlocal :
      sourceι ≫ localMap =
        homOfTopSection
          (M.restrict e.hom) (s a) := by
    dsimp only [sourceι, localMap]
    exact Limits.Sigma.ι_desc _ _
  have hassoc :
      targetι ≫
          (freeIso.hom ≫
            (restrictFunctor e.inv).map localMap) =
        (targetι ≫ freeIso.hom) ≫
          (restrictFunctor e.inv).map localMap :=
    (Category.assoc _ _ _).symm
  have hmain :
      targetι ≫ isoTransportedTopSectionCoproduct e M s =
        (unitInv ≫
          (restrictFunctor e.inv).map
            (homOfTopSection
              (M.restrict e.hom) (s a))) ≫
          cancelHom := by
    unfold isoTransportedTopSectionCoproduct
    change
      targetι ≫
          ((freeIso.hom ≫
            (restrictFunctor e.inv).map localMap) ≫
          cancelHom) = _
    have h₁ :
        targetι ≫
            ((freeIso.hom ≫
              (restrictFunctor e.inv).map localMap) ≫ cancelHom) =
          (targetι ≫
            (freeIso.hom ≫
              (restrictFunctor e.inv).map localMap)) ≫ cancelHom :=
      (Category.assoc _ _ _).symm
    have h₂ :
        (targetι ≫
            (freeIso.hom ≫
              (restrictFunctor e.inv).map localMap)) ≫ cancelHom =
          (((targetι ≫ freeIso.hom) ≫
            (restrictFunctor e.inv).map localMap) ≫ cancelHom) :=
      congrArg (fun q => q ≫ cancelHom) hassoc
    have h₃ :
        (((targetι ≫ freeIso.hom) ≫
            (restrictFunctor e.inv).map localMap) ≫ cancelHom) =
          (((unitInv ≫ (restrictFunctor e.inv).map sourceι) ≫
            (restrictFunctor e.inv).map localMap) ≫ cancelHom) :=
      congrArg
        (fun q =>
          (q ≫ (restrictFunctor e.inv).map localMap) ≫ cancelHom)
        hι
    have hmap :
        (restrictFunctor e.inv).map (sourceι ≫ localMap) =
          (restrictFunctor e.inv).map sourceι ≫
            (restrictFunctor e.inv).map localMap :=
      @Functor.map_comp X.Modules _ Y.Modules _
        (restrictFunctor e.inv) _ _ _ sourceι localMap
    have hinner :
        (unitInv ≫ (restrictFunctor e.inv).map sourceι) ≫
            (restrictFunctor e.inv).map localMap =
          unitInv ≫ (restrictFunctor e.inv).map (sourceι ≫ localMap) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => unitInv ≫ q) hmap.symm)
    have h₄ :
        (((unitInv ≫ (restrictFunctor e.inv).map sourceι) ≫
            (restrictFunctor e.inv).map localMap) ≫ cancelHom) =
          ((unitInv ≫
            (restrictFunctor e.inv).map (sourceι ≫ localMap)) ≫
            cancelHom) := by
      exact congrArg (fun q => q ≫ cancelHom) hinner
    have h₅ :
        ((unitInv ≫
            (restrictFunctor e.inv).map (sourceι ≫ localMap)) ≫
            cancelHom) =
          ((unitInv ≫
            (restrictFunctor e.inv).map
              (homOfTopSection (M.restrict e.hom) (s a))) ≫ cancelHom) :=
      congrArg
        (fun q => (unitInv ≫ (restrictFunctor e.inv).map q) ≫ cancelHom)
        hlocal
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  change targetι ≫ isoTransportedTopSectionCoproduct e M s = _
  rw [hmain]
  exact homOfTopSection_to_isoTransport e M (s a)

/-- The transported map is the coproduct of the transported
top-section maps. -/
theorem isoTransportedTopSectionCoproduct_eq_sigmaDesc
    {ι : Type u}
    (s : ι → Γ(M.restrict e.hom, ⊤)) :
    isoTransportedTopSectionCoproduct e M s =
      Limits.Sigma.desc
        (fun a =>
          homOfTopSection M
            (isoTransportedTopSection e M (s a))) := by
  apply Limits.Sigma.hom_ext
  intro a
  rw [ι_isoTransportedTopSectionCoproduct]
  exact
    (Limits.Sigma.ι_desc
      (fun b : ι =>
        homOfTopSection M
          (isoTransportedTopSection e M (s b))) a).symm

end AlgebraicGeometry.Scheme.Modules
