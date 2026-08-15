/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionEpi

/-!
# Transporting top sections through a module-sheaf isomorphism

An isomorphism between two module sheaves on the same scheme transports
top sections and their associated maps from the structure module.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A top section transported through an isomorphism of module sheaves. -/
def moduleIsoTopSection (e : M ≅ N) (x : Γ(M, ⊤)) :
    Γ(N, ⊤) :=
  e.hom.val.app (op (⊤ : X.Opens)) x

/-- The top-section morphism of a transported section is obtained by
postcomposing with the module-sheaf isomorphism. -/
theorem homOfTopSection_moduleIsoTopSection
    (e : M ≅ N) (x : Γ(M, ⊤)) :
    homOfTopSection M x ≫ e.hom =
      homOfTopSection N (moduleIsoTopSection e x) := by
  apply unit_hom_ext_top
  have hleft :
      (homOfTopSection M x ≫ e.hom).val.app
          (op (⊤ : X.Opens))
          (1 : X.ringCatSheaf.obj.obj (op ⊤)) =
        moduleIsoTopSection e x := by
    change e.hom.val.app (op (⊤ : X.Opens))
      ((homOfTopSection M x).val.app
        (op (⊤ : X.Opens))
        (1 : X.ringCatSheaf.obj.obj (op ⊤))) =
      e.hom.val.app (op (⊤ : X.Opens)) x
    exact congrArg
      (fun y => e.hom.val.app (op (⊤ : X.Opens)) y)
      (homOfTopSection_app_top_one M x)
  have hright :
      (homOfTopSection N
        (moduleIsoTopSection e x)).val.app
          (op (⊤ : X.Opens))
          (1 : X.ringCatSheaf.obj.obj (op ⊤)) =
        moduleIsoTopSection e x :=
    homOfTopSection_app_top_one N
      (moduleIsoTopSection e x)
  exact hleft.trans hright.symm

/-- An epimorphic top-section coproduct remains epimorphic after all
sections are transported through a module-sheaf isomorphism. -/
theorem sigmaDesc_moduleIsoTopSection_epi
    {ι : Type u}
    (e : M ≅ N) (s : ι → Γ(M, ⊤))
    (h :
      Epi
        (Limits.Sigma.desc
          (fun a => homOfTopSection M (s a)))) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          homOfTopSection N
            (moduleIsoTopSection e (s a)))) := by
  let localMap :=
    Limits.Sigma.desc
      (fun a => homOfTopSection M (s a))
  let transportedMap :=
    Limits.Sigma.desc
      (fun a =>
        homOfTopSection N
          (moduleIsoTopSection e (s a)))
  have hmap :
      transportedMap = localMap ≫ e.hom := by
    apply Limits.Sigma.hom_ext
    intro a
    let sourceι :=
      Limits.Sigma.ι
        (fun _ : ι =>
          SheafOfModules.unit X.ringCatSheaf) a
    have htransported :
        sourceι ≫ transportedMap =
          homOfTopSection N
            (moduleIsoTopSection e (s a)) := by
      dsimp only [sourceι, transportedMap]
      exact Limits.Sigma.ι_desc _ _
    have hlocal :
        sourceι ≫ localMap =
          homOfTopSection M (s a) := by
      dsimp only [sourceι, localMap]
      exact Limits.Sigma.ι_desc _ _
    calc
      sourceι ≫ transportedMap =
          homOfTopSection N
            (moduleIsoTopSection e (s a)) :=
        htransported
      _ = homOfTopSection M (s a) ≫ e.hom :=
        (homOfTopSection_moduleIsoTopSection
          e (s a)).symm
      _ = (sourceι ≫ localMap) ≫ e.hom :=
        congrArg (fun q => q ≫ e.hom) hlocal.symm
      _ = sourceι ≫ (localMap ≫ e.hom) :=
        Category.assoc _ _ _
  let hlocal : Epi localMap := by
    dsimp only [localMap]
    exact h
  let htarget : Epi e.hom := inferInstance
  let hcomp : Epi (localMap ≫ e.hom) :=
    @CategoryTheory.epi_comp
      _ _ _ _ _ localMap hlocal e.hom htarget
  change Epi transportedMap
  exact (congrArg Epi hmap).symm.mp hcomp

end AlgebraicGeometry.Scheme.Modules
