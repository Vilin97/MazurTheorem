/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionCoproduct

/-!
# Epimorphic coproducts of ambient-open section maps

An epimorphic coproduct of top-section maps remains epimorphic after
transport to the slice site of the corresponding ambient open.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- An epimorphic coproduct of top-section maps on the open subscheme
gives an epimorphic coproduct of the corresponding ambient-open maps. -/
theorem sigmaDesc_homOfOpenSection_epi_of_restrict
    {ι : Type u}
    (s : ι → Γ(M.restrict U.ι, ⊤))
    (h :
      Epi
        (restrictedTopSectionCoproduct M U s)) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          homOfOpenSection M U
            ((eqToIso (congrArg (fun V => Γ(M, V))
                U.ι_image_top)).hom
              ((M.restrictAppIso U.ι ⊤).hom (s a))))) := by
  let F := (overEquivalence U).functor
  letI : Limits.PreservesColimitsOfSize.{u, u} F :=
    (overEquivalence U).toAdjunction.leftAdjoint_preservesColimits
  letI : F.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
      (overEquivalence U).toAdjunction
  let localMap := restrictedTopSectionCoproduct M U s
  haveI : Epi localMap := h
  let hFmap : Epi (F.map localMap) :=
    F.map_epi localMap
  letI : Epi (F.map localMap) := hFmap
  let hfree :
      Epi
        (SheafOfModules.mapFreeIso F ι
          (unitOverIso U).symm).hom :=
    inferInstance
  let hpair :
      Epi
        ((SheafOfModules.mapFreeIso F ι
          (unitOverIso U).symm).hom ≫
            F.map localMap) :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (SheafOfModules.mapFreeIso F ι
        (unitOverIso U).symm).hom hfree
      (F.map localMap) hFmap
  letI :
      Epi
        ((SheafOfModules.mapFreeIso F ι
          (unitOverIso U).symm).hom ≫
            F.map localMap) :=
    hpair
  let htarget : Epi (restrictOverIso U M).hom :=
    inferInstance
  let htransported :
      Epi (transportedTopSectionCoproduct M U s) := by
    unfold transportedTopSectionCoproduct
    exact
      @CategoryTheory.epi_comp _ _ _ _ _
        ((SheafOfModules.mapFreeIso F ι
          (unitOverIso U).symm).hom ≫
            F.map localMap) hpair
        (restrictOverIso U M).hom htarget
  rw [← transportedTopSectionCoproduct_eq_sigmaDesc]
  exact htransported

end AlgebraicGeometry.Scheme.Modules
