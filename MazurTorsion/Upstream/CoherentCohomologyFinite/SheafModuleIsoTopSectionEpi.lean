/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionCoproduct

/-!
# Epimorphic top-section coproducts across a scheme isomorphism

Restriction along a scheme isomorphism is an equivalence.  Hence an
epimorphic family of top-section maps remains epimorphic after the family
is transported back across that isomorphism.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)

/-- An epimorphic coproduct of top-section maps remains epimorphic after
transport across a scheme isomorphism. -/
theorem sigmaDesc_isoTransportedTopSection_epi
    {ι : Type u}
    (s : ι → Γ(M.restrict e.hom, ⊤))
    (h :
      Epi
        (Limits.Sigma.desc
          (fun a =>
            homOfTopSection
              (M.restrict e.hom) (s a)))) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          homOfTopSection M
            (isoTransportedTopSection e M (s a)))) := by
  let F := restrictFunctor e.inv
  letI : F.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
      (restrictAdjunction e.inv)
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
  let freeIso :=
    @SheafOfModules.mapFreeIso
      _ _ _ _ _ _ _ _ _ _ _ _
      (restrictFunctor e.inv) ι hpres
      (restrictUnitIso e.inv).symm
  let localMap :=
    Limits.Sigma.desc
      (fun a =>
        homOfTopSection
          (M.restrict e.hom) (s a))
  let hlocal : Epi localMap := by
    dsimp only [localMap]
    exact h
  let hFmap : Epi (F.map localMap) :=
    @CategoryTheory.Functor.map_epi
      _ _ _ _ F _ _ _ localMap hlocal
  letI : Epi (F.map localMap) := hFmap
  let hfree : Epi freeIso.hom := inferInstance
  let hpair :
      Epi (freeIso.hom ≫ F.map localMap) :=
    @CategoryTheory.epi_comp
      _ _ _ _ _ freeIso.hom hfree
      (F.map localMap) hFmap
  let htarget : Epi (restrictIsoOfIso e.symm M).hom :=
    inferInstance
  let htotal :
      Epi
        ((freeIso.hom ≫ F.map localMap) ≫
          (restrictIsoOfIso e.symm M).hom) :=
    @CategoryTheory.epi_comp
      _ _ _ _ _
      (freeIso.hom ≫ F.map localMap) hpair
      (restrictIsoOfIso e.symm M).hom htarget
  have htransported :
      Epi
        (isoTransportedTopSectionCoproduct e M s) := by
    unfold isoTransportedTopSectionCoproduct
    change
      Epi
        ((freeIso.hom ≫ F.map localMap) ≫
          (restrictIsoOfIso e.symm M).hom)
    exact htotal
  rw [← isoTransportedTopSectionCoproduct_eq_sigmaDesc]
  exact htransported

end AlgebraicGeometry.Scheme.Modules
