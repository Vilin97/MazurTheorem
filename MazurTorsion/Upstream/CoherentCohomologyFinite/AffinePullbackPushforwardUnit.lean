/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffinePullbackTilde

/-!
# The affine pullback--pushforward unit

The canonical pullback--pushforward unit on a tilde module is an
isomorphism whenever the corresponding extension-of-scalars unit is an
isomorphism.  The proof uses the compatibility of the two units and
affine reconstruction.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/--
A morphism between affine modules reconstructed by `tilde` is an
isomorphism as soon as its map on global sections is an isomorphism.
-/
theorem isIso_of_isIso_moduleSpecΓ_map
    {F G : (Spec R).Modules}
    [IsIso F.fromTildeΓ] [IsIso G.fromTildeΓ]
    (α : F ⟶ G)
    [IsIso (moduleSpecΓFunctor.map α)] :
    IsIso α := by
  rw [← isIso_iff_of_reflects_iso α modulesSpecToSheaf]
  apply isLocalizing_of_isIso_app_top
  · change IsIso (moduleSpecΓFunctor.map α)
    infer_instance
  · exact
      (isIso_fromTildeΓ_iff_isLocalizing F).mp
        (inferInstanceAs (IsIso F.fromTildeΓ))
  · exact
      (isIso_fromTildeΓ_iff_isLocalizing G).mp
        (inferInstanceAs (IsIso G.fromTildeΓ))

/--
For a tilde module, an invertible algebraic extension-of-scalars unit
implies that the scheme-theoretic pullback--pushforward unit is
invertible.
-/
theorem isIso_pullbackPushforward_unit_tilde_of_isIso_extendScalars_unit
    (M : ModuleCat R)
    [IsIso ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M)] :
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map φ)).unit.app (tilde M)) := by
  let adjA := tildePullbackAdjunction φ
  let adjB :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S))
  let e := pullbackTildeIso φ
  haveI hTildeUnit :
      IsIso
        ((tilde.adjunction (R := S)).unit.app
          ((ModuleCat.extendScalars φ.hom).obj M)) :=
    inferInstance
  haveI hRestrictedTildeUnit :
      IsIso
        ((ModuleCat.restrictScalars φ.hom).map
          ((tilde.adjunction (R := S)).unit.app
            ((ModuleCat.extendScalars φ.hom).obj M))) :=
    inferInstance
  haveI hAdjBUnit : IsIso (adjB.unit.app M) := by
    dsimp only [adjB]
    rw [Adjunction.comp_unit_app]
    exact
      IsIso.comp_isIso'
        (inferInstanceAs
          (IsIso
            ((ModuleCat.extendRestrictScalarsAdj
              φ.hom).unit.app M)))
        hRestrictedTildeUnit
  haveI hComparisonMap :
      IsIso
        ((moduleSpecΓFunctor (R := S) ⋙
          ModuleCat.restrictScalars φ.hom).map
            (e.hom.app M)) :=
    inferInstance
  have hUnitCompatibility := pullbackTildeIso_unit φ M
  haveI hAdjAUnitComp :
      IsIso
        (adjA.unit.app M ≫
          (moduleSpecΓFunctor (R := S) ⋙
            ModuleCat.restrictScalars φ.hom).map
              (e.hom.app M)) := by
    exact hUnitCompatibility.symm ▸ hAdjBUnit
  haveI hAdjAUnit : IsIso (adjA.unit.app M) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _
      (adjA.unit.app M)
      ((moduleSpecΓFunctor (R := S) ⋙
          ModuleCat.restrictScalars φ.hom).map
        (e.hom.app M))
      hComparisonMap hAdjAUnitComp
  haveI hGlobalSectionsUnit :
      IsIso
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map φ)).unit.app (tilde M))) := by
    haveI hABC :
        IsIso
          ((tilde.adjunction (R := R)).unit.app M ≫
            moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                (Spec.map φ)).unit.app (tilde M)) ≫
            (pushforwardModuleSpecΓIso φ).hom.app
              ((Scheme.Modules.pullback
                (Spec.map φ)).obj (tilde M))) :=
      (tildePullbackAdjunction_unit_app φ M) ▸ hAdjAUnit
    haveI hBC :
        IsIso
          (moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                (Spec.map φ)).unit.app (tilde M)) ≫
            (pushforwardModuleSpecΓIso φ).hom.app
              ((Scheme.Modules.pullback
                (Spec.map φ)).obj (tilde M))) :=
      @IsIso.of_isIso_comp_left _ _ _ _ _
        ((tilde.adjunction (R := R)).unit.app M)
        (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (Spec.map φ)).unit.app (tilde M)) ≫
          (pushforwardModuleSpecΓIso φ).hom.app
            ((Scheme.Modules.pullback
              (Spec.map φ)).obj (tilde M)))
        (inferInstanceAs
          (IsIso ((tilde.adjunction (R := R)).unit.app M)))
        hABC
    exact
      @IsIso.of_isIso_comp_right _ _ _ _ _
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map φ)).unit.app (tilde M)))
        ((pushforwardModuleSpecΓIso φ).hom.app
          ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)))
        (inferInstanceAs
          (IsIso
            ((pushforwardModuleSpecΓIso φ).hom.app
              ((Scheme.Modules.pullback
                (Spec.map φ)).obj (tilde M)))))
        hBC
  let eTarget :
      tilde
          ((ModuleCat.restrictScalars φ.hom).obj
            ((ModuleCat.extendScalars φ.hom).obj M)) ≅
        (Scheme.Modules.pushforward (Spec.map φ)).obj
          ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)) :=
    tildeRestrictScalarsIsoPushforward φ
        ((ModuleCat.extendScalars φ.hom).obj M) ≪≫
      (Scheme.Modules.pushforward (Spec.map φ)).mapIso
        ((pullbackTildeIso φ).app M).symm
  letI hTargetReconstruction :
      IsIso
        ((Scheme.Modules.pushforward (Spec.map φ)).obj
          ((Scheme.Modules.pullback (Spec.map φ)).obj
            (tilde M))).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr
      ⟨(ModuleCat.restrictScalars φ.hom).obj
          ((ModuleCat.extendScalars φ.hom).obj M),
        ⟨eTarget⟩⟩
  letI hSourceReconstruction : IsIso (tilde M).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr
      ⟨M, ⟨Iso.refl _⟩⟩
  exact
    @isIso_of_isIso_moduleSpecΓ_map _
      (tilde M)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)))
      hSourceReconstruction
      hTargetReconstruction
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map φ)).unit.app (tilde M))
      hGlobalSectionsUnit

end AlgebraicGeometry
