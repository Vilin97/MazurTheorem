/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

This is the affine-tilde unit slice of AINTLIB's
`ForMathlib/AffineModuleBaseChange.lean`.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.AdjunctionUnitIsoTransport
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent

/-!
# Affine base change for tilde modules

This file retains the comparison needed to transport an invertible
extension-of-scalars unit to the geometric pullback--pushforward unit on a
tilde sheaf.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def moduleSpecPushforwardΓIso₁
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) := by
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (CategoryTheory.evaluation
      (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
      (op (⊤ : (Spec R).Opens))
  exact (Functor.associator
      (pushforward (Spec.map φ)) modulesSpecToSheaf H).symm ≪≫
    Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ) H

private noncomputable def moduleSpecPushforwardΓIsoApp₂
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : (Spec S).Modules) :
    (((modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens))).obj N) ≅
      (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj N := by
  have htop :
      (Opens.map (Spec.map φ).base).op.obj (op (⊤ : (Spec R).Opens)) =
        op (⊤ : (Spec S).Opens) := by
    simp
  exact (ModuleCat.restrictScalars φ.hom).mapIso
    ((modulesSpecToSheaf.obj N).presheaf.mapIso (eqToIso htop))

private noncomputable def moduleSpecPushforwardΓIso₂
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (moduleSpecPushforwardΓIsoApp₂ φ) (by
    intro M N f
    have htop :
        (Opens.map (Spec.map φ).base).op.obj (op (⊤ : (Spec R).Opens)) =
          op (⊤ : (Spec S).Opens) := by
      simp
    change
      (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.map f).1.app
              ((Opens.map (Spec.map φ).base).op.obj
                (op (⊤ : (Spec R).Opens)))) ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.obj N).presheaf.map (eqToHom htop)) =
        (ModuleCat.restrictScalars φ.hom).map
              ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom htop)) ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.map f).1.app
              (op (⊤ : (Spec S).Opens)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (ModuleCat.restrictScalars φ.hom).map
      ((modulesSpecToSheaf.map f).1.naturality (eqToHom htop)).symm)

private noncomputable def moduleSpecPushforwardΓIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  moduleSpecPushforwardΓIso₁ φ ≪≫ moduleSpecPushforwardΓIso₂ φ

private noncomputable def tildePullbackIsoExtendScalars
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    (moduleSpecPushforwardΓIso φ)).symm

/-- For a tilde sheaf on an affine spectrum, an invertible extension-of-scalars
unit implies that the geometric pullback unit is invertible. -/
theorem isIso_pullbackPushforward_unit_tilde_of_isIso_extendScalars_unit
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R)
    [IsIso ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M)] :
    IsIso ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)) := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  haveI hAdj₂ : IsIso (adj₂.unit.app M) := by
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    infer_instance
  haveI hAdj₁ : IsIso (adj₁.unit.app M) :=
    Adjunction.isIso_unit_app_of_natIso_left
      adj₁ adj₂ (tildePullbackIsoExtendScalars φ).symm M
  haveI hComposite :
      IsIso ((tilde.adjunction (R := R)).unit.app M ≫
        moduleSpecΓFunctor.map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M))) := by
    exact hAdj₁
  haveI hMapped :
      IsIso (moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((tilde.adjunction (R := R)).unit.app M)
      (moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)))
      (inferInstanceAs (IsIso ((tilde.adjunction (R := R)).unit.app M)))
      hComposite
  haveI hPullback :
      ((pullback (Spec.map φ)).obj (tilde M)).IsQuasicoherent := by
    let e := (tildePullbackIsoExtendScalars φ).app M
    have hTilde :
        ((tilde.functor S).obj
          ((ModuleCat.extendScalars φ.hom).obj M)).IsQuasicoherent :=
      inferInstance
    exact (_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
      e.symm hTilde
  haveI hPushforward :
      ((pushforward (Spec.map φ)).obj
        ((pullback (Spec.map φ)).obj (tilde M))).IsQuasicoherent :=
    isQuasicoherent_of_pushforward (Spec.map φ)
      ((pullback (Spec.map φ)).obj (tilde M))
  letI hSource :
      ((𝟭 (Spec R).Modules).obj (tilde M)).IsQuasicoherent := by
    change (tilde M).IsQuasicoherent
    infer_instance
  letI hTarget :
      ((pullback (Spec.map φ) ⋙ pushforward (Spec.map φ)).obj
        (tilde M)).IsQuasicoherent := by
    exact hPushforward
  apply isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)))

end AlgebraicGeometry.Scheme.Modules
