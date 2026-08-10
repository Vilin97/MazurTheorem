/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project, Vasily Ilin

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

The named top-section generator and its evaluator are project-original
specializations of the retained private global-sections mate.
-/

open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

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

/-- Pullback of a tilde module along a map of affine spectra agrees with extension of scalars. -/
noncomputable def tildePullbackIsoExtendScalars
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    (moduleSpecPushforwardΓIso φ)).symm

/-- The canonical top-level section of the pullback of a tilde module generated by an element
of the original module. -/
noncomputable def tildePullbackGenerator
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat R) (m : M) :
    Γ((pullback (Spec.map φ)).obj (tilde M),
      (⊤ : (Spec S).Opens)) :=
  ((tilde.adjunction (R := R)).unit.app M ≫
      moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction
          (Spec.map φ)).unit.app ((tilde.functor R).obj M)) ≫
      (moduleSpecPushforwardΓIso φ).hom.app
        ((tilde.functor R ⋙ pullback (Spec.map φ)).obj M)) m

/-- The packaged affine pullback generator is the pullback-unit image of the corresponding
top tilde section, transported along the canonical identification of the inverse image of the
top open with the top open. -/
theorem tildePullbackGenerator_eq_pullbackUnit_toOpen_top
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat R) (m : M) :
    let f := Spec.map φ
    let htop :
        (Opens.map f.base).op.obj (op (⊤ : (Spec R).Opens)) =
          op (⊤ : (Spec S).Opens) := by simp
    tildePullbackGenerator φ M m =
      (((pullback f).obj (tilde M)).presheaf.map (eqToHom htop))
        (((pullbackPushforwardAdjunction f).unit.app (tilde M)).val.app
          (op (⊤ : (Spec R).Opens))
          (tilde.toOpen M (⊤ : (Spec R).Opens) m)) := by
  rfl

private theorem tildePullbackIsoExtendScalars_inv_comp_unit
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((tilde.adjunction (R := S)).unit.app
                ((ModuleCat.extendScalars φ.hom).obj M) ≫
            moduleSpecΓFunctor.map
              ((tildePullbackIsoExtendScalars φ).inv.app M)) =
      (tilde.adjunction (R := R)).unit.app M ≫
        moduleSpecΓFunctor.map
          ((pullbackPushforwardAdjunction
            (Spec.map φ)).unit.app ((tilde.functor R).obj M)) ≫
        (moduleSpecPushforwardΓIso φ).hom.app
          ((tilde.functor R ⋙ pullback (Spec.map φ)).obj M) := by
  have h := unit_conjugateEquiv_symm
    ((tilde.adjunction (R := R)).comp
      (pullbackPushforwardAdjunction (Spec.map φ)))
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S)))
    (moduleSpecPushforwardΓIso φ).hom M
  have hβ : (tildePullbackIsoExtendScalars φ).inv =
      (conjugateEquiv
        ((tilde.adjunction (R := R)).comp
          (pullbackPushforwardAdjunction (Spec.map φ)))
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
          (tilde.adjunction (R := S)))).symm
        (moduleSpecPushforwardΓIso φ).hom := by
    rfl
  simpa only [hβ, Adjunction.comp_unit_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.assoc] using h.symm

/-- The affine tilde base-change comparison sends the canonical pullback generator to the top
section generated by the extension-of-scalars unit. -/
theorem tildePullbackIsoExtendScalars_hom_generator
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat R) (m : M) :
    ((tildePullbackIsoExtendScalars φ).hom.app M).val.app
        (op (⊤ : (Spec S).Opens))
        (tildePullbackGenerator φ M m) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M)
        (⊤ : (Spec S).Opens)
        ((1 : S) ⊗ₜ[R, φ.hom] m) := by
  let e := (tildePullbackIsoExtendScalars φ).app M
  have h := ConcreteCategory.congr_hom
    (tildePullbackIsoExtendScalars_inv_comp_unit φ M) m
  let s : moduleSpecΓFunctor.obj
      ((tilde.functor S).obj
        ((ModuleCat.extendScalars φ.hom).obj M)) :=
    tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M)
      (⊤ : (Spec S).Opens)
      ((1 : S) ⊗ₜ[R, φ.hom] m)
  change
    (moduleSpecΓFunctor.map e.inv) s =
      tildePullbackGenerator φ M m at h
  change
    (moduleSpecΓFunctor.map e.hom)
        (tildePullbackGenerator φ M m) =
      s
  have hcomp :
      moduleSpecΓFunctor.map e.inv ≫
          moduleSpecΓFunctor.map e.hom =
        𝟙 _ := by
    calc
      _ = moduleSpecΓFunctor.map (e.inv ≫ e.hom) :=
        (moduleSpecΓFunctor.map_comp e.inv e.hom).symm
      _ = moduleSpecΓFunctor.map (𝟙 _) :=
        congrArg moduleSpecΓFunctor.map e.inv_hom_id
      _ = 𝟙 _ := moduleSpecΓFunctor.map_id _
  have hs := ConcreteCategory.congr_hom hcomp s
  calc
    _ = (moduleSpecΓFunctor.map e.hom)
        ((moduleSpecΓFunctor.map e.inv) s) :=
      congrArg (moduleSpecΓFunctor.map e.hom) h.symm
    _ = s := by
      simpa only [CategoryTheory.comp_apply,
        CategoryTheory.id_apply] using hs

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
