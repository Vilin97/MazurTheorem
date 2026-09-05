/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.SchemeModulePullbackCoherent
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import Mathlib.RingTheory.IsTensorProduct

/-!
# Sections under affine pullback

This file identifies the canonical pullback-unit map on global sections of a
quasicoherent module over an affine Cartesian square as extension of scalars.
The proof passes through the affine-spectrum tilde comparison, verifies that
the resulting tensor map is the geometric adjunction unit, and then cancels
the coordinate-ring pushout attached to the Cartesian square.

This is deliberately an affine-local interface: it does not assert proper or
family-level cohomology base change.  Its named downstream consumer is
`SchemeModuleBaseChangeCech`, which assembles these section maps over affine
intersections into a comparison of base-linear Cech complexes.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

noncomputable def specPullbackSectionsTargetIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) ≅
      (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) := by
  let P := moduleSpecΓFunctor.obj M
  let Q := (ModuleCat.extendScalars φ.hom).obj P
  let eM : (tilde.functor R).obj P ≅ M := by
    exact @asIso _ _ _ _ M.fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent M)
  let ePull :
      (pullback (Spec.map φ)).obj ((tilde.functor R).obj P) ≅
        (pullback (Spec.map φ)).obj M :=
    (pullback (Spec.map φ)).mapIso eM
  let eBase :
      (pullback (Spec.map φ)).obj ((tilde.functor R).obj P) ≅
        (tilde.functor S).obj Q :=
    (tildePullbackIsoExtendScalars φ).app P
  exact moduleSpecΓFunctor.mapIso (ePull.symm ≪≫ eBase) ≪≫
    (tilde.toTildeΓNatIso.app Q).symm

noncomputable def specPullbackSectionsLinearMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    letI : Algebra R S := φ.hom.toAlgebra
    let Q := moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M)
    letI : Module R Q := Module.compHom Q φ.hom
    letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    moduleSpecΓFunctor.obj M →ₗ[R] Q := by
  letI : Algebra R S := φ.hom.toAlgebra
  let P := moduleSpecΓFunctor.obj M
  let Q := moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M)
  letI : Module R Q := Module.compHom Q φ.hom
  letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e := specPullbackSectionsTargetIso φ M
  exact ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app P ≫
    (ModuleCat.restrictScalars φ.hom).map e.inv).hom

theorem specPullbackSectionsLinearMap_isBaseChange
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    letI : Algebra R S := φ.hom.toAlgebra
    let Q := moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M)
    letI : Module R Q := Module.compHom Q φ.hom
    letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange S (specPullbackSectionsLinearMap φ M) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let P := moduleSpecΓFunctor.obj M
  let Q := moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M)
  letI : Module R Q := Module.compHom Q φ.hom
  letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply IsBaseChange.of_equiv
    (specPullbackSectionsTargetIso φ M).symm.toLinearEquiv
  intro m
  change (specPullbackSectionsTargetIso φ M).inv
      ((1 : S) ⊗ₜ[R, φ.hom] m) = _
  rfl

noncomputable def pullbackUnitTop
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : Γ((pullback f).obj M, ⊤) :=
  let htop :
      (Opens.map f.base).op.obj (.op (⊤ : X.Opens)) =
        .op (⊤ : Y.Opens) := by
    simp
  (((pullback f).obj M).presheaf.map (eqToHom htop))
    (((pullbackPushforwardAdjunction f).unit.app M).val.app
      (.op (⊤ : X.Opens)) x)

theorem pullbackUnitTop_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    (q : M ⟶ N) (x : Γ(M, (⊤ : X.Opens))) :
    ((pullback f).map q).val.app (.op (⊤ : Y.Opens))
        (pullbackUnitTop f M x) =
      pullbackUnitTop f N (q.val.app (.op (⊤ : X.Opens)) x) := by
  let PB := pullback f
  let adj := pullbackPushforwardAdjunction f
  let htop :
      (Opens.map f.base).op.obj (.op (⊤ : X.Opens)) =
        .op (⊤ : Y.Opens) := by
    simp
  let raw := (adj.unit.app M).val.app (.op (⊤ : X.Opens)) x
  have hrestrict :=
    PresheafOfModules.naturality_apply (PB.map q).val (eqToHom htop) raw
  change (PB.map q).val.app (.op (⊤ : Y.Opens))
      ((PB.obj M).presheaf.map (eqToHom htop) raw) =
    (PB.obj N).presheaf.map (eqToHom htop)
      ((PB.map q).val.app
        ((Opens.map f.base).op.obj (.op (⊤ : X.Opens))) raw) at hrestrict
  have hunit := congrArg
    (fun k ↦ k.val.app (.op (⊤ : X.Opens)) x) (adj.unit.naturality q)
  conv_lhs at hunit =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at hunit =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change (adj.unit.app N).val.app (.op (⊤ : X.Opens))
      (q.val.app (.op (⊤ : X.Opens)) x) =
    (PB.map q).val.app
      ((Opens.map f.base).op.obj (.op (⊤ : X.Opens))) raw at hunit
  change (PB.map q).val.app (.op (⊤ : Y.Opens))
      ((PB.obj M).presheaf.map (eqToHom htop) raw) =
    (PB.obj N).presheaf.map (eqToHom htop)
      ((adj.unit.app N).val.app (.op (⊤ : X.Opens))
        (q.val.app (.op (⊤ : X.Opens)) x))
  exact hrestrict.trans
    (congrArg ((PB.obj N).presheaf.map (eqToHom htop)) hunit.symm)

private theorem iso_inv_val_app_of_hom_val_app
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U))
    (h : e.hom.val.app (.op U) x = y) :
    e.inv.val.app (.op U) y = x := by
  have hid := congrArg (fun q ↦ q.val.app (.op U) x) e.hom_inv_id
  conv_lhs at hid =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change e.inv.val.app (.op U) (e.hom.val.app (.op U) x) = x at hid
  exact (congrArg (e.inv.val.app (.op U)) h.symm).trans hid

theorem specPullbackSectionsLinearMap_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj M) :
    specPullbackSectionsLinearMap φ M x =
      pullbackUnitTop (Spec.map φ) M x := by
  let P := moduleSpecΓFunctor.obj M
  let Q := (ModuleCat.extendScalars φ.hom).obj P
  let eM : (tilde.functor R).obj P ≅ M := by
    exact @asIso _ _ _ _ M.fromTildeΓ
      (isIso_fromTildeΓ_of_isQuasicoherent M)
  let PB := pullback (Spec.map φ)
  let ePull : PB.obj ((tilde.functor R).obj P) ≅ PB.obj M :=
    PB.mapIso eM
  let eBase : PB.obj ((tilde.functor R).obj P) ≅
      (tilde.functor S).obj Q :=
    (tildePullbackIsoExtendScalars φ).app P
  let y := tilde.toOpen Q (⊤ : (Spec S).Opens)
    ((1 : S) ⊗ₜ[R, φ.hom] x)
  let g := tildePullbackGenerator φ P x
  have hbase := tildePullbackIsoExtendScalars_hom_generator φ P x
  change eBase.hom.val.app (.op ⊤) g = y at hbase
  have hbaseInv : eBase.inv.val.app (.op ⊤) y = g :=
    iso_inv_val_app_of_hom_val_app eBase ⊤ g y hbase
  have hgenerator :=
    tildePullbackGenerator_eq_pullbackUnit_toOpen_top φ P x
  change g = pullbackUnitTop (Spec.map φ) ((tilde.functor R).obj P)
    (tilde.toOpen P ⊤ x) at hgenerator
  have hnat := pullbackUnitTop_naturality (Spec.map φ) eM.hom
    (tilde.toOpen P ⊤ x)
  change ePull.hom.val.app (.op ⊤)
      (pullbackUnitTop (Spec.map φ) ((tilde.functor R).obj P)
        (tilde.toOpen P ⊤ x)) =
    pullbackUnitTop (Spec.map φ) M
      (eM.hom.val.app (.op ⊤) (tilde.toOpen P ⊤ x)) at hnat
  have hcounit := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := R)).right_triangle_components M) x
  conv_lhs at hcounit =>
    erw [ModuleCat.comp_apply]
  have hcounit' :
      eM.hom.val.app (.op ⊤) (tilde.toOpen P ⊤ x) = x := by
    exact hcounit
  change ePull.hom.val.app (.op ⊤)
      (eBase.inv.val.app (.op ⊤) y) =
    pullbackUnitTop (Spec.map φ) M x
  exact (congrArg (ePull.hom.val.app (.op ⊤))
      (hbaseInv.trans hgenerator)).trans
      (hnat.trans (congrArg (pullbackUnitTop (Spec.map φ) M) hcounit'))

noncomputable def pullbackUnitTopLinearMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    Γ(M, (⊤ : X.Opens)) →ₗ[Γ(X, ⊤)]
      baseSections f ((pullback f).obj M) :=
  ((baseModulePresheafIdTopIso M).hom ≫
    ((baseModulePresheafFunctor (𝟙 X)).map
      ((pullbackPushforwardAdjunction f).unit.app M)).app (.op ⊤) ≫
    (baseSectionsPushforwardTopIso f ((pullback f).obj M)).inv).hom

@[simp]
theorem pullbackUnitTopLinearMap_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    pullbackUnitTopLinearMap f M x = pullbackUnitTop f M x := by
  apply (ConcreteCategory.bijective_of_isIso
    (baseSectionsPushforwardTopIso f ((pullback f).obj M)).hom).1
  simp only [pullbackUnitTopLinearMap,
    baseSectionsPushforwardTopIso_hom_apply]
  rfl

theorem pullbackUnitTopLinearMap_bijective_of_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (M : X.Modules) :
    Function.Bijective (pullbackUnitTopLinearMap f M) := by
  let q := (pullbackPushforwardAdjunction f).unit.app M
  haveI : IsIso q := inferInstance
  let η := (baseModulePresheafFunctor (𝟙 X)).map q
  haveI : IsIso η := Functor.map_isIso (baseModulePresheafFunctor (𝟙 X)) q
  haveI : IsIso (η.app (.op (⊤ : X.Opens))) :=
    NatIso.isIso_app_of_isIso η _
  let a := (baseModulePresheafIdTopIso M).hom
  let b := η.app (.op (⊤ : X.Opens))
  let c := (baseSectionsPushforwardTopIso f ((pullback f).obj M)).inv
  have ha : Function.Bijective a := ConcreteCategory.bijective_of_isIso a
  have hb : Function.Bijective b := ConcreteCategory.bijective_of_isIso b
  have hc : Function.Bijective c := ConcreteCategory.bijective_of_isIso c
  change Function.Bijective (fun x ↦ c.hom (b.hom (a.hom x)))
  exact hc.comp (hb.comp ha)

noncomputable def pullbackUnitTopLinearEquivOfIsIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (M : X.Modules) :
    Γ(M, (⊤ : X.Opens)) ≃ₗ[Γ(X, ⊤)]
      baseSections f ((pullback f).obj M) := by
  exact LinearEquiv.ofBijective (pullbackUnitTopLinearMap f M)
    (pullbackUnitTopLinearMap_bijective_of_isIso f M)

theorem isoSpec_hom_appTop_eq_ΓSpecIso_hom
    (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom := by
  simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]

theorem isoSpec_inv_appTop_eq_ΓSpecIso_inv
    (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop =
      (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv := by
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom]
  rw [← isoSpec_hom_appTop_eq_ΓSpecIso_hom X]
  rw [← Scheme.Hom.comp_appTop]
  rw [X.isoSpec.hom_inv_id]
  rw [isoSpec_hom_appTop_eq_ΓSpecIso_hom X]
  simp

noncomputable def isoSpecInvBaseSectionsIsoModuleSpec
    (X : Scheme.{u}) [IsAffine X]
    (N : (Spec Γ(X, (⊤ : X.Opens))).Modules) :
    baseSections X.isoSpec.inv N ≅ moduleSpecΓFunctor.obj N := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext (x : Γ(N, (⊤ : (Spec Γ(X, ⊤)).Opens)))
  change
    (Spec Γ(X, ⊤)).presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (.op ⊤))
        ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) • x =
      (Spec Γ(X, ⊤)).presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (.op ⊤))
        (X.isoSpec.inv.appTop r) • x
  rw [isoSpec_inv_appTop_eq_ΓSpecIso_inv X]

noncomputable def isoSpecInvPullbackUnitTopLinearEquiv
    (X : Scheme.{u}) [IsAffine X] (M : X.Modules) :
    Γ(M, (⊤ : X.Opens)) ≃ₗ[Γ(X, ⊤)]
      moduleSpecΓFunctor.obj ((pullback X.isoSpec.inv).obj M) :=
  (pullbackUnitTopLinearEquivOfIsIso X.isoSpec.inv M).trans
    (isoSpecInvBaseSectionsIsoModuleSpec X
      ((pullback X.isoSpec.inv).obj M)).toLinearEquiv

@[simp]
theorem isoSpecInvPullbackUnitTopLinearEquiv_apply
    (X : Scheme.{u}) [IsAffine X] (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    isoSpecInvPullbackUnitTopLinearEquiv X M x =
      pullbackUnitTop X.isoSpec.inv M x := by
  rw [isoSpecInvPullbackUnitTopLinearEquiv]
  rfl

noncomputable def isoSpecHomPullbackUnitTopLinearMap
    (Y : Scheme.{u}) [IsAffine Y]
    (N : (Spec Γ(Y, (⊤ : Y.Opens))).Modules) :
    moduleSpecΓFunctor.obj N →ₗ[Γ(Y, ⊤)]
      Γ((pullback Y.isoSpec.hom).obj N, (⊤ : Y.Opens)) := by
  let e := pullbackUnitTopLinearEquivOfIsIso Y.isoSpec.hom N
  refine
    { toFun := e
      map_add' := e.map_add
      map_smul' := ?_ }
  intro r x
  let x' : Γ(N, (⊤ : (Spec Γ(Y, ⊤)).Opens)) := x
  let smulY : Γ(Y, ⊤) →
      Γ((pullback Y.isoSpec.hom).obj N, (⊤ : Y.Opens)) →
        Γ((pullback Y.isoSpec.hom).obj N, (⊤ : Y.Opens)) :=
    fun s z ↦ s • z
  have h := e.map_smul
    ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) x'
  have hsource :
      ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) • x' =
        (r • x : moduleSpecΓFunctor.obj N) := by
    rfl
  have htarget :
      ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) •
          (e x' : baseSections Y.isoSpec.hom
            ((pullback Y.isoSpec.hom).obj N)) =
        smulY (Y.isoSpec.hom.appTop
          ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)) (e x) := by
    change
      smulY (Y.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (.op (⊤ : Y.Opens)))
          (Y.isoSpec.hom.appTop
            ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r))) (e x) =
      smulY (Y.isoSpec.hom.appTop
          ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)) (e x)
    rw [show (initialOpOfTerminal isTerminalTop).to (.op (⊤ : Y.Opens)) =
      𝟙 _ from Subsingleton.elim _ _]
    simp
  have hfinal :
      smulY (Y.isoSpec.hom.appTop
          ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)) (e x) =
        smulY r (e x) := by
    rw [isoSpec_hom_appTop_eq_ΓSpecIso_hom Y]
    simp [smulY]
  simpa [smulY] using (congrArg e hsource.symm).trans
    (h.trans (htarget.trans hfinal))

@[simp]
theorem isoSpecHomPullbackUnitTopLinearMap_apply
    (Y : Scheme.{u}) [IsAffine Y]
    (N : (Spec Γ(Y, (⊤ : Y.Opens))).Modules)
    (x : moduleSpecΓFunctor.obj N) :
    isoSpecHomPullbackUnitTopLinearMap Y N x =
      pullbackUnitTop Y.isoSpec.hom N x := by
  rw [isoSpecHomPullbackUnitTopLinearMap]
  change (pullbackUnitTopLinearMap Y.isoSpec.hom N) x = _
  exact pullbackUnitTopLinearMap_apply Y.isoSpec.hom N x

noncomputable def isoSpecHomPullbackUnitTopLinearEquiv
    (Y : Scheme.{u}) [IsAffine Y]
    (N : (Spec Γ(Y, (⊤ : Y.Opens))).Modules) :
    moduleSpecΓFunctor.obj N ≃ₗ[Γ(Y, ⊤)]
      Γ((pullback Y.isoSpec.hom).obj N, (⊤ : Y.Opens)) :=
  LinearEquiv.ofBijective (isoSpecHomPullbackUnitTopLinearMap Y N) (by
    rw [show (⇑(isoSpecHomPullbackUnitTopLinearMap Y N)) =
        ⇑(pullbackUnitTopLinearMap Y.isoSpec.hom N) by
      funext x
      exact (isoSpecHomPullbackUnitTopLinearMap_apply Y N x).trans
        (pullbackUnitTopLinearMap_apply Y.isoSpec.hom N x).symm]
    exact pullbackUnitTopLinearMap_bijective_of_isIso Y.isoSpec.hom N)

@[simp]
theorem pullbackUnitTop_eq_unit_app_top
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    pullbackUnitTop f M x =
      ((pullbackPushforwardAdjunction f).unit.app M).val.app
        (.op (⊤ : X.Opens)) x := by
  let htop :
      (Opens.map f.base).op.obj (.op (⊤ : X.Opens)) =
        .op (⊤ : Y.Opens) := by
    simp
  let z := ((pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op (⊤ : X.Opens)) x
  change (((pullback f).obj M).presheaf.map (eqToHom htop)).hom z = z
  have hh : eqToHom htop = 𝟙 _ := Subsingleton.elim _ _
  rw [hh]
  exact ConcreteCategory.congr_hom
    (((pullback f).obj M).presheaf.map_id _) z

theorem pullbackUnitTop_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) :
    ((pullbackComp g f).hom.app M).val.app (.op (⊤ : Z.Opens))
        (pullbackUnitTop g ((pullback f).obj M)
          (pullbackUnitTop f M x)) =
      pullbackUnitTop (g ≫ f) M x := by
  let adj₁ := (pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction g)
  let adj₂ := pullbackPushforwardAdjunction (g ≫ f)
  have hunit := unit_conjugateEquiv adj₁ adj₂
    (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at hunit
  have hx := congrArg
    (fun q ↦ q.val.app (.op (⊤ : X.Opens)) x) hunit
  dsimp only [adj₁, adj₂] at hx
  rw [Adjunction.comp_unit_app] at hx
  conv_lhs at hx =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at hx =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change
    ((pullbackPushforwardAdjunction g).unit.app
        ((pullback f).obj M)).val.app
      (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (((pullbackPushforwardAdjunction f).unit.app M).val.app
        (.op (⊤ : X.Opens)) x) =
    ((pullbackComp g f).inv.app M).val.app
      (.op ((g ≫ f) ⁻¹ᵁ (⊤ : X.Opens)))
      (((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).val.app
        (.op (⊤ : X.Opens)) x) at hx
  let W : Z.Opens := (g ≫ f) ⁻¹ᵁ (⊤ : X.Opens)
  let e := (pullbackComp g f).app M
  have hx' := congrArg (fun z ↦ e.hom.val.app (.op W) z) hx
  let y := ((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).val.app
    (.op (⊤ : X.Opens)) x
  have he := congrArg (fun q ↦ q.val.app (.op W) y) e.inv_hom_id
  conv_lhs at he =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  change e.hom.val.app (.op W) (e.inv.val.app (.op W) y) = y at he
  have hxy := hx'.trans he
  let xf := ((pullbackPushforwardAdjunction f).unit.app M).val.app
    (.op (⊤ : X.Opens)) x
  let ug := ((pullbackPushforwardAdjunction g).unit.app
    ((pullback f).obj M)).val.app (.op (⊤ : Y.Opens))
  let xg := ug xf
  have hf : pullbackUnitTop f M x = xf :=
    pullbackUnitTop_eq_unit_app_top f M x
  have hg : pullbackUnitTop g ((pullback f).obj M)
      (pullbackUnitTop f M x) = ug (pullbackUnitTop f M x) :=
    pullbackUnitTop_eq_unit_app_top g ((pullback f).obj M) _
  have hinput : ug (pullbackUnitTop f M x) = xg :=
    congrArg ug hf
  have hW : W = (⊤ : Z.Opens) := by
    simp [W]
  subst W
  have hxyTop : e.hom.val.app (.op (⊤ : Z.Opens)) xg = y := by
    change e.hom.val.app (.op (⊤ : Z.Opens)) xg = y at hxy
    exact hxy
  have hd : pullbackUnitTop (g ≫ f) M x = y :=
    pullbackUnitTop_eq_unit_app_top (g ≫ f) M x
  exact (congrArg (e.hom.val.app (.op (⊤ : Z.Opens)))
    (hg.trans hinput)).trans (hxyTop.trans hd.symm)

theorem pullbackUnitTop_congr
    {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) :
    ((pullbackCongr h).hom.app M).val.app (.op (⊤ : Y.Opens))
        (pullbackUnitTop f M x) =
      pullbackUnitTop g M x := by
  subst g
  rfl

noncomputable def topSectionsLinearEquivOfIso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Γ(M, (⊤ : X.Opens)) ≃ₗ[Γ(X, ⊤)] Γ(N, (⊤ : X.Opens)) where
  toFun := e.hom.val.app (.op ⊤)
  invFun := e.inv.val.app (.op ⊤)
  left_inv x := by
    have h := congrArg (fun q ↦ q.val.app (.op (⊤ : X.Opens)) x)
      e.hom_inv_id
    conv_lhs at h =>
      erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
    change e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) x) = x at h
    exact h
  right_inv x := by
    have h := congrArg (fun q ↦ q.val.app (.op (⊤ : X.Opens)) x)
      e.inv_hom_id
    conv_lhs at h =>
      erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
    change e.hom.val.app (.op ⊤) (e.inv.val.app (.op ⊤) x) = x at h
    exact h
  map_add' := map_add _
  map_smul' := fun r x ↦
    (e.hom.val.app (.op (⊤ : X.Opens))).hom.map_smul r x

@[simp]
theorem topSectionsLinearEquivOfIso_apply
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (x : Γ(M, (⊤ : X.Opens))) :
    topSectionsLinearEquivOfIso e x = e.hom.val.app (.op ⊤) x :=
  rfl

@[reducible] noncomputable def baseSectionsSourceModule
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules) :
    Module Γ(Y, ⊤) (baseSections f N) := by
  change Module Γ(Y, ⊤) Γ(N, (⊤ : Y.Opens))
  infer_instance

theorem baseSections_isScalarTower
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
    letI : Module Γ(Y, ⊤) (baseSections f N) :=
      baseSectionsSourceModule f N
    IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) (baseSections f N) := by
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  letI : Module Γ(Y, ⊤) (baseSections f N) :=
    baseSectionsSourceModule f N
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change f.appTop r • (x : Γ(N, (⊤ : Y.Opens))) =
    Y.presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (.op (⊤ : Y.Opens)))
        (f.appTop r) • (x : Γ(N, (⊤ : Y.Opens)))
  rw [show (initialOpOfTerminal isTerminalTop).to (.op (⊤ : Y.Opens)) =
    𝟙 _ from Subsingleton.elim _ _]
  simp

theorem affinePullback_decomposition
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) :
    Y.isoSpec.hom ≫ (Spec.map f.appTop ≫ X.isoSpec.inv) = f := by
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp

noncomputable def affinePullbackDecompositionIso
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (M : X.Modules) :
    (pullback Y.isoSpec.hom).obj
        ((pullback (Spec.map f.appTop)).obj
          ((pullback X.isoSpec.inv).obj M)) ≅
      (pullback f).obj M :=
  (pullback Y.isoSpec.hom).mapIso
      ((pullbackComp (Spec.map f.appTop) X.isoSpec.inv).app M) ≪≫
    (pullbackComp Y.isoSpec.hom
      (Spec.map f.appTop ≫ X.isoSpec.inv)).app M ≪≫
    (pullbackCongr (affinePullback_decomposition f)).app M

theorem affinePullbackDecompositionIso_hom_pullbackUnitTop
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) :
    ((affinePullbackDecompositionIso f M).hom.val.app
        (.op (⊤ : Y.Opens)))
        (pullbackUnitTop Y.isoSpec.hom
          ((pullback (Spec.map f.appTop)).obj
            ((pullback X.isoSpec.inv).obj M))
          (pullbackUnitTop (Spec.map f.appTop)
            ((pullback X.isoSpec.inv).obj M)
            (pullbackUnitTop X.isoSpec.inv M x))) =
      pullbackUnitTop f M x := by
  let b := X.isoSpec.inv
  let g := Spec.map f.appTop
  let a := Y.isoSpec.hom
  let Mb := (pullback b).obj M
  let Mg := (pullback g).obj Mb
  let xb := pullbackUnitTop b M x
  let xg := pullbackUnitTop g Mb xb
  let xa := pullbackUnitTop a Mg xg
  let q := (pullbackComp g b).hom.app M
  have hgb :
      q.val.app (.op (⊤ : (Spec Γ(Y, ⊤)).Opens)) xg =
        pullbackUnitTop (g ≫ b) M x := by
    exact pullbackUnitTop_comp b g M x
  have hnat :
      ((pullback a).map q).val.app (.op (⊤ : Y.Opens)) xa =
        pullbackUnitTop a ((pullback (g ≫ b)).obj M)
          (pullbackUnitTop (g ≫ b) M x) := by
    refine (pullbackUnitTop_naturality a q xg).trans ?_
    exact congrArg (pullbackUnitTop a ((pullback (g ≫ b)).obj M)) hgb
  have hcomp :
      ((pullbackComp a (g ≫ b)).hom.app M).val.app
          (.op (⊤ : Y.Opens))
          (((pullback a).map q).val.app (.op (⊤ : Y.Opens)) xa) =
        pullbackUnitTop (a ≫ (g ≫ b)) M x := by
    refine (congrArg
      (((pullbackComp a (g ≫ b)).hom.app M).val.app
        (.op (⊤ : Y.Opens))) hnat).trans ?_
    exact pullbackUnitTop_comp (g ≫ b) a M x
  have hcongr := pullbackUnitTop_congr
    (affinePullback_decomposition f) M x
  change
    ((pullbackCongr (affinePullback_decomposition f)).hom.app M).val.app
        (.op (⊤ : Y.Opens))
        (((pullbackComp a (g ≫ b)).hom.app M).val.app
          (.op (⊤ : Y.Opens))
          (((pullback a).map q).val.app (.op (⊤ : Y.Opens)) xa)) =
      pullbackUnitTop f M x
  exact (congrArg
    (((pullbackCongr (affinePullback_decomposition f)).hom.app M).val.app
      (.op (⊤ : Y.Opens))) hcomp).trans hcongr

@[reducible] noncomputable def topSectionsBaseModule
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules) :
    Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
  Module.compHom Γ(N, (⊤ : Y.Opens)) f.appTop.hom

noncomputable def topSectionsBaseLinearEquiv
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules) :
    letI : Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
      topSectionsBaseModule f N
    Γ(N, (⊤ : Y.Opens)) ≃ₗ[Γ(X, ⊤)] baseSections f N := by
  letI : Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
    topSectionsBaseModule f N
  refine
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := ?_ }
  intro r x
  change f.appTop r • x =
    Y.presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (.op (⊤ : Y.Opens)))
        (f.appTop r) • x
  rw [show (initialOpOfTerminal isTerminalTop).to (.op (⊤ : Y.Opens)) =
    𝟙 _ from Subsingleton.elim _ _]
  simp

@[simp]
theorem topSectionsBaseLinearEquiv_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules)
    (x : Γ(N, (⊤ : Y.Opens))) :
    letI : Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
      topSectionsBaseModule f N
    topSectionsBaseLinearEquiv f N x = x := by
  letI : Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
    topSectionsBaseModule f N
  rfl

@[simp]
theorem topSectionsBaseLinearEquiv_symm_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules)
    (x : baseSections f N) :
    letI : Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
      topSectionsBaseModule f N
    (topSectionsBaseLinearEquiv f N).symm x = x := by
  letI : Module Γ(X, ⊤) Γ(N, (⊤ : Y.Opens)) :=
    topSectionsBaseModule f N
  rfl

noncomputable def topSectionsSourceLinearEquiv
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules) :
    letI : Module Γ(Y, ⊤) (baseSections f N) :=
      baseSectionsSourceModule f N
    Γ(N, (⊤ : Y.Opens)) ≃ₗ[Γ(Y, ⊤)] baseSections f N := by
  letI : Module Γ(Y, ⊤) (baseSections f N) :=
    baseSectionsSourceModule f N
  exact
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem topSectionsSourceLinearEquiv_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules)
    (x : Γ(N, (⊤ : Y.Opens))) :
    letI : Module Γ(Y, ⊤) (baseSections f N) :=
      baseSectionsSourceModule f N
    topSectionsSourceLinearEquiv f N x = x := by
  letI : Module Γ(Y, ⊤) (baseSections f N) :=
    baseSectionsSourceModule f N
  rfl

@[simp]
theorem topSectionsSourceLinearEquiv_symm_apply
    {X Y : Scheme.{u}} (f : Y ⟶ X) (N : Y.Modules)
    (x : baseSections f N) :
    letI : Module Γ(Y, ⊤) (baseSections f N) :=
      baseSectionsSourceModule f N
    (topSectionsSourceLinearEquiv f N).symm x = x := by
  letI : Module Γ(Y, ⊤) (baseSections f N) :=
    baseSectionsSourceModule f N
  rfl

@[reducible] noncomputable def baseSectionsFurtherBaseModule
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) : Module Γ(Z, ⊤) (baseSections snd N) :=
  Module.compHom (baseSections snd N) g.appTop.hom

noncomputable def pullbackUnitTopBaseLinearMapRaw
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules) :
    letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
      topSectionsBaseModule f M
    letI : Module Γ(Y, ⊤)
        Γ((pullback fst).obj M, (⊤ : P.Opens)) :=
      topSectionsBaseModule snd ((pullback fst).obj M)
    letI : Module Γ(Z, ⊤)
        Γ((pullback fst).obj M, (⊤ : P.Opens)) :=
      Module.compHom Γ((pullback fst).obj M, (⊤ : P.Opens)) g.appTop.hom
    Γ(M, (⊤ : X.Opens)) →ₗ[Γ(Z, ⊤)]
      Γ((pullback fst).obj M, (⊤ : P.Opens)) := by
  let N := (pullback fst).obj M
  letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
    topSectionsBaseModule f M
  letI : Module Γ(X, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule fst N
  letI : Module Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule snd N
  letI : Module Γ(Z, ⊤) Γ(N, (⊤ : P.Opens)) :=
    Module.compHom Γ(N, (⊤ : P.Opens)) g.appTop.hom
  let eFst := topSectionsBaseLinearEquiv fst N
  let uA : Γ(M, (⊤ : X.Opens)) →ₗ[Γ(X, ⊤)]
      Γ(N, (⊤ : P.Opens)) :=
    eFst.symm.toLinearMap.comp (pullbackUnitTopLinearMap fst M)
  refine
    { toFun := uA
      map_add' := uA.map_add
      map_smul' := ?_ }
  intro r x
  have happ : f.appTop ≫ fst.appTop = g.appTop ≫ snd.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h]
  have hr : fst.appTop (f.appTop r) = snd.appTop (g.appTop r) := by
    simpa only [CommRingCat.comp_apply] using
      ConcreteCategory.congr_hom happ r
  have hu := uA.map_smul (f.appTop r) x
  change uA (f.appTop r • x) = snd.appTop (g.appTop r) • uA x
  rw [← hr]
  exact hu

@[simp]
theorem pullbackUnitTopBaseLinearMapRaw_apply
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
      topSectionsBaseModule f M
    letI : Module Γ(Y, ⊤)
        Γ((pullback fst).obj M, (⊤ : P.Opens)) :=
      topSectionsBaseModule snd ((pullback fst).obj M)
    letI : Module Γ(Z, ⊤)
        Γ((pullback fst).obj M, (⊤ : P.Opens)) :=
      Module.compHom Γ((pullback fst).obj M, (⊤ : P.Opens)) g.appTop.hom
    pullbackUnitTopBaseLinearMapRaw fst snd f g h M x =
      pullbackUnitTop fst M x := by
  let N := (pullback fst).obj M
  letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
    topSectionsBaseModule f M
  letI : Module Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule snd N
  letI : Module Γ(Z, ⊤) Γ(N, (⊤ : P.Opens)) :=
    Module.compHom Γ(N, (⊤ : P.Opens)) g.appTop.hom
  letI : Module Γ(X, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule fst N
  change (topSectionsBaseLinearEquiv fst N).symm
    ((pullbackUnitTopLinearMap fst M) x) = pullbackUnitTop fst M x
  rw [topSectionsBaseLinearEquiv_symm_apply,
    pullbackUnitTopLinearMap_apply]

noncomputable def pullbackUnitBaseLinearMap
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules) :
    letI : Module Γ(Z, ⊤)
        (baseSections snd ((pullback fst).obj M)) :=
      baseSectionsFurtherBaseModule snd g ((pullback fst).obj M)
    baseSections f M →ₗ[Γ(Z, ⊤)]
      baseSections snd ((pullback fst).obj M) := by
  let N := (pullback fst).obj M
  letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
    topSectionsBaseModule f M
  letI : Module Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule snd N
  letI : Module Γ(Z, ⊤) Γ(N, (⊤ : P.Opens)) :=
    Module.compHom Γ(N, (⊤ : P.Opens)) g.appTop.hom
  letI : Module Γ(Z, ⊤) (baseSections snd N) :=
    baseSectionsFurtherBaseModule snd g N
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) (baseSections snd N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eSource := topSectionsBaseLinearEquiv f M
  let eTarget := topSectionsBaseLinearEquiv snd N
  exact (eTarget.toLinearMap.restrictScalars Γ(Z, ⊤)).comp
    ((pullbackUnitTopBaseLinearMapRaw fst snd f g h M).comp
      eSource.symm.toLinearMap)

@[simp]
theorem pullbackUnitBaseLinearMap_apply
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    (x : baseSections f M) :
    letI : Module Γ(Z, ⊤)
        (baseSections snd ((pullback fst).obj M)) :=
      baseSectionsFurtherBaseModule snd g ((pullback fst).obj M)
    pullbackUnitBaseLinearMap fst snd f g h M x =
      pullbackUnitTop fst M x := by
  let N := (pullback fst).obj M
  letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
    topSectionsBaseModule f M
  letI : Module Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule snd N
  letI : Module Γ(Z, ⊤) Γ(N, (⊤ : P.Opens)) :=
    Module.compHom Γ(N, (⊤ : P.Opens)) g.appTop.hom
  letI : Module Γ(Z, ⊤) (baseSections snd N) :=
    baseSectionsFurtherBaseModule snd g N
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) (baseSections snd N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eSource := topSectionsBaseLinearEquiv f M
  let eTarget := topSectionsBaseLinearEquiv snd N
  let raw := pullbackUnitTopBaseLinearMapRaw fst snd f g h M
  let xRaw : Γ(M, (⊤ : X.Opens)) := x
  let unitRaw : Γ(M, (⊤ : X.Opens)) → Γ(N, (⊤ : P.Opens)) :=
    fun z ↦ pullbackUnitTop fst M z
  let toBase : Γ(N, (⊤ : P.Opens)) → baseSections snd N :=
    fun z ↦ z
  have hSource : eSource.symm x = xRaw := by
    dsimp only [eSource, xRaw]
    exact topSectionsBaseLinearEquiv_symm_apply f M x
  have hRaw (z : Γ(M, (⊤ : X.Opens))) : raw z = unitRaw z := by
    dsimp only [raw, unitRaw]
    exact pullbackUnitTopBaseLinearMapRaw_apply fst snd f g h M z
  have hTarget (z : Γ(N, (⊤ : P.Opens))) :
      eTarget z = toBase z := by
    dsimp only [eTarget, toBase]
    exact topSectionsBaseLinearEquiv_apply snd N z
  have hMiddle : raw (eSource.symm x) = unitRaw xRaw :=
    (hRaw (eSource.symm x)).trans (congrArg unitRaw hSource)
  change eTarget (raw (eSource.symm x)) = pullbackUnitTop fst M x
  exact (congrArg eTarget hMiddle).trans ((hTarget _).trans rfl)

theorem pullbackUnitTopLinearMap_isBaseChange_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
    letI : Module Γ(Y, ⊤) (baseSections f ((pullback f).obj M)) :=
      baseSectionsSourceModule f ((pullback f).obj M)
    letI : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤)
        (baseSections f ((pullback f).obj M)) :=
      baseSections_isScalarTower f ((pullback f).obj M)
    IsBaseChange Γ(Y, ⊤) (pullbackUnitTopLinearMap f M) := by
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  letI : Module Γ(Y, ⊤) (baseSections f ((pullback f).obj M)) :=
    baseSectionsSourceModule f ((pullback f).obj M)
  letI : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤)
      (baseSections f ((pullback f).obj M)) :=
    baseSections_isScalarTower f ((pullback f).obj M)
  let b := X.isoSpec.inv
  let g := Spec.map f.appTop
  let a := Y.isoSpec.hom
  let Mb := (pullback b).obj M
  have hMb : Mb.IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffine b M
  letI : Mb.IsQuasicoherent := hMb
  let Mg := (pullback g).obj Mb
  let Ma := (pullback a).obj Mg
  letI : Module Γ(X, ⊤) (moduleSpecΓFunctor.obj Mg) :=
    Module.compHom (moduleSpecΓFunctor.obj Mg) f.appTop.hom
  letI : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤)
      (moduleSpecΓFunctor.obj Mg) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module Γ(X, ⊤) Γ(Ma, (⊤ : Y.Opens)) :=
    Module.compHom Γ(Ma, (⊤ : Y.Opens)) f.appTop.hom
  letI : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤)
      Γ(Ma, (⊤ : Y.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eB := isoSpecInvPullbackUnitTopLinearEquiv X M
  let cSpec := specPullbackSectionsLinearMap f.appTop Mb
  let eA := isoSpecHomPullbackUnitTopLinearEquiv Y Mg
  let eSheaf := affinePullbackDecompositionIso f M
  let eTop : Γ(Ma, (⊤ : Y.Opens)) ≃ₗ[Γ(Y, ⊤)]
      baseSections f ((pullback f).obj M) :=
    topSectionsLinearEquivOfIso eSheaf
  let composite : Γ(M, (⊤ : X.Opens)) →ₗ[Γ(X, ⊤)]
      baseSections f ((pullback f).obj M) :=
    (eTop.toLinearMap.restrictScalars Γ(X, ⊤)).comp
      ((eA.toLinearMap.restrictScalars Γ(X, ⊤)).comp
        (cSpec.comp eB.toLinearMap))
  have hSpec : IsBaseChange Γ(Y, ⊤) cSpec :=
    specPullbackSectionsLinearMap_isBaseChange f.appTop Mb
  have hComposite : IsBaseChange Γ(Y, ⊤) composite := by
    exact (((hSpec.comp_equiv eB cSpec).comp
      (IsBaseChange.ofEquiv eA)).comp
      (IsBaseChange.ofEquiv eTop))
  have hEq : composite = pullbackUnitTopLinearMap f M := by
    ext x
    have heB (z : Γ(M, (⊤ : X.Opens))) :
        eB z = pullbackUnitTop b M z := by
      dsimp only [eB, b]
      exact isoSpecInvPullbackUnitTopLinearEquiv_apply X M z
    have hcSpec (z : moduleSpecΓFunctor.obj Mb) :
        cSpec z = pullbackUnitTop g Mb z := by
      dsimp only [cSpec, g]
      exact specPullbackSectionsLinearMap_apply f.appTop Mb z
    have heA (z : moduleSpecΓFunctor.obj Mg) :
        eA z = pullbackUnitTop a Mg z := by
      dsimp only [eA, a]
      exact isoSpecHomPullbackUnitTopLinearMap_apply Y Mg z
    have heTop (z : Γ(Ma, (⊤ : Y.Opens))) :
        eTop z = eSheaf.hom.val.app (.op ⊤) z := by
      rfl
    let unitB : moduleSpecΓFunctor.obj Mb :=
      pullbackUnitTop b M x
    let unitG : moduleSpecΓFunctor.obj Mb →
        moduleSpecΓFunctor.obj Mg :=
      fun z ↦ pullbackUnitTop g Mb z
    let unitA : moduleSpecΓFunctor.obj Mg → Γ(Ma, (⊤ : Y.Opens)) :=
      fun z ↦ pullbackUnitTop a Mg z
    let eSheafFun : Γ(Ma, (⊤ : Y.Opens)) →
        baseSections f ((pullback f).obj M) :=
      fun z ↦ eSheaf.hom.val.app (.op ⊤) z
    let xb : moduleSpecΓFunctor.obj Mb := eB x
    let xg : moduleSpecΓFunctor.obj Mg := cSpec xb
    let xa : Γ(Ma, (⊤ : Y.Opens)) := eA xg
    have hxb : xb = unitB := by
      dsimp only [xb, unitB]
      exact heB x
    have hcSpec' (z : moduleSpecΓFunctor.obj Mb) :
        cSpec z = unitG z := by
      dsimp only [unitG]
      exact hcSpec z
    have hxg : xg = unitG unitB := by
      exact (hcSpec' xb).trans (congrArg unitG hxb)
    have heA' (z : moduleSpecΓFunctor.obj Mg) :
        eA z = unitA z := by
      dsimp only [unitA]
      exact heA z
    have hxa : xa = unitA (unitG unitB) := by
      exact (heA' xg).trans (congrArg unitA hxg)
    have heTop' (z : Γ(Ma, (⊤ : Y.Opens))) :
        eTop z = eSheafFun z := by
      dsimp only [eSheafFun]
      exact heTop z
    have hgeom : eSheafFun (unitA (unitG unitB)) =
        pullbackUnitTop f M x := by
      dsimp only [eSheafFun, unitA, unitG, unitB, eSheaf,
        a, g, b, Mg, Mb]
      exact affinePullbackDecompositionIso_hom_pullbackUnitTop f M x
    change eTop (eA (cSpec (eB x))) = pullbackUnitTop f M x
    exact (heTop' xa).trans
      ((congrArg eSheafFun hxa).trans hgeom)
  rw [← hEq]
  exact hComposite

theorem pullbackUnitBaseLinearMap_isBaseChange_of_isPullback
    {P X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent] :
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : Module Γ(Z, ⊤)
        (baseSections snd ((pullback fst).obj M)) :=
      baseSectionsFurtherBaseModule snd g ((pullback fst).obj M)
    letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
        (baseSections snd ((pullback fst).obj M)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange Γ(Y, ⊤)
      (pullbackUnitBaseLinearMap fst snd f g h.w M) := by
  let N := (pullback fst).obj M
  letI : IsAffine P := IsAffine.of_isPullback h
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(Z, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := snd.appTop.hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(P, ⊤) := fst.appTop.hom.toAlgebra
  letI : Algebra Γ(Z, ⊤) Γ(P, ⊤) :=
    (g.appTop ≫ snd.appTop).hom.toAlgebra
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have happ : f.appTop ≫ fst.appTop = g.appTop ≫ snd.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h.w]
  letI : IsScalarTower Γ(Z, ⊤) Γ(X, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change snd.appTop (g.appTop r) = fst.appTop (f.appTop r)
      simpa only [CommRingCat.comp_apply] using
        (ConcreteCategory.congr_hom happ r).symm
  have hPush : Algebra.IsPushout Γ(Z, ⊤) Γ(Y, ⊤)
      Γ(X, ⊤) Γ(P, ⊤) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    exact (isPushout_appTop_of_isPullback h).flip
  letI : Module Γ(Z, ⊤) Γ(M, (⊤ : X.Opens)) :=
    topSectionsBaseModule f M
  letI : IsScalarTower Γ(Z, ⊤) Γ(X, ⊤)
      Γ(M, (⊤ : X.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module Γ(X, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule fst N
  letI : Module Γ(Y, ⊤) Γ(N, (⊤ : P.Opens)) :=
    topSectionsBaseModule snd N
  letI : Module Γ(Z, ⊤) Γ(N, (⊤ : P.Opens)) :=
    Module.compHom Γ(N, (⊤ : P.Opens)) g.appTop.hom
  letI : IsScalarTower Γ(X, ⊤) Γ(P, ⊤)
      Γ(N, (⊤ : P.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤)
      Γ(N, (⊤ : P.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
      Γ(N, (⊤ : P.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module Γ(P, ⊤) (baseSections fst N) :=
    baseSectionsSourceModule fst N
  letI : IsScalarTower Γ(X, ⊤) Γ(P, ⊤)
      (baseSections fst N) :=
    baseSections_isScalarTower fst N
  let eFst := topSectionsBaseLinearEquiv fst N
  let eFstSource := topSectionsSourceLinearEquiv fst N
  let uA : Γ(M, (⊤ : X.Opens)) →ₗ[Γ(X, ⊤)]
      Γ(N, (⊤ : P.Opens)) :=
    eFst.symm.toLinearMap.comp (pullbackUnitTopLinearMap fst M)
  have hAffine : IsBaseChange Γ(P, ⊤)
      (pullbackUnitTopLinearMap fst M) :=
    pullbackUnitTopLinearMap_isBaseChange_of_isAffine fst M
  have hANatural : IsBaseChange Γ(P, ⊤) uA := by
    refine IsBaseChange.of_equiv
      (hAffine.equiv.trans eFstSource.symm) ?_
    intro x
    change eFstSource.symm (hAffine.equiv (1 ⊗ₜ[Γ(X, ⊤)] x)) =
      uA x
    rw [hAffine.equiv_tmul]
    rw [one_smul]
    rfl
  letI : Algebra.IsPushout Γ(Z, ⊤) Γ(Y, ⊤)
      Γ(X, ⊤) Γ(P, ⊤) := hPush
  let eCancel := Algebra.IsPushout.cancelBaseChange
    Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) Γ(P, ⊤)
      Γ(M, (⊤ : X.Opens))
  let eRaw : Γ(Y, ⊤) ⊗[Γ(Z, ⊤)] Γ(M, (⊤ : X.Opens)) ≃ₗ[Γ(Y, ⊤)]
      Γ(N, (⊤ : P.Opens)) :=
    eCancel.symm.trans (hANatural.equiv.restrictScalars Γ(Y, ⊤))
  let raw := pullbackUnitTopBaseLinearMapRaw fst snd f g h.w M
  have hRaw : IsBaseChange Γ(Y, ⊤) raw := by
    refine IsBaseChange.of_equiv eRaw ?_
    intro x
    change hANatural.equiv (eCancel.symm (1 ⊗ₜ[Γ(Z, ⊤)] x)) =
      raw x
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
    simp only [map_one]
    rw [hANatural.equiv_tmul]
    rw [one_smul]
    rfl
  letI : Module Γ(Z, ⊤) (baseSections snd N) :=
    baseSectionsFurtherBaseModule snd g N
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) (baseSections snd N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eSource := topSectionsBaseLinearEquiv f M
  let eTarget := topSectionsBaseLinearEquiv snd N
  let eTensor := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(Y, ⊤) Γ(Y, ⊤)) eSource.symm
  let eBase := (eTensor.trans hRaw.equiv).trans eTarget
  refine IsBaseChange.of_equiv eBase ?_
  intro x
  change eTarget
    (hRaw.equiv (1 ⊗ₜ[Γ(Z, ⊤)] eSource.symm x)) =
      pullbackUnitBaseLinearMap fst snd f g h.w M x
  rw [hRaw.equiv_tmul]
  rw [one_smul]
  rfl

end AlgebraicGeometry.Scheme.Modules
