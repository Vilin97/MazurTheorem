/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineModuleBaseChange
import MazurTorsion.Upstream.AffineDivisorTensorBaseChange

/-!
# Affine tilde base change for divisor tensor addition

The fixed tensor-addition comparison for affine divisor modules is transported through the
canonical affine comparison between pullback of a tilde sheaf and tilde of extension of scalars.
The resulting tensor comparison is relative to that affine tilde comparison.  Its identification
with the monoidal tensorator of sheaf pullback is deliberately left to a later coherence result.
The single-factor comparison is now identified with the specified open-immersion restriction
comparison used by the overlap-descent chain.
-/

namespace MazurTorsion.AlgebraicGeometry

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped ChangeOfRings nonZeroDivisors TensorProduct

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForTildeBaseChange (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Reinterpret the carrier of Mathlib's extension-of-scalars object as the usual algebra tensor
product, and then apply a supplied linear equivalence. -/
private noncomputable def extendScalarsCarrierEquiv
    (R B M N : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N]
    [Algebra R B]
    (e : B ⊗[R] M ≃ₗ[B] N) :
    (ModuleCat.extendScalars (algebraMap R B)).obj
        (ModuleCat.of R M) ≃ₗ[B] N := by
  dsimp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
  letI : IsScalarTower R B
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eB : ((ModuleCat.restrictScalars (algebraMap R B)).obj
      (ModuleCat.of B B)) ≃ₗ[B] B := LinearEquiv.refl B B
  let eM : ModuleCat.of R M ≃ₗ[R] M := LinearEquiv.refl R M
  exact (TensorProduct.AlgebraTensorModule.congr eB eM).trans e

private lemma extendScalarsCarrierEquiv_apply_tmul
    (R B M N : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N]
    [Algebra R B]
    (e : B ⊗[R] M ≃ₗ[B] N) (b : B) (m : M) :
    extendScalarsCarrierEquiv R B M N e (b ⊗ₜ[R] m) = e (b ⊗ₜ[R] m) := by
  change ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl B B) (LinearEquiv.refl R M)).trans e)
      (b ⊗ₜ[R] m) = e (b ⊗ₜ[R] m)
  simp

/-- The carrier bridge is natural in the source module. -/
private theorem extendScalarsCarrierEquiv_naturality
    (R B M N P : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module B P]
    [Algebra R B]
    (g : M ≃ₗ[R] N) (e : B ⊗[R] N ≃ₗ[B] P) :
    (ModuleCat.extendScalars (algebraMap R B)).map g.toModuleIso.hom ≫
        (extendScalarsCarrierEquiv R B N P e).toModuleIso.hom =
      (extendScalarsCarrierEquiv R B M P
        ((g.baseChange R B).trans e)).toModuleIso.hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change extendScalarsCarrierEquiv R B N P e ((1 : B) ⊗ₜ[R] g m) =
    extendScalarsCarrierEquiv R B M P ((g.baseChange R B).trans e)
      ((1 : B) ⊗ₜ[R] m)
  rw [extendScalarsCarrierEquiv_apply_tmul, extendScalarsCarrierEquiv_apply_tmul]
  rfl

/-- The carrier bridge carries composition of raw equivalences to categorical composition. -/
private theorem extendScalarsCarrierEquiv_trans_hom
    (R B M N P : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P]
    [Algebra R B]
    (e : B ⊗[R] M ≃ₗ[B] N) (f : N ≃ₗ[B] P) :
    (extendScalarsCarrierEquiv R B M N e).toModuleIso.hom ≫
        f.toModuleIso.hom =
      (extendScalarsCarrierEquiv R B M P (e.trans f)).toModuleIso.hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change f (extendScalarsCarrierEquiv R B M N e ((1 : B) ⊗ₜ[R] m)) =
    extendScalarsCarrierEquiv R B M P (e.trans f) ((1 : B) ⊗ₜ[R] m)
  rw [extendScalarsCarrierEquiv_apply_tmul, extendScalarsCarrierEquiv_apply_tmul]
  rfl

namespace AffineTilde

/-- Relative to the canonical affine tilde/extension-of-scalars comparison, pullback of the
tensor of two tilde sheaves is tilde of a specified scalar-extension target.  This private
comparison is the implementation path for the divisor-specific public comparison below.

No factorization through the tensor of the two individually pulled-back sheaves is asserted. -/
private noncomputable def tildeTensorPullbackIsoExtendScalars
    (R B M N P : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module B P]
    (e : B ⊗[R] (M ⊗[R] N) ≃ₗ[B] P) :
    (Scheme.Modules.pullback
        (AffineDivisorLocalization.CommonExtension.extensionMap R B)).obj
        (_root_.AlgebraicGeometry.tilde (ModuleCat.of R M) ⊗
          _root_.AlgebraicGeometry.tilde (ModuleCat.of R N)) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B P) :=
  (Scheme.Modules.pullback
      (AffineDivisorLocalization.CommonExtension.extensionMap R B)).mapIso
        (tildeTensorIso R M N) ≪≫
    (Scheme.Modules.tildePullbackIsoExtendScalars
      (CommRingCat.ofHom (algebraMap R B))).app
        (ModuleCat.of R (M ⊗[R] N)) ≪≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).mapIso
      (extendScalarsCarrierEquiv R B (M ⊗[R] N) P e).toModuleIso

/-- The affine tilde/extension-of-scalars tail of the generic tensor pullback comparison. -/
private noncomputable def tildeTensorPullbackHomTail
    (R B M N P : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module B P]
    (e : B ⊗[R] (M ⊗[R] N) ≃ₗ[B] P) :
    (Scheme.Modules.pullback
      (AffineDivisorLocalization.CommonExtension.extensionMap R B)).obj
        (_root_.AlgebraicGeometry.tilde (ModuleCat.of R (M ⊗[R] N))) ⟶
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B) (ModuleCat.of B P) :=
  (Scheme.Modules.tildePullbackIsoExtendScalars
      (CommRingCat.ofHom (algebraMap R B))).hom.app
        (ModuleCat.of R (M ⊗[R] N)) ≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
      (extendScalarsCarrierEquiv R B (M ⊗[R] N) P e).toModuleIso.hom

/-- Hom expansion of the generic affine tilde tensor/pullback comparison. -/
private theorem tildeTensorPullbackIsoExtendScalars_hom
    (R B M N P : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module B P]
    (e : B ⊗[R] (M ⊗[R] N) ≃ₗ[B] P) :
    (tildeTensorPullbackIsoExtendScalars R B M N P e).hom =
      (Scheme.Modules.pullback
        (AffineDivisorLocalization.CommonExtension.extensionMap R B)).map
          (tildeTensorIso R M N).hom ≫
        tildeTensorPullbackHomTail R B M N P e :=
  rfl

end AffineTilde

namespace AffineDivisorLocalization.CommonExtension

/-- Hom expansion of the deterministic affine line-bundle addition isomorphism. -/
private theorem lineBundleAddIso_hom
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (ExplicitIdeal.lineBundleAddIso R K D E).hom =
      (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
          (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom ≫
        (AffineTilde.tildeTensorIso R
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).inv :=
  rfl

/-- Pullback of affine line-bundle addition followed by the mapped affine tilde tensor
comparison cancels the tensor comparison introduced by `lineBundleAddIso`. -/
private theorem pullback_lineBundleAddIso_hom_tildeTensor
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [Algebra R B]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).map
          (ExplicitIdeal.lineBundleAddIso R K D E).hom ≫
        (Scheme.Modules.pullback (extensionMap R B)).map
          (AffineTilde.tildeTensorIso R
            (AffineDedekind.lineBundleModule R K D)
            (AffineDedekind.lineBundleModule R K E)).hom =
      (Scheme.Modules.pullback (extensionMap R B)).map
        ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
          (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) := by
  let f := (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
    (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom
  let τ := AffineTilde.tildeTensorIso R
    (AffineDedekind.lineBundleModule R K D)
    (AffineDedekind.lineBundleModule R K E)
  have hinner :
      (ExplicitIdeal.lineBundleAddIso R K D E).hom ≫ τ.hom = f := by
    have hlineBundle :
        (ExplicitIdeal.lineBundleAddIso R K D E).hom ≫ τ.hom =
          (f ≫ τ.inv) ≫ τ.hom :=
      congrArg (fun q ↦ q ≫ τ.hom) (lineBundleAddIso_hom R K D E)
    have hassoc :
        (f ≫ τ.inv) ≫ τ.hom = f ≫ (τ.inv ≫ τ.hom) :=
      Category.assoc f τ.inv τ.hom
    have hcancel : f ≫ (τ.inv ≫ τ.hom) = f ≫ 𝟙 _ :=
      congrArg (fun q ↦ f ≫ q) τ.inv_hom_id
    have hidentity : f ≫ 𝟙 _ = f := Category.comp_id f
    exact hlineBundle.trans (hassoc.trans (hcancel.trans hidentity))
  have hmapComp :
      (Scheme.Modules.pullback (extensionMap R B)).map
            (ExplicitIdeal.lineBundleAddIso R K D E).hom ≫
          (Scheme.Modules.pullback (extensionMap R B)).map
            (AffineTilde.tildeTensorIso R
              (AffineDedekind.lineBundleModule R K D)
              (AffineDedekind.lineBundleModule R K E)).hom =
        (Scheme.Modules.pullback (extensionMap R B)).map
          ((ExplicitIdeal.lineBundleAddIso R K D E).hom ≫
            (AffineTilde.tildeTensorIso R
              (AffineDedekind.lineBundleModule R K D)
              (AffineDedekind.lineBundleModule R K E)).hom) :=
    ((Scheme.Modules.pullback (extensionMap R B)).map_comp _ _).symm
  have hmapInner :
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((ExplicitIdeal.lineBundleAddIso R K D E).hom ≫
            (AffineTilde.tildeTensorIso R
              (AffineDedekind.lineBundleModule R K D)
              (AffineDedekind.lineBundleModule R K E)).hom) =
        (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) :=
    congrArg (Scheme.Modules.pullback (extensionMap R B)).map hinner
  exact hmapComp.trans hmapInner

/-- The landed tensor-to-sum module square, rewritten in the sum-to-tensor orientation used by
the sheaf addition isomorphism. -/
private theorem lineBundleModuleAddEquiv_baseChange
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((ExplicitIdeal.lineBundleModuleAddEquiv R K D E).baseChange R B).trans
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).trans
        (TensorProduct.congr
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E))) =
      (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E)).trans
        (extendedInverseIdealTensorAddEquiv R B K D E).symm := by
  rw [ExplicitIdeal.lineBundleModuleAddEquiv, LinearEquiv.baseChange_symm]
  let A := (ExplicitIdeal.lineBundleModuleTensorAddEquiv R K D E).baseChange R B
  let cSum := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E)
  let δ := TensorProduct.AlgebraTensorModule.distribBaseChange R B
    (AffineDedekind.lineBundleModule R K D)
    (AffineDedekind.lineBundleModule R K E)
  let C := TensorProduct.congr
    (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
    (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)
  let m := extendedInverseIdealTensorAddEquiv R B K D E
  change A.symm.trans (δ.trans C) = cSum.trans m.symm
  have h : A.trans cSum = δ.trans (C.trans m) :=
    lineBundleModuleTensorAddEquiv_baseChange R B K D E
  have hpost : (A.trans cSum).trans m.symm = δ.trans C := by
    rw [h]
    exact LinearEquiv.trans_symm_cancel_right m (δ.trans C)
  calc
    A.symm.trans (δ.trans C) =
        A.symm.trans ((A.trans cSum).trans m.symm) := congrArg A.symm.trans hpost.symm
    _ = cSum.trans m.symm :=
      LinearEquiv.symm_trans_cancel_left A (cSum.trans m.symm)

/-- The reversed module square after passing through Mathlib's categorical
extension-of-scalars carrier. -/
private theorem lineBundleModuleAdd_extendScalarsCarrier_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (ModuleCat.extendScalars (algebraMap R B)).map
          (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom ≫
        (extendScalarsCarrierEquiv R B
          (AffineDedekind.lineBundleModule R K D ⊗[R]
            AffineDedekind.lineBundleModule R K E)
          (extendedInverseIdeal R B K D ⊗[B]
            extendedInverseIdeal R B K E)
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
              (AffineDedekind.lineBundleModule R K D)
              (AffineDedekind.lineBundleModule R K E)).trans
            (TensorProduct.congr
              (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
              (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)))).toModuleIso.hom =
      (extendScalarsCarrierEquiv R B
        (AffineDedekind.lineBundleModule R K (D + E))
        (extendedInverseIdeal R B K (D + E))
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E))).toModuleIso.hom ≫
        (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso.hom := by
  rw [extendScalarsCarrierEquiv_naturality]
  rw [lineBundleModuleAddEquiv_baseChange]
  exact extendScalarsCarrierEquiv_trans_hom R B
    (AffineDedekind.lineBundleModule R K (D + E))
    (extendedInverseIdeal R B K (D + E))
    (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
    (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E))
    (extendedInverseIdealTensorAddEquiv R B K D E).symm

/-- Tilde of the extended inverse ideal of a divisor sum is the tensor product of the two
extended inverse-ideal tilde sheaves. -/
noncomputable def extendedInverseIdealAddIso
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R B K (D + E))) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K E)) :=
  (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).mapIso
      (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso ≪≫
    (AffineTilde.tildeTensorIso B
      (extendedInverseIdeal R B K D)
      (extendedInverseIdeal R B K E)).symm

/-- Hom expansion of addition for extended inverse-ideal tilde sheaves. -/
private theorem extendedInverseIdealAddIso_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (extendedInverseIdealAddIso R B K D E).hom =
      (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
          (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso.hom ≫
        (AffineTilde.tildeTensorIso B
          (extendedInverseIdeal R B K D)
          (extendedInverseIdeal R B K E)).inv :=
  rfl

/-- The pulled-back fixed line bundle is identified with the tilde sheaf of its extended inverse
ideal using the canonical affine tilde/extension-of-scalars comparison.  The `ViaExtendScalars`
suffix distinguishes this comparison from the older private mate used by the overlap chain. -/
noncomputable def lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        (AffineDedekind.lineBundle R K D).obj ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R B K D)) :=
  (Scheme.Modules.tildePullbackIsoExtendScalars
      (CommRingCat.ofHom (algebraMap R B))).app
        (ModuleCat.of R (AffineDedekind.lineBundleModule R K D)) ≪≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).mapIso
      (extendScalarsCarrierEquiv R B
        (AffineDedekind.lineBundleModule R K D)
        (extendedInverseIdeal R B K D)
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)).toModuleIso

/-- Hom expansion of the fixed-line-bundle comparison through affine extension of scalars. -/
private theorem lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D).hom =
      (Scheme.Modules.tildePullbackIsoExtendScalars
        (CommRingCat.ofHom (algebraMap R B))).hom.app
          (ModuleCat.of R (AffineDedekind.lineBundleModule R K D)) ≫
        (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
          (extendScalarsCarrierEquiv R B
            (AffineDedekind.lineBundleModule R K D)
            (extendedInverseIdeal R B K D)
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)).toModuleIso.hom :=
  rfl

/-- The open-immersion restriction comparison used by the overlap tower is the restriction-to-
pullback comparison followed by the public affine tilde/extension-of-scalars comparison.  This
identifies the legacy restriction API with the fixed scalar-extension path used below. -/
theorem restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq_viaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K D =
      (Scheme.Modules.restrictFunctorIsoPullback
          (extensionMap R B)).app
            (AffineDedekind.lineBundle R K D).obj ≪≫
        lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D := by
  apply Iso.ext
  rfl

/-- Pullback of the tensor of the two fixed line bundles is identified directly with the tensor
of the two extended inverse-ideal tilde sheaves.  The comparison runs through the affine
tilde/extension-of-scalars isomorphism and the module-level distributivity equivalence.

No identification with the tensor of the two factorwise pullbacks, or with the canonical
monoidal tensorator of pullback, is asserted here. -/
noncomputable def lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        ((AffineDedekind.lineBundle R K D).obj ⊗
          (AffineDedekind.lineBundle R K E).obj) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K E)) :=
  AffineTilde.tildeTensorPullbackIsoExtendScalars R B
      (AffineDedekind.lineBundleModule R K D)
      (AffineDedekind.lineBundleModule R K E)
      (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).trans
        (TensorProduct.congr
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E))) ≪≫
    (AffineTilde.tildeTensorIso B
      (extendedInverseIdeal R B K D)
      (extendedInverseIdeal R B K E)).symm

/-- Hom expansion of the direct comparison from a pulled-back tensor of fixed line bundles to
the tensor of the two raw extended inverse-ideal tilde sheaves. -/
private theorem lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E).hom =
      (AffineTilde.tildeTensorPullbackIsoExtendScalars R B
        (AffineDedekind.lineBundleModule R K D)
        (AffineDedekind.lineBundleModule R K E)
        (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
            (AffineDedekind.lineBundleModule R K D)
            (AffineDedekind.lineBundleModule R K E)).trans
          (TensorProduct.congr
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)))).hom ≫
        (AffineTilde.tildeTensorIso B
          (extendedInverseIdeal R B K D)
          (extendedInverseIdeal R B K E)).inv :=
  rfl

/-- The direct divisor comparison, normalized so its pulled tilde-tensor component is the first
arrow and the remaining affine extension-of-scalars path is an opaque tail. -/
private theorem lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_normalized
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E).hom =
      (Scheme.Modules.pullback (extensionMap R B)).map
          (AffineTilde.tildeTensorIso R
            (AffineDedekind.lineBundleModule R K D)
            (AffineDedekind.lineBundleModule R K E)).hom ≫
        (AffineTilde.tildeTensorPullbackHomTail R B
            (AffineDedekind.lineBundleModule R K D)
            (AffineDedekind.lineBundleModule R K E)
            (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
            ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
                (AffineDedekind.lineBundleModule R K D)
                (AffineDedekind.lineBundleModule R K E)).trans
              (TensorProduct.congr
                (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
                (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E))) ≫
          (AffineTilde.tildeTensorIso B
            (extendedInverseIdeal R B K D)
            (extendedInverseIdeal R B K E)).inv) := by
  let core := AffineTilde.tildeTensorPullbackIsoExtendScalars R B
    (AffineDedekind.lineBundleModule R K D)
    (AffineDedekind.lineBundleModule R K E)
    (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
        (AffineDedekind.lineBundleModule R K D)
        (AffineDedekind.lineBundleModule R K E)).trans
      (TensorProduct.congr
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)))
  let τB := AffineTilde.tildeTensorIso B
    (extendedInverseIdeal R B K D)
    (extendedInverseIdeal R B K E)
  let pulledTensor := (Scheme.Modules.pullback (extensionMap R B)).map
    (AffineTilde.tildeTensorIso R
      (AffineDedekind.lineBundleModule R K D)
      (AffineDedekind.lineBundleModule R K E)).hom
  let tail := AffineTilde.tildeTensorPullbackHomTail R B
    (AffineDedekind.lineBundleModule R K D)
    (AffineDedekind.lineBundleModule R K E)
    (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
        (AffineDedekind.lineBundleModule R K D)
        (AffineDedekind.lineBundleModule R K E)).trans
      (TensorProduct.congr
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)))
  have houter :
      (lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E).hom =
        core.hom ≫ τB.inv :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom R B K D E
  have hcore :
      core.hom ≫ τB.inv = (pulledTensor ≫ tail) ≫ τB.inv :=
    congrArg (fun q ↦ q ≫ τB.inv)
      (AffineTilde.tildeTensorPullbackIsoExtendScalars_hom R B
        (AffineDedekind.lineBundleModule R K D)
        (AffineDedekind.lineBundleModule R K E)
        (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
            (AffineDedekind.lineBundleModule R K D)
            (AffineDedekind.lineBundleModule R K E)).trans
          (TensorProduct.congr
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E))))
  have hassoc :
      (pulledTensor ≫ tail) ≫ τB.inv = pulledTensor ≫ (tail ≫ τB.inv) :=
    Category.assoc pulledTensor tail τB.inv
  exact houter.trans (hcore.trans hassoc)

/-- The affine tilde/extension-of-scalars arrow for the tensor of the two fixed modules. -/
private noncomputable def lineBundleTensorPullbackAINTArrow
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
          (ModuleCat.of R
            (AffineDedekind.lineBundleModule R K D ⊗[R]
              AffineDedekind.lineBundleModule R K E))) ⟶
      (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).obj
        ((ModuleCat.extendScalars (algebraMap R B)).obj
          (ModuleCat.of R
            (AffineDedekind.lineBundleModule R K D ⊗[R]
              AffineDedekind.lineBundleModule R K E))) :=
  (Scheme.Modules.tildePullbackIsoExtendScalars
      (CommRingCat.ofHom (algebraMap R B))).hom.app
        (ModuleCat.of R (AffineDedekind.lineBundleModule R K D ⊗[R]
          AffineDedekind.lineBundleModule R K E))

/-- The mapped extension-of-scalars carrier arrow for the two extended inverse ideals. -/
private noncomputable def lineBundleTensorPullbackCarrierArrow
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).obj
          ((ModuleCat.extendScalars (algebraMap R B)).obj
            (ModuleCat.of R
              (AffineDedekind.lineBundleModule R K D ⊗[R]
                AffineDedekind.lineBundleModule R K E))) ⟶
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R B K D ⊗[B]
          extendedInverseIdeal R B K E)) :=
  (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
    (extendScalarsCarrierEquiv R B
      (AffineDedekind.lineBundleModule R K D ⊗[R]
        AffineDedekind.lineBundleModule R K E)
      (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).trans
        (TensorProduct.congr
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)))).toModuleIso.hom

/-- The inverse affine tilde tensor comparison for the two extended inverse ideals. -/
private noncomputable def lineBundleTensorPullbackTensorInvArrow
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K D ⊗[B]
            extendedInverseIdeal R B K E)) ⟶
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K E))) :=
  (AffineTilde.tildeTensorIso B
    (extendedInverseIdeal R B K D)
    (extendedInverseIdeal R B K E)).inv

/-- The original generic affine tilde tail specialized to the divisor modules. -/
private noncomputable def lineBundleTensorPullbackGenericTailViaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
          (ModuleCat.of R
            (AffineDedekind.lineBundleModule R K D ⊗[R]
              AffineDedekind.lineBundleModule R K E))) ⟶
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K E))) :=
  AffineTilde.tildeTensorPullbackHomTail R B
      (AffineDedekind.lineBundleModule R K D)
      (AffineDedekind.lineBundleModule R K E)
      (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).trans
        (TensorProduct.congr
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
          (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E))) ≫
    (AffineTilde.tildeTensorIso B
      (extendedInverseIdeal R B K D)
      (extendedInverseIdeal R B K E)).inv

/-- The divisor-specialized affine extension-of-scalars tail used to split the final coherence
proof at a small, typed morphism boundary. -/
private noncomputable def lineBundleTensorPullbackTailViaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
          (ModuleCat.of R
            (AffineDedekind.lineBundleModule R K D ⊗[R]
              AffineDedekind.lineBundleModule R K E))) ⟶
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K E))) :=
  (lineBundleTensorPullbackAINTArrow R B K D E ≫
      lineBundleTensorPullbackCarrierArrow R B K D E) ≫
    lineBundleTensorPullbackTensorInvArrow R B K D E

/-- The generic specialized tail is definitionally the componentized left-associated tail. -/
private theorem lineBundleTensorPullbackGenericTailViaExtendScalars_eq
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    lineBundleTensorPullbackGenericTailViaExtendScalars R B K D E =
      lineBundleTensorPullbackTailViaExtendScalars R B K D E := by
  dsimp only [lineBundleTensorPullbackGenericTailViaExtendScalars,
    lineBundleTensorPullbackTailViaExtendScalars,
    lineBundleTensorPullbackAINTArrow,
    lineBundleTensorPullbackCarrierArrow,
    lineBundleTensorPullbackTensorInvArrow,
    AffineTilde.tildeTensorPullbackHomTail]

/-- The right-associated affine tilde/extension-of-scalars form of the specialized tail. -/
private noncomputable def lineBundleTensorPullbackExpandedTailViaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
          (ModuleCat.of R
            (AffineDedekind.lineBundleModule R K D ⊗[R]
              AffineDedekind.lineBundleModule R K E))) ⟶
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
            (ModuleCat.of B (extendedInverseIdeal R B K E))) :=
  lineBundleTensorPullbackAINTArrow R B K D E ≫
    (lineBundleTensorPullbackCarrierArrow R B K D E ≫
      lineBundleTensorPullbackTensorInvArrow R B K D E)

/-- Expansion of the divisor-specialized tail through affine tilde and extension of scalars. -/
private theorem lineBundleTensorPullbackTailViaExtendScalars_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    lineBundleTensorPullbackTailViaExtendScalars R B K D E =
      lineBundleTensorPullbackExpandedTailViaExtendScalars R B K D E := by
  dsimp only [lineBundleTensorPullbackTailViaExtendScalars,
    lineBundleTensorPullbackExpandedTailViaExtendScalars]
  exact Category.assoc
    (lineBundleTensorPullbackAINTArrow R B K D E)
    (lineBundleTensorPullbackCarrierArrow R B K D E)
    (lineBundleTensorPullbackTensorInvArrow R B K D E)

/-- Evaluation of the pullback-then-direct-comparison path through the original generic affine
extension-of-scalars tail. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_lhs_to_genericTail_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((Scheme.Modules.pullback (extensionMap R B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R K D E) ≪≫
        lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
          R B K D E).hom =
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackGenericTailViaExtendScalars R B K D E := by
  rw [Iso.trans_hom, Functor.mapIso_hom]
  rw [lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_normalized]
  let t :
      (Scheme.Modules.pullback (extensionMap R B)).obj
          (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
            (ModuleCat.of R
              (AffineDedekind.lineBundleModule R K D ⊗[R]
                AffineDedekind.lineBundleModule R K E))) ⟶
        (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
              (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
          _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
              (ModuleCat.of B (extendedInverseIdeal R B K E))) :=
    lineBundleTensorPullbackGenericTailViaExtendScalars R B K D E
  have hcTail :
      ((Scheme.Modules.pullback (extensionMap R B)).map
              (ExplicitIdeal.lineBundleAddIso R K D E).hom ≫
            (Scheme.Modules.pullback (extensionMap R B)).map
              (AffineTilde.tildeTensorIso R
                (AffineDedekind.lineBundleModule R K D)
                (AffineDedekind.lineBundleModule R K E)).hom) ≫ t =
        (Scheme.Modules.pullback (extensionMap R B)).map
            ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
              (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫ t :=
    congrArg (fun q ↦ q ≫ t)
      (pullback_lineBundleAddIso_hom_tildeTensor R B K D E)
  have hcancel :
      (Scheme.Modules.pullback (extensionMap R B)).map
            (ExplicitIdeal.lineBundleAddIso R K D E).hom ≫
          ((Scheme.Modules.pullback (extensionMap R B)).map
              (AffineTilde.tildeTensorIso R
                (AffineDedekind.lineBundleModule R K D)
                (AffineDedekind.lineBundleModule R K E)).hom ≫ t) =
        (Scheme.Modules.pullback (extensionMap R B)).map
            ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
              (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫ t :=
    (Category.assoc
      ((Scheme.Modules.pullback (extensionMap R B)).map
        (ExplicitIdeal.lineBundleAddIso R K D E).hom)
      ((Scheme.Modules.pullback (extensionMap R B)).map
        (AffineTilde.tildeTensorIso R
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).hom)
      t).symm.trans hcTail
  exact hcancel

/-- The fixed module-addition prefix transports the generic/componentized tail bridge. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_genericTail_to_tail_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackGenericTailViaExtendScalars R B K D E =
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackTailViaExtendScalars R B K D E :=
  congrArg
    (fun q ↦
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫ q)
    (lineBundleTensorPullbackGenericTailViaExtendScalars_eq R B K D E)

/-- Evaluation of the pullback-then-direct-comparison path through the componentized affine
extension-of-scalars tail. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_lhs_to_tail_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((Scheme.Modules.pullback (extensionMap R B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R K D E) ≪≫
        lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
          R B K D E).hom =
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackTailViaExtendScalars R B K D E :=
  (lineBundleAddIso_pullback_viaExtendScalars_lhs_to_genericTail_hom R B K D E).trans
    (lineBundleAddIso_pullback_viaExtendScalars_genericTail_to_tail_hom R B K D E)

/-- Expanding the specialized divisor tail yields the explicit affine
tilde/extension-of-scalars middle path. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_tail_to_mid_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackTailViaExtendScalars R B K D E =
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackExpandedTailViaExtendScalars R B K D E := by
  exact congrArg
    (fun q ↦
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫ q)
    (lineBundleTensorPullbackTailViaExtendScalars_hom R B K D E)

/-- Evaluation of the pullback-then-direct-comparison path at the explicit affine middle
path. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_lhs_to_mid_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((Scheme.Modules.pullback (extensionMap R B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R K D E) ≪≫
        lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
          R B K D E).hom =
      (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackExpandedTailViaExtendScalars R B K D E :=
  (lineBundleAddIso_pullback_viaExtendScalars_lhs_to_tail_hom R B K D E).trans
    (lineBundleAddIso_pullback_viaExtendScalars_tail_to_mid_hom R B K D E)

/-- The explicit affine tilde/extension-of-scalars middle path agrees with the chosen sum
comparison followed by raw inverse-ideal addition. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_mid_to_common_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).map
          ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map
            (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom) ≫
        lineBundleTensorPullbackExpandedTailViaExtendScalars R B K D E =
      (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          R B K (D + E)).hom ≫
        ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
            (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso.hom ≫
          (AffineTilde.tildeTensorIso B
            (extendedInverseIdeal R B K D)
            (extendedInverseIdeal R B K E)).inv) := by
  dsimp only [lineBundleTensorPullbackExpandedTailViaExtendScalars]
  let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
  let AINT := Scheme.Modules.tildePullbackIsoExtendScalars
    (CommRingCat.ofHom (algebraMap R B))
  let g := (ExplicitIdeal.lineBundleModuleAddEquiv R K D E).toModuleIso.hom
  let extAdd := (ModuleCat.extendScalars (algebraMap R B)).map g
  let carrierTensor := (extendScalarsCarrierEquiv R B
    (AffineDedekind.lineBundleModule R K D ⊗[R]
      AffineDedekind.lineBundleModule R K E)
    (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R B
        (AffineDedekind.lineBundleModule R K D)
        (AffineDedekind.lineBundleModule R K E)).trans
      (TensorProduct.congr
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)))).toModuleIso.hom
  let carrierSum := (extendScalarsCarrierEquiv R B
    (AffineDedekind.lineBundleModule R K (D + E))
    (extendedInverseIdeal R B K (D + E))
    (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E))).toModuleIso.hom
  let μ := (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso.hom
  let τB := (AffineTilde.tildeTensorIso B
    (extendedInverseIdeal R B K D)
    (extendedInverseIdeal R B K E)).inv
  let AINTTensor := AINT.hom.app
    (ModuleCat.of R (AffineDedekind.lineBundleModule R K D ⊗[R]
      AffineDedekind.lineBundleModule R K E))
  let AINTSum := AINT.hom.app
    (ModuleCat.of R (AffineDedekind.lineBundleModule R K (D + E)))
  have hnat :
      (Scheme.Modules.pullback (extensionMap R B)).map
            ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map g) ≫
          (AINTTensor ≫ (TB.map carrierTensor ≫ τB)) =
        AINTSum ≫ (TB.map extAdd ≫ (TB.map carrierTensor ≫ τB)) :=
    AINT.hom.naturality_assoc g (TB.map carrierTensor ≫ τB)
  have hmapCollapse :
      TB.map extAdd ≫ (TB.map carrierTensor ≫ τB) =
        TB.map (extAdd ≫ carrierTensor) ≫ τB :=
    (TB.map_comp_assoc extAdd carrierTensor τB).symm
  have hmapCollapsePre :
      AINTSum ≫ (TB.map extAdd ≫ (TB.map carrierTensor ≫ τB)) =
        AINTSum ≫ (TB.map (extAdd ≫ carrierTensor) ≫ τB) :=
    congrArg (fun q ↦ AINTSum ≫ q) hmapCollapse
  have hcarrier : extAdd ≫ carrierTensor = carrierSum ≫ μ :=
    lineBundleModuleAdd_extendScalarsCarrier_hom R B K D E
  have hcarrierMap :
      TB.map (extAdd ≫ carrierTensor) = TB.map (carrierSum ≫ μ) :=
    congrArg TB.map hcarrier
  have hcarrierPost :
      TB.map (extAdd ≫ carrierTensor) ≫ τB =
        TB.map (carrierSum ≫ μ) ≫ τB :=
    congrArg (fun q ↦ q ≫ τB) hcarrierMap
  have hcarrierPre :
      AINTSum ≫ (TB.map (extAdd ≫ carrierTensor) ≫ τB) =
        AINTSum ≫ (TB.map (carrierSum ≫ μ) ≫ τB) :=
    congrArg (fun q ↦ AINTSum ≫ q) hcarrierPost
  have hmapExpand :
      TB.map (carrierSum ≫ μ) ≫ τB =
        TB.map carrierSum ≫ (TB.map μ ≫ τB) :=
    TB.map_comp_assoc carrierSum μ τB
  have hmapExpandPre :
      AINTSum ≫ (TB.map (carrierSum ≫ μ) ≫ τB) =
        AINTSum ≫ (TB.map carrierSum ≫ (TB.map μ ≫ τB)) :=
    congrArg (fun q ↦ AINTSum ≫ q) hmapExpand
  have hchosen :
      (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          R B K (D + E)).hom = AINTSum ≫ TB.map carrierSum :=
    lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars_hom R B K (D + E)
  have hchosenPost :
      (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
            R B K (D + E)).hom ≫ (TB.map μ ≫ τB) =
        (AINTSum ≫ TB.map carrierSum) ≫ (TB.map μ ≫ τB) :=
    congrArg (fun q ↦ q ≫ (TB.map μ ≫ τB)) hchosen
  have hchosenAssoc :
      (AINTSum ≫ TB.map carrierSum) ≫ (TB.map μ ≫ τB) =
        AINTSum ≫ (TB.map carrierSum ≫ (TB.map μ ≫ τB)) :=
    Category.assoc AINTSum (TB.map carrierSum) (TB.map μ ≫ τB)
  have hchosenPath :
      (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
            R B K (D + E)).hom ≫ (TB.map μ ≫ τB) =
        AINTSum ≫ (TB.map carrierSum ≫ (TB.map μ ≫ τB)) :=
    hchosenPost.trans hchosenAssoc
  exact hnat.trans (hmapCollapsePre.trans
    (hcarrierPre.trans (hmapExpandPre.trans hchosenPath.symm)))

/-- Evaluation of the pullback-then-direct-comparison path at the common chosen path. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_lhs_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((Scheme.Modules.pullback (extensionMap R B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R K D E) ≪≫
        lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
          R B K D E).hom =
      (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          R B K (D + E)).hom ≫
        ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
            (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso.hom ≫
          (AffineTilde.tildeTensorIso B
            (extendedInverseIdeal R B K D)
            (extendedInverseIdeal R B K E)).inv) :=
  (lineBundleAddIso_pullback_viaExtendScalars_lhs_to_mid_hom R B K D E).trans
    (lineBundleAddIso_pullback_viaExtendScalars_mid_to_common_hom R B K D E)

/-- Evaluation of the chosen-comparison-then-raw-addition path at the same opaque middle path. -/
private theorem lineBundleAddIso_pullback_viaExtendScalars_rhs_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K (D + E) ≪≫
        extendedInverseIdealAddIso R B K D E).hom =
      (lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          R B K (D + E)).hom ≫
        ((_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).map
            (extendedInverseIdealTensorAddEquiv R B K D E).symm.toModuleIso.hom ≫
          (AffineTilde.tildeTensorIso B
            (extendedInverseIdeal R B K D)
            (extendedInverseIdeal R B K E)).inv) := by
  rw [Iso.trans_hom, extendedInverseIdealAddIso_hom]
  rfl

/-- The deterministic sum-to-tensor line-bundle isomorphism is natural along one flat-epimorphic
affine pullback/base-change leg, relative to the canonical affine tilde/extension-of-scalars
comparison.

The codomain is the tensor of the two raw extended inverse-ideal tilde sheaves.  Factoring this
comparison through factorwise pulled-back line bundles and the canonical pullback tensorator is
a separate coherence statement. -/
theorem lineBundleAddIso_pullback_viaExtendScalars
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R K D E) ≪≫
        lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
          R B K D E =
      lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K (D + E) ≪≫
        extendedInverseIdealAddIso R B K D E := by
  apply Iso.ext
  exact (lineBundleAddIso_pullback_viaExtendScalars_lhs_hom R B K D E).trans
    (lineBundleAddIso_pullback_viaExtendScalars_rhs_hom R B K D E).symm

end AffineDivisorLocalization.CommonExtension
end MazurTorsion.AlgebraicGeometry
