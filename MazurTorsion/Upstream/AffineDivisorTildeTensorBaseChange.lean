/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineModuleBaseChange
import MazurTorsion.Upstream.AffineDivisorTensorBaseChange
import MazurTorsion.Upstream.AffineTildeTensorPullbackCoherence

/-!
# Affine tilde base change for divisor tensor addition

The fixed tensor-addition comparison for affine divisor modules is transported through the
canonical affine comparison between pullback of a tilde sheaf and tilde of extension of scalars.
The resulting direct tensor comparison is identified with the canonical inverse pullback
tensorator followed by the two factorwise affine tilde comparisons.
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

/-- Cancel the inverse tail of an explicitly factored morphism after postcomposition. -/
private theorem comp_inv_hom_cancel
    {C : Type*} [Category C] {A B C₁ D E : C}
    (d : A ⟶ E) (x : A ⟶ B) (y : B ⟶ C₁) (z : C₁ ⟶ D)
    (e : E ≅ D) (hd : d = x ≫ ((y ≫ z) ≫ e.inv)) :
    d ≫ e.hom = (x ≫ y) ≫ z := by
  have hpost := congrArg (fun q ↦ q ≫ e.hom) hd
  have htail₁ : ((y ≫ z) ≫ e.inv) ≫ e.hom =
      (y ≫ z) ≫ (e.inv ≫ e.hom) := Category.assoc _ _ _
  have htail₂ : (y ≫ z) ≫ (e.inv ≫ e.hom) = (y ≫ z) ≫ 𝟙 _ :=
    congrArg (fun q ↦ (y ≫ z) ≫ q) e.inv_hom_id
  have htail₃ : (y ≫ z) ≫ 𝟙 _ = y ≫ z := Category.comp_id _
  have htail := htail₁.trans (htail₂.trans htail₃)
  have houter₁ : (x ≫ ((y ≫ z) ≫ e.inv)) ≫ e.hom =
      x ≫ (((y ≫ z) ≫ e.inv) ≫ e.hom) := Category.assoc _ _ _
  have houter₂ : x ≫ (((y ≫ z) ≫ e.inv) ≫ e.hom) = x ≫ (y ≫ z) :=
    congrArg (fun q ↦ x ≫ q) htail
  have houter₃ : x ≫ (y ≫ z) = (x ≫ y) ≫ z := (Category.assoc _ _ _).symm
  exact hpost.trans (houter₁.trans (houter₂.trans houter₃))

/-- Precomposition carries a two-step factorization to the corresponding associated path. -/
private theorem comp_eq_comp_comp_of_eq
    {C : Type*} [Category C] {A B D E : C}
    (x : A ⟶ B) (f : B ⟶ E) (g : B ⟶ D) (h : D ⟶ E)
    (hfg : f = g ≫ h) :
    x ≫ f = (x ≫ g) ≫ h := by
  have hpre : x ≫ f = x ≫ (g ≫ h) :=
    congrArg (fun q ↦ x ≫ q) hfg
  exact hpre.trans (Category.assoc x g h).symm

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

/-- The carrier bridge on Mathlib's bundled extension-of-scalars generator. -/
private lemma extendScalarsCarrierEquiv_apply_changeOfRings_tmul
    (R B M N : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N]
    [Algebra R B]
    (e : B ⊗[R] M ≃ₗ[B] N) (b : B) (m : M) :
    extendScalarsCarrierEquiv R B M N e
        (b ⊗ₜ[R, algebraMap R B] m) = e (b ⊗ₜ[R] m) := by
  letI : IsScalarTower R B
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eB : ((ModuleCat.restrictScalars (algebraMap R B)).obj
      (ModuleCat.of B B)) ≃ₗ[B] B := LinearEquiv.refl B B
  let eM : ModuleCat.of R M ≃ₗ[R] M := LinearEquiv.refl R M
  change ((TensorProduct.AlgebraTensorModule.congr
      eB eM).trans e)
      (b ⊗ₜ[R, algebraMap R B] m) = e (b ⊗ₜ[R] m)
  change e (TensorProduct.AlgebraTensorModule.congr eB eM
    (b ⊗ₜ[R, algebraMap R B] m)) = e (b ⊗ₜ[R] m)
  have hcongr :
      TensorProduct.AlgebraTensorModule.congr eB eM
          (b ⊗ₜ[R, algebraMap R B] m) = eB b ⊗ₜ[R] eM m :=
    TensorProduct.AlgebraTensorModule.congr_tmul eB eM b m
  have hb : eB b = b := rfl
  have hm : eM m = m := rfl
  have hpure : eB b ⊗ₜ[R] eM m = b ⊗ₜ[R] m :=
    congrArg₂ (fun x y ↦ x ⊗ₜ[R] y) hb hm
  exact congrArg e (hcongr.trans hpure)

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

/-- The carrier bridge for a distributed tensor extension is the extension-of-scalars
cotensorator followed by the tensor of the two carrier bridges. -/
private theorem extendScalarsCarrierEquiv_tensor
    (R B M N P Q : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module B P]
    [AddCommGroup Q] [Module B Q]
    [Algebra R B]
    (eM : B ⊗[R] M ≃ₗ[B] P) (eN : B ⊗[R] N ≃ₗ[B] Q) :
    let ES := ModuleCat.extendScalars (algebraMap R B)
    let MR := ModuleCat.of R M
    let NR := ModuleCat.of R N
    let qM := (extendScalarsCarrierEquiv R B M P eM).toModuleIso.hom
    let qN := (extendScalarsCarrierEquiv R B N Q eN).toModuleIso.hom
    (extendScalarsCarrierEquiv R B (M ⊗[R] N) (P ⊗[B] Q)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).trans
          (TensorProduct.congr eM eN))).toModuleIso.hom =
      Functor.OplaxMonoidal.δ ES MR NR ≫ (qM ⊗ₘ qN) := by
  dsimp only
  let ES := ModuleCat.extendScalars (algebraMap R B)
  let MR := ModuleCat.of R M
  let NR := ModuleCat.of R N
  let qT := (extendScalarsCarrierEquiv R B (M ⊗[R] N) (P ⊗[B] Q)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).trans
      (TensorProduct.congr eM eN))).toModuleIso.hom
  let qM := (extendScalarsCarrierEquiv R B M P eM).toModuleIso.hom
  let qN := (extendScalarsCarrierEquiv R B N Q eN).toModuleIso.hom
  let δ := Functor.OplaxMonoidal.δ ES MR NR
  let L := qT
  let G := δ ≫ (qM ⊗ₘ qN)
  change L = G
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  change L ((1 : B) ⊗ₜ[R, algebraMap R B] z) =
    G ((1 : B) ⊗ₜ[R, algebraMap R B] z)
  induction z using TensorProduct.induction_on with
  | zero =>
      have hz :
          ((1 : B) ⊗ₜ[R, algebraMap R B] (0 : M ⊗[R] N) :
            ES.obj (MR ⊗ NR)) = 0 :=
        @TensorProduct.tmul_zero R _ B (M ⊗[R] N) _ _
          (Module.compHom B (algebraMap R B)) _ (1 : B)
      have hLzero : L (0 : ES.obj (MR ⊗ NR)) = 0 := L.hom.map_zero
      have hGzero : G (0 : ES.obj (MR ⊗ NR)) = 0 := G.hom.map_zero
      exact (congrArg L.hom hz).trans
        (hLzero.trans (hGzero.symm.trans (congrArg G.hom hz.symm)))
  | tmul m n =>
      let z : ES.obj (MR ⊗ NR) :=
        (1 : B) ⊗ₜ[R, algebraMap R B] (m ⊗ₜ[R] n)
      let zm : ES.obj MR := (1 : B) ⊗ₜ[R, algebraMap R B] m
      let zn : ES.obj NR := (1 : B) ⊗ₜ[R, algebraMap R B] n
      let rm : B ⊗[R] M := (1 : B) ⊗ₜ[R] m
      let rn : B ⊗[R] N := (1 : B) ⊗ₜ[R] n
      let rt : B ⊗[R] (M ⊗[R] N) := (1 : B) ⊗ₜ[R] (m ⊗ₜ[R] n)
      let target : P ⊗[B] Q := eM rm ⊗ₜ[B] eN rn
      have hqT := extendScalarsCarrierEquiv_apply_changeOfRings_tmul R B
        (M ⊗[R] N) (P ⊗[B] Q)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).trans
          (TensorProduct.congr eM eN)) (1 : B) (m ⊗ₜ[R] n)
      change L z =
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).trans
          (TensorProduct.congr eM eN)) rt at hqT
      have heval :
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).trans
            (TensorProduct.congr eM eN)) rt = target := by
        dsimp only [rt, target, rm, rn]
        rw [LinearEquiv.trans_apply,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          TensorProduct.congr_tmul]
      have hleft : L z = target := hqT.trans heval
      have hδ := ModuleCat.extendScalars_δ_tmul
        (algebraMap R B) MR NR m n
      change δ z = zm ⊗ₜ[B] zn at hδ
      have hpair := ModuleCat.MonoidalCategory.tensorHom_tmul qM qN zm zn
      change (qM ⊗ₘ qN) (zm ⊗ₜ[B] zn) = qM zm ⊗ₜ[B] qN zn at hpair
      have hqM := extendScalarsCarrierEquiv_apply_changeOfRings_tmul
        R B M P eM (1 : B) m
      change qM zm = eM rm at hqM
      have hqN := extendScalarsCarrierEquiv_apply_changeOfRings_tmul
        R B N Q eN (1 : B) n
      change qN zn = eN rn at hqN
      have hright₁ := congrArg (qM ⊗ₘ qN).hom hδ
      have hright₂ := hright₁.trans hpair
      have hright₃ : qM zm ⊗ₜ[B] qN zn = target :=
        congrArg₂ (fun a b ↦ a ⊗ₜ[B] b) hqM hqN
      have hright : G z = target := hright₂.trans hright₃
      exact hleft.trans hright.symm
  | add x y hx hy =>
      have ha :
          ((1 : B) ⊗ₜ[R, algebraMap R B] (x + y) : ES.obj (MR ⊗ NR)) =
            ((1 : B) ⊗ₜ[R, algebraMap R B] x) +
              ((1 : B) ⊗ₜ[R, algebraMap R B] y) :=
        @TensorProduct.tmul_add R _ B (M ⊗[R] N) _ _
          (Module.compHom B (algebraMap R B)) _ (1 : B) x y
      have hLadd : L (((1 : B) ⊗ₜ[R, algebraMap R B] x) +
            ((1 : B) ⊗ₜ[R, algebraMap R B] y)) =
          L ((1 : B) ⊗ₜ[R, algebraMap R B] x) +
            L ((1 : B) ⊗ₜ[R, algebraMap R B] y) :=
        L.hom.map_add _ _
      have hGadd : G (((1 : B) ⊗ₜ[R, algebraMap R B] x) +
            ((1 : B) ⊗ₜ[R, algebraMap R B] y)) =
          G ((1 : B) ⊗ₜ[R, algebraMap R B] x) +
            G ((1 : B) ⊗ₜ[R, algebraMap R B] y) :=
        G.hom.map_add _ _
      exact (congrArg L.hom ha).trans
        (hLadd.trans ((congrArg₂ (fun a b ↦ a + b) hx hy).trans
          (hGadd.symm.trans (congrArg G.hom ha.symm))))

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

Its hom is factored through the canonical pullback cotensorator and the two factorwise affine
comparisons by
`lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_eq_factorwise`. -/
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

/-- Cancelling the final inverse tilde-tensor comparison exposes the direct affine
extension-of-scalars carrier path. -/
private theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_post_tildeTensor
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let MD := AffineDedekind.lineBundleModule R K D
    let ME := AffineDedekind.lineBundleModule R K E
    let MR := ModuleCat.of R MD
    let ER := ModuleCat.of R ME
    let ID := extendedInverseIdeal R B K D
    let IE := extendedInverseIdeal R B K E
    let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
    let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
    let A := Scheme.Modules.tildePullbackIsoExtendScalars
      (CommRingCat.ofHom (algebraMap R B))
    let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
    let qT := (extendScalarsCarrierEquiv R B (MD ⊗[R] ME) (ID ⊗[B] IE)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R B MD ME).trans
        (TensorProduct.congr eD eE))).toModuleIso.hom
    let τR := AffineTilde.tildeTensorIso R MD ME
    let τB := AffineTilde.tildeTensorIso B ID IE
    (lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
        R B K D E).hom ≫ τB.hom =
      (PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)) ≫ TB.map qT := by
  dsimp only
  let PB := Scheme.Modules.pullback (extensionMap R B)
  let MD := AffineDedekind.lineBundleModule R K D
  let ME := AffineDedekind.lineBundleModule R K E
  let MR := ModuleCat.of R MD
  let ER := ModuleCat.of R ME
  let ID := extendedInverseIdeal R B K D
  let IE := extendedInverseIdeal R B K E
  let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
  let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
  let A := Scheme.Modules.tildePullbackIsoExtendScalars
    (CommRingCat.ofHom (algebraMap R B))
  let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
  let qT := (extendScalarsCarrierEquiv R B (MD ⊗[R] ME) (ID ⊗[B] IE)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R B MD ME).trans
      (TensorProduct.congr eD eE))).toModuleIso.hom
  let τR := AffineTilde.tildeTensorIso R MD ME
  let τB := AffineTilde.tildeTensorIso B ID IE
  let direct :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E
  have hdirect :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_normalized
      R B K D E
  change direct.hom = PB.map τR.hom ≫
    ((A.hom.app (MR ⊗ ER) ≫ TB.map qT) ≫ τB.inv) at hdirect
  exact comp_inv_hom_cancel direct.hom (PB.map τR.hom)
    (A.hom.app (MR ⊗ ER)) (TB.map qT) τB hdirect

/-- Mapping the distributed carrier factorization through affine tilde gives the carrier half
of the direct tensor comparison path. -/
private theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_mapped_carrier_path
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let ES := ModuleCat.extendScalars (algebraMap R B)
    let MD := AffineDedekind.lineBundleModule R K D
    let ME := AffineDedekind.lineBundleModule R K E
    let MR := ModuleCat.of R MD
    let ER := ModuleCat.of R ME
    let ID := extendedInverseIdeal R B K D
    let IE := extendedInverseIdeal R B K E
    let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
    let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
    let A := Scheme.Modules.tildePullbackIsoExtendScalars
      (CommRingCat.ofHom (algebraMap R B))
    let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
    let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
    let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
    let qT := (extendScalarsCarrierEquiv R B (MD ⊗[R] ME) (ID ⊗[B] IE)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R B MD ME).trans
        (TensorProduct.congr eD eE))).toModuleIso.hom
    let δES := Functor.OplaxMonoidal.δ ES MR ER
    let τR := AffineTilde.tildeTensorIso R MD ME
    (PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)) ≫ TB.map qT =
      ((PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)) ≫ TB.map δES) ≫
        TB.map (qD ⊗ₘ qE) := by
  dsimp only
  let PB := Scheme.Modules.pullback (extensionMap R B)
  let ES := ModuleCat.extendScalars (algebraMap R B)
  let MD := AffineDedekind.lineBundleModule R K D
  let ME := AffineDedekind.lineBundleModule R K E
  let MR := ModuleCat.of R MD
  let ER := ModuleCat.of R ME
  let ID := extendedInverseIdeal R B K D
  let IE := extendedInverseIdeal R B K E
  let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
  let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
  let A := Scheme.Modules.tildePullbackIsoExtendScalars
    (CommRingCat.ofHom (algebraMap R B))
  let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
  let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
  let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
  let qT := (extendScalarsCarrierEquiv R B (MD ⊗[R] ME) (ID ⊗[B] IE)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R B MD ME).trans
      (TensorProduct.congr eD eE))).toModuleIso.hom
  let δES := Functor.OplaxMonoidal.δ ES MR ER
  let τR := AffineTilde.tildeTensorIso R MD ME
  let X := PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)
  let qPair := qD ⊗ₘ qE
  have hcarrier := extendScalarsCarrierEquiv_tensor R B MD ME ID IE eD eE
  dsimp only at hcarrier
  change qT = δES ≫ qPair at hcarrier
  have hcarrierMap : TB.map qT = TB.map δES ≫ TB.map qPair := by
    rw [hcarrier]
    exact TB.map_comp δES qPair
  exact comp_eq_comp_comp_of_eq X (TB.map qT) (TB.map δES)
    (TB.map qPair) hcarrierMap

/-- The generic affine tilde/base-change coherence square remains equal after postcomposition
by the mapped tensor of the two divisor carrier maps. -/
private theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_generic_coherence_post
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let φ := CommRingCat.ofHom (algebraMap R B)
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let ES := ModuleCat.extendScalars (algebraMap R B)
    let MD := AffineDedekind.lineBundleModule R K D
    let ME := AffineDedekind.lineBundleModule R K E
    let MR := ModuleCat.of R MD
    let ER := ModuleCat.of R ME
    let ID := extendedInverseIdeal R B K D
    let IE := extendedInverseIdeal R B K E
    let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
    let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
    let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
    let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
    let δES := Functor.OplaxMonoidal.δ ES MR ER
    let τR := AffineTilde.tildeTensorIso R MD ME
    let τES := AffineTilde.tildeTensorIso B (ES.obj MR) (ES.obj ER)
    let aD := A.hom.app MR
    let aE := A.hom.app ER
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
    let δPB := Functor.OplaxMonoidal.δ PB
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) MR)
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) ER)
    ((PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)) ≫ TB.map δES) ≫
        TB.map (qD ⊗ₘ qE) =
      ((δPB ≫ (aD ⊗ₘ aE)) ≫ τES.hom) ≫ TB.map (qD ⊗ₘ qE) := by
  dsimp only
  let φ := CommRingCat.ofHom (algebraMap R B)
  let PB := Scheme.Modules.pullback (extensionMap R B)
  let ES := ModuleCat.extendScalars (algebraMap R B)
  let MD := AffineDedekind.lineBundleModule R K D
  let ME := AffineDedekind.lineBundleModule R K E
  let MR := ModuleCat.of R MD
  let ER := ModuleCat.of R ME
  let ID := extendedInverseIdeal R B K D
  let IE := extendedInverseIdeal R B K E
  let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
  let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
  let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
  let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
  let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
  let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
  let δES := Functor.OplaxMonoidal.δ ES MR ER
  let τR := AffineTilde.tildeTensorIso R MD ME
  let τES := AffineTilde.tildeTensorIso B (ES.obj MR) (ES.obj ER)
  let aD := A.hom.app MR
  let aE := A.hom.app ER
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
  let δPB := Functor.OplaxMonoidal.δ PB
    (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) MR)
    (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) ER)
  let X := PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)
  let qPair := qD ⊗ₘ qE
  let H := δPB ≫ (aD ⊗ₘ aE)
  have hcoherence :=
    AffineTilde.tildePullbackIsoExtendScalars_tensor_hom φ MR ER
  dsimp only at hcoherence
  change X ≫ TB.map δES = H ≫ τES.hom at hcoherence
  exact congrArg (fun q ↦ q ≫ TB.map qPair) hcoherence

/-- The distributed carrier path for the direct comparison is the generic affine
tilde/base-change coherence path, postcomposed by the tensor of the two carrier maps. -/
private theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_carrier_coherence
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let φ := CommRingCat.ofHom (algebraMap R B)
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let ES := ModuleCat.extendScalars (algebraMap R B)
    let MD := AffineDedekind.lineBundleModule R K D
    let ME := AffineDedekind.lineBundleModule R K E
    let MR := ModuleCat.of R MD
    let ER := ModuleCat.of R ME
    let ID := extendedInverseIdeal R B K D
    let IE := extendedInverseIdeal R B K E
    let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
    let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
    let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
    let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
    let qT := (extendScalarsCarrierEquiv R B (MD ⊗[R] ME) (ID ⊗[B] IE)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R B MD ME).trans
        (TensorProduct.congr eD eE))).toModuleIso.hom
    let τR := AffineTilde.tildeTensorIso R MD ME
    let τES := AffineTilde.tildeTensorIso B (ES.obj MR) (ES.obj ER)
    let aD := A.hom.app MR
    let aE := A.hom.app ER
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
    let δPB := Functor.OplaxMonoidal.δ PB
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) MR)
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) ER)
    (PB.map τR.hom ≫ A.hom.app (MR ⊗ ER)) ≫ TB.map qT =
      ((δPB ≫ (aD ⊗ₘ aE)) ≫ τES.hom) ≫ TB.map (qD ⊗ₘ qE) := by
  dsimp only
  have hcarrierPath :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_mapped_carrier_path
      R B K D E
  dsimp only at hcarrierPath
  have hcoherencePost :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_generic_coherence_post
      R B K D E
  dsimp only at hcoherencePost
  exact hcarrierPath.trans hcoherencePost

/-- Naturality of the affine tilde tensor comparison converts the generic factorwise carrier
path into the tensor of the two chosen single-factor divisor comparisons. -/
private theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_factorwise_naturality
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let φ := CommRingCat.ofHom (algebraMap R B)
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let ES := ModuleCat.extendScalars (algebraMap R B)
    let MD := AffineDedekind.lineBundleModule R K D
    let ME := AffineDedekind.lineBundleModule R K E
    let MR := ModuleCat.of R MD
    let ER := ModuleCat.of R ME
    let ID := extendedInverseIdeal R B K D
    let IE := extendedInverseIdeal R B K E
    let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
    let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
    let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
    let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
    let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
    let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
    let τES := AffineTilde.tildeTensorIso B (ES.obj MR) (ES.obj ER)
    let τB := AffineTilde.tildeTensorIso B ID IE
    let aD := A.hom.app MR
    let aE := A.hom.app ER
    let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
    let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
    let δPB := Functor.OplaxMonoidal.δ PB
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) MR)
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) ER)
    ((δPB ≫ (aD ⊗ₘ aE)) ≫ τES.hom) ≫ TB.map (qD ⊗ₘ qE) =
      (δPB ≫ (cD.hom ⊗ₘ cE.hom)) ≫ τB.hom := by
  dsimp only
  let φ := CommRingCat.ofHom (algebraMap R B)
  let PB := Scheme.Modules.pullback (extensionMap R B)
  let ES := ModuleCat.extendScalars (algebraMap R B)
  let MD := AffineDedekind.lineBundleModule R K D
  let ME := AffineDedekind.lineBundleModule R K E
  let MR := ModuleCat.of R MD
  let ER := ModuleCat.of R ME
  let ID := extendedInverseIdeal R B K D
  let IE := extendedInverseIdeal R B K E
  let eD := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D
  let eE := lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E
  let A := Scheme.Modules.tildePullbackIsoExtendScalars φ
  let TB := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
  let qD := (extendScalarsCarrierEquiv R B MD ID eD).toModuleIso.hom
  let qE := (extendScalarsCarrierEquiv R B ME IE eE).toModuleIso.hom
  let τES := AffineTilde.tildeTensorIso B (ES.obj MR) (ES.obj ER)
  let τB := AffineTilde.tildeTensorIso B ID IE
  let aD := A.hom.app MR
  let aE := A.hom.app ER
  let tD := TB.map qD
  let tE := TB.map qE
  let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
  let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
  let δPB := Functor.OplaxMonoidal.δ PB
    (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) MR)
    (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) ER)
  let qPair := qD ⊗ₘ qE
  let tPair := tD ⊗ₘ tE
  let aPair := aD ⊗ₘ aE
  let H := δPB ≫ aPair
  have hτnat := AffineTilde.tildeTensorIso_hom_naturality B qD qE
  change tPair ≫ τB.hom = τES.hom ≫ TB.map qPair at hτnat
  have hcD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars_hom R B K D
  change cD.hom = aD ≫ tD at hcD
  have hcE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars_hom R B K E
  change cE.hom = aE ≫ tE at hcE
  have hnatPath : (H ≫ τES.hom) ≫ TB.map qPair =
      (H ≫ tPair) ≫ τB.hom := by
    have h₁ : (H ≫ τES.hom) ≫ TB.map qPair =
        H ≫ (τES.hom ≫ TB.map qPair) := Category.assoc _ _ _
    have h₂ : H ≫ (τES.hom ≫ TB.map qPair) =
        H ≫ (tPair ≫ τB.hom) :=
      congrArg (fun q ↦ H ≫ q) hτnat.symm
    have h₃ : H ≫ (tPair ≫ τB.hom) =
        (H ≫ tPair) ≫ τB.hom := (Category.assoc _ _ _).symm
    exact h₁.trans (h₂.trans h₃)
  have htensor := MonoidalCategory.tensorHom_comp_tensorHom aD aE tD tE
  change aPair ≫ tPair = ((aD ≫ tD) ⊗ₘ (aE ≫ tE)) at htensor
  have hcompCore : H ≫ tPair =
      δPB ≫ ((aD ≫ tD) ⊗ₘ (aE ≫ tE)) := by
    have h₁ : (δPB ≫ aPair) ≫ tPair = δPB ≫ (aPair ≫ tPair) :=
      Category.assoc _ _ _
    have h₂ : δPB ≫ (aPair ≫ tPair) =
        δPB ≫ ((aD ≫ tD) ⊗ₘ (aE ≫ tE)) :=
      congrArg (fun q ↦ δPB ≫ q) htensor
    exact h₁.trans h₂
  have hcompPath : (H ≫ tPair) ≫ τB.hom =
      (δPB ≫ ((aD ≫ tD) ⊗ₘ (aE ≫ tE))) ≫ τB.hom :=
    congrArg (fun q ↦ q ≫ τB.hom) hcompCore
  have hfactor : ((aD ≫ tD) ⊗ₘ (aE ≫ tE)) =
      (cD.hom ⊗ₘ cE.hom) :=
    congrArg₂ (fun q r ↦ q ⊗ₘ r) hcD.symm hcE.symm
  have hfactorPath :
      (δPB ≫ ((aD ≫ tD) ⊗ₘ (aE ≫ tE))) ≫ τB.hom =
        (δPB ≫ (cD.hom ⊗ₘ cE.hom)) ≫ τB.hom :=
    congrArg (fun q ↦ (δPB ≫ q) ≫ τB.hom) hfactor
  exact hnatPath.trans (hcompPath.trans hfactorPath)

/-- The direct affine tensor/base-change comparison is the canonical pullback cotensorator
followed by the two factorwise affine tilde/base-change comparisons. -/
theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_eq_factorwise
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let LD := (AffineDedekind.lineBundle R K D).obj
    let LE := (AffineDedekind.lineBundle R K E).obj
    let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
    let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
    (lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E).hom =
      Functor.OplaxMonoidal.δ PB LD LE ≫ (cD.hom ⊗ₘ cE.hom) := by
  dsimp only
  let PB := Scheme.Modules.pullback (extensionMap R B)
  let ID := extendedInverseIdeal R B K D
  let IE := extendedInverseIdeal R B K E
  let τB := AffineTilde.tildeTensorIso B ID IE
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
  have hdirectPost :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_post_tildeTensor
      R B K D E
  dsimp only at hdirectPost
  have hcarrierCoherence :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_carrier_coherence
      R B K D E
  dsimp only at hcarrierCoherence
  have hfactorwiseNaturality :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_factorwise_naturality
      R B K D E
  dsimp only at hfactorwiseNaturality
  apply (cancel_mono τB.hom).1
  exact hdirectPost.trans
    (hcarrierCoherence.trans hfactorwiseNaturality)

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

The codomain is the tensor of the two raw extended inverse-ideal tilde sheaves.  Its comparison
through factorwise pulled-back line bundles and the canonical pullback tensorator is supplied by
`lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_eq_factorwise`.  No
cross-chart or descent-data compatibility is asserted here. -/
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
