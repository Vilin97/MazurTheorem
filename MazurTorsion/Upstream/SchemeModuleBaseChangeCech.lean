/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.SchemeModuleAffinePullbackSections
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechPushforward
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechCochains
import MazurTorsion.Upstream.SchemeModuleBaseCechHZeroComparison
import MazurTorsion.Upstream.SchemeModuleBaseCechHOneComparison
import MazurTorsion.Upstream.SchemeModulePullbackCoherent
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Cech assembly for low-degree coherent-cohomology base change

This file assembles the canonical affine pullback map on sections termwise over a finite affine
Cech cover.  It identifies the scalar-extended base-linear Cech complex with the Cech complex of
the pulled-back module and proves that flat scalar extension commutes with its homology.  The
native degree-zero and degree-one Cech comparisons then give genuine cohomology base change.

The design boundary is intentionally narrow: the checked field-extension facade
`fieldExtensionLowDegreeBaseChange` packages exactly degrees zero and one over spectra of fields.
General proper-flat base change and semicontinuity are not asserted here.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry ChangeOfRings TensorProduct

namespace ModuleCat

theorem restrictScalarsSource_isScalarTower
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ModuleCat.{u} S) :
    letI : Algebra R S := φ.toAlgebra
    IsScalarTower R S ((restrictScalars φ).obj N) := by
  letI : Algebra R S := φ.toAlgebra
  exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

noncomputable def restrictScalarsSourceIso
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ModuleCat.{u} S) :
    ModuleCat.of S ((restrictScalars φ).obj N) ≅ N := by
  exact Iso.refl N

@[simp]
theorem restrictScalarsSourceIso_hom_apply
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ModuleCat.{u} S) (x : (restrictScalars φ).obj N) :
    (restrictScalarsSourceIso φ N).hom x = x := by
  rfl

theorem restrictScalarsSourceIso_naturality_apply
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{u} S} (q : M ⟶ N)
    (x : (restrictScalars φ).obj M) :
    q ((restrictScalarsSourceIso φ M).hom x) =
      (restrictScalarsSourceIso φ N).hom ((restrictScalars φ).map q x) := by
  rfl

noncomputable def extendScalarsTensorIso
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : ModuleCat.{u} R) :
    letI : Algebra R S := φ.toAlgebra
    (extendScalars φ).obj M ≅ ModuleCat.of S (S ⊗[R] M) :=
  by
    letI : Algebra R S := φ.toAlgebra
    exact Iso.refl _

noncomputable def extendScalarsTensorMap
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{u} R} (q : M ⟶ N) :
    letI : Algebra R S := φ.toAlgebra
    ModuleCat.of S (S ⊗[R] M) ⟶ ModuleCat.of S (S ⊗[R] N) :=
  by
    letI : Algebra R S := φ.toAlgebra
    exact (extendScalarsTensorIso φ M).inv ≫
      (extendScalars φ).map q ≫ (extendScalarsTensorIso φ N).hom

@[simp]
theorem extendScalarsTensorMap_tmul
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{u} R} (q : M ⟶ N) (s : S) (x : M) :
    letI : Algebra R S := φ.toAlgebra
    extendScalarsTensorMap φ q (s ⊗ₜ[R] x) = s ⊗ₜ[R] q x := by
  letI : Algebra R S := φ.toAlgebra
  exact ExtendScalars.map_tmul φ q s x

@[reassoc]
theorem extendScalars_map_comp_tensorIso_hom
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{u} R} (q : M ⟶ N) :
    letI : Algebra R S := φ.toAlgebra
    (extendScalars φ).map q ≫ (extendScalarsTensorIso φ N).hom =
      (extendScalarsTensorIso φ M).hom ≫ extendScalarsTensorMap φ q := by
  letI : Algebra R S := φ.toAlgebra
  simp [extendScalarsTensorMap]

noncomputable def extendScalarsComplexComponentIso
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (extendScalars φ).obj (C.X n) ≅
      (((extendScalars φ).mapHomologicalComplex (.up ℕ)).obj C).X n :=
  Iso.refl _

@[reassoc]
theorem extendScalarsComplexComponentIso_hom_naturality
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ) :
    (extendScalarsComplexComponentIso φ C i).hom ≫
        (((extendScalars φ).mapHomologicalComplex (.up ℕ)).obj C).d i j =
      (extendScalars φ).map (C.d i j) ≫
        (extendScalarsComplexComponentIso φ C j).hom := by
  rfl

noncomputable def restrictScalarsComplexComponentIso
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (D : CochainComplex (ModuleCat.{u} S) ℕ) (n : ℕ) :
    (restrictScalars φ).obj (D.X n) ≅
      (((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D).X n :=
  Iso.refl _

def restrictScalarsComplexComponentLinearMap
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {C : CochainComplex (ModuleCat.{u} R) ℕ}
    {D : CochainComplex (ModuleCat.{u} S) ℕ}
    (f : C ⟶ ((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) : C.X n →ₗ[R] (restrictScalars φ).obj (D.X n) :=
  (f.f n ≫ (restrictScalarsComplexComponentIso φ D n).inv).hom

@[simp]
theorem restrictScalarsComplexComponentLinearMap_apply
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {C : CochainComplex (ModuleCat.{u} R) ℕ}
    {D : CochainComplex (ModuleCat.{u} S) ℕ}
    (f : C ⟶ ((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D)
    (n : ℕ) (x : C.X n) :
    restrictScalarsComplexComponentLinearMap φ f n x =
      (restrictScalarsComplexComponentIso φ D n).inv (f.f n x) :=
  rfl

theorem restrictScalarsComplexComponentIso_hom_naturality
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (D : CochainComplex (ModuleCat.{u} S) ℕ) (i j : ℕ) :
    (restrictScalarsComplexComponentIso φ D i).hom ≫
        (((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D).d i j =
      (restrictScalars φ).map (D.d i j) ≫
        (restrictScalarsComplexComponentIso φ D j).hom := by
  rfl

theorem restrictScalarsComplexComponentIso_inv_naturality
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (D : CochainComplex (ModuleCat.{u} S) ℕ) (i j : ℕ) :
    (((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D).d i j ≫
        (restrictScalarsComplexComponentIso φ D j).inv =
      (restrictScalarsComplexComponentIso φ D i).inv ≫
        (restrictScalars φ).map (D.d i j) := by
  rw [← cancel_epi (restrictScalarsComplexComponentIso φ D i).hom]
  rw [← Category.assoc]
  rw [restrictScalarsComplexComponentIso_hom_naturality]
  simp

theorem restrictScalarsComplexComponentLinearMap_comm_apply
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {C : CochainComplex (ModuleCat.{u} R) ℕ}
    {D : CochainComplex (ModuleCat.{u} S) ℕ}
    (f : C ⟶ ((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D)
    (i j : ℕ) (x : C.X i) :
    ((restrictScalars φ).map (D.d i j))
        (restrictScalarsComplexComponentLinearMap φ f i x) =
      restrictScalarsComplexComponentLinearMap φ f j (C.d i j x) := by
  change ((f.f i ≫ (restrictScalarsComplexComponentIso φ D i).inv) ≫
      (restrictScalars φ).map (D.d i j)) x =
    (C.d i j ≫ f.f j ≫
      (restrictScalarsComplexComponentIso φ D j).inv) x
  rw [Category.assoc,
    ← restrictScalarsComplexComponentIso_inv_naturality]
  rw [← Category.assoc, f.comm, Category.assoc]

noncomputable def homologicalComplexExtendScalarsIsoOfIsBaseChange
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (D : CochainComplex (ModuleCat.{u} S) ℕ)
    (f : C ⟶ ((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D)
    (hf : ∀ n,
      letI : Algebra R S := φ.toAlgebra
      letI : IsScalarTower R S ((restrictScalars φ).obj (D.X n)) :=
        restrictScalarsSource_isScalarTower φ (D.X n)
      IsBaseChange S (restrictScalarsComplexComponentLinearMap φ f n)) :
    ((extendScalars φ).mapHomologicalComplex (.up ℕ)).obj C ≅ D := by
  letI : Algebra R S := φ.toAlgebra
  let baseComponent (n : ℕ) :
      (((extendScalars φ).mapHomologicalComplex (.up ℕ)).obj C).X n ≅
        ModuleCat.of S ((restrictScalars φ).obj (D.X n)) := by
    letI : IsScalarTower R S ((restrictScalars φ).obj (D.X n)) :=
      restrictScalarsSource_isScalarTower φ (D.X n)
    exact (extendScalarsComplexComponentIso φ C n).symm ≪≫
      extendScalarsTensorIso φ (C.X n) ≪≫
      (hf n).equiv.toModuleIso
  let component (n : ℕ) :
      (((extendScalars φ).mapHomologicalComplex (.up ℕ)).obj C).X n ≅
        D.X n :=
    baseComponent n ≪≫ restrictScalarsSourceIso φ (D.X n)
  exact HomologicalComplex.Hom.isoOfComponents component (by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst j
    letI : IsScalarTower R S ((restrictScalars φ).obj (D.X i)) :=
      restrictScalarsSource_isScalarTower φ (D.X i)
    letI : IsScalarTower R S ((restrictScalars φ).obj (D.X (i + 1))) :=
      restrictScalarsSource_isScalarTower φ (D.X (i + 1))
    rw [← cancel_epi (extendScalarsComplexComponentIso φ C i).hom]
    simp only [component, baseComponent, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [extendScalarsComplexComponentIso_hom_naturality_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [extendScalars_map_comp_tensorIso_hom_assoc]
    rw [cancel_epi (extendScalarsTensorIso φ (C.X i)).hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | tmul s x =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      have hi : ((hf i).equiv.toModuleIso.hom).hom (s ⊗ₜ[R] x) =
          s • restrictScalarsComplexComponentLinearMap φ f i x :=
        (hf i).equiv_tmul s x
      have hd : (extendScalarsTensorMap φ (C.d i (i + 1))).hom (s ⊗ₜ[R] x) =
          s ⊗ₜ[R] C.d i (i + 1) x :=
        extendScalarsTensorMap_tmul φ (C.d i (i + 1)) s x
      have hj : ((hf (i + 1)).equiv.toModuleIso.hom).hom
          (s ⊗ₜ[R] C.d i (i + 1) x) =
            s • restrictScalarsComplexComponentLinearMap φ f (i + 1)
              (C.d i (i + 1) x) :=
        (hf (i + 1)).equiv_tmul s (C.d i (i + 1) x)
      rw [hi, hd, hj]
      simp only [map_smul]
      rw [restrictScalarsSourceIso_naturality_apply]
      exact congrArg (fun y ↦ s •
        (restrictScalarsSourceIso φ (D.X (i + 1))).hom y)
        (restrictScalarsComplexComponentLinearMap_comm_apply
          φ f i (i + 1) x))

/-- Flat extension of scalars commutes with the homology of a cochain complex. -/
noncomputable def homologyExtendScalarsIso
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat)
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (((extendScalars φ).mapHomologicalComplex (.up ℕ)).obj C).homology n ≅
      (extendScalars φ).obj (C.homology n) := by
  letI : PreservesFiniteLimits (extendScalars φ) :=
    preservesFiniteLimits_extendScalars_of_flat hφ
  exact (C.sc n).mapHomologyIso (extendScalars φ)

/-- A componentwise base-change map of cochain complexes induces base change on
homology when the ring map is flat. -/
noncomputable def homologyExtendScalarsIsoOfIsBaseChange
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.Flat)
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (D : CochainComplex (ModuleCat.{u} S) ℕ)
    (f : C ⟶ ((restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D)
    (hf : ∀ n,
      letI : Algebra R S := φ.toAlgebra
      letI : IsScalarTower R S ((restrictScalars φ).obj (D.X n)) :=
        restrictScalarsSource_isScalarTower φ (D.X n)
      IsBaseChange S (restrictScalarsComplexComponentLinearMap φ f n))
    (n : ℕ) :
    (extendScalars φ).obj (C.homology n) ≅ D.homology n :=
  (homologyExtendScalarsIso φ hφ C n).symm ≪≫
    HomologicalComplex.homologyMapIso
      (homologicalComplexExtendScalarsIsoOfIsBaseChange φ C D f hf) n

/-- Restriction of scalars commutes with products. -/
noncomputable def restrictScalarsPiIso
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {I : Type u} (P : I → ModuleCat.{u} S) :
    (restrictScalars φ).obj (∏ᶜ P) ≅ ∏ᶜ fun i ↦ (restrictScalars φ).obj (P i) := by
  let eDiagram : Discrete.functor P ⋙ restrictScalars φ ≅
      Discrete.functor (fun i ↦ (restrictScalars φ).obj (P i)) :=
    Discrete.natIso fun _ ↦ Iso.refl _
  exact preservesLimitIso (restrictScalars φ) (Discrete.functor P) ≪≫
    HasLimit.isoOfNatIso eDiagram

@[reassoc]
theorem restrictScalarsPiIso_hom_π
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {I : Type u} (P : I → ModuleCat.{u} S) (i : I) :
    (restrictScalarsPiIso φ P).hom ≫
        Pi.π (fun j ↦ (restrictScalars φ).obj (P j)) i =
      (restrictScalars φ).map (Pi.π P i) := by
  dsimp [restrictScalarsPiIso]
  rw [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  change (preservesLimitIso (restrictScalars φ) (Discrete.functor P)).hom ≫
      limit.π (Discrete.functor P ⋙ restrictScalars φ) (Discrete.mk i) =
    (restrictScalars φ).map (Pi.π P i)
  exact preservesLimitIso_hom_π (restrictScalars φ) (Discrete.functor P)
    (Discrete.mk i)

end ModuleCat

namespace AlgebraicGeometry.Scheme.Modules

/-- Top sections after restriction to an open are the original sections on that open,
with their base-module structure retained. -/
noncomputable def baseSectionsRestrictIso
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules) (U : X.Opens) :
    baseSections (U.ι ≫ f) (M.restrict U.ι) ≅
      (baseModulePresheaf f M).obj (op U) :=
  baseModulePresheafRestrictAppIso f U.ι M (⊤ : U.toScheme.Opens) ≪≫
    ((baseModulePresheaf f M).mapIso (eqToIso U.ι_image_top).op).symm

@[simp]
theorem baseSectionsRestrictIso_inv_apply
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules) (U : X.Opens)
    (x : (baseModulePresheaf f M).obj (op U)) :
    (baseSectionsRestrictIso f M U).inv x =
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op x) := by
  rfl

theorem pullbackSquare_pushforwardTopSection_apply
    {P X : Scheme.{u}} (fst : P ⟶ X) (U : X.Opens) (N : P.Modules)
    (y : Γ(N, fst ⁻¹ᵁ U)) :
    N.presheaf.map
          (eqToHom
            (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
              (isPullback_morphismRestrict fst U)
              (⊤ : U.toScheme.Opens))).op
        (((pushforward fst).obj N).presheaf.map
          (eqToHom U.ι_image_top).op y) =
      pushforwardTopSection (fst ∣_ U)
        (N.restrict (fst ⁻¹ᵁ U).ι)
        ((N.restrictAppIso (fst ⁻¹ᵁ U).ι
          (⊤ : (fst ⁻¹ᵁ U).toScheme.Opens)).inv
          (N.presheaf.map
            (eqToHom (fst ⁻¹ᵁ U).ι_image_top).op y)) := by
  dsimp only [pushforwardTopSection]
  rw [restrictAppIso_inv_map_apply]
  change N.presheaf.map _ (N.presheaf.map _ y) =
    N.presheaf.map _ (N.presheaf.map _ y)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom
    (N.presheaf.congr_map (Subsingleton.elim _ _)) _

/-- The local pullback module on an open has the same base-linear top sections as the
restriction of the global pullback module to the inverse-image open. -/
noncomputable def pullbackBaseSectionsRestrictIso
    {P X Y : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (M : X.Modules) (U : X.Opens) :
    baseSections ((fst ⁻¹ᵁ U).ι ≫ snd)
        ((pullback (fst ∣_ U)).obj (M.restrict U.ι)) ≅
      (baseModulePresheaf snd ((pullback fst).obj M)).obj
        (op (fst ⁻¹ᵁ U)) :=
  ((baseModulePresheafFunctor ((fst ⁻¹ᵁ U).ι ≫ snd)).mapIso
      ((openPullbackSquareExplicitIsoT fst U).app M)).app
        (op (⊤ : (fst ⁻¹ᵁ U).toScheme.Opens)) ≪≫
    baseSectionsRestrictIso snd ((pullback fst).obj M) (fst ⁻¹ᵁ U)

/-- The base-linear pullback unit bundled as a morphism from base sections to
restricted-scalars base sections. -/
noncomputable def pullbackUnitBaseLinearHom
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules) :
    (baseModulePresheaf f M).obj (op (⊤ : X.Opens)) ⟶
      (ModuleCat.restrictScalars g.appTop.hom).obj
        ((baseModulePresheaf snd ((pullback fst).obj M)).obj
          (op (⊤ : P.Opens))) := by
  let N := (pullback fst).obj M
  letI : Module Γ(Z, ⊤) (baseSections snd N) :=
    baseSectionsFurtherBaseModule snd g N
  exact ModuleCat.ofHom
    (X := (baseModulePresheaf f M).obj (op (⊤ : X.Opens)))
    (Y := (ModuleCat.restrictScalars g.appTop.hom).obj
      ((baseModulePresheaf snd N).obj (op (⊤ : P.Opens))))
    (pullbackUnitBaseLinearMap fst snd f g h M)

noncomputable def baseModulePresheafCompRestrictScalarsAppIso
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) (W : P.Opensᵒᵖ) :
    (baseModulePresheaf (snd ≫ g) N).obj W ≅
      (ModuleCat.restrictScalars g.appTop.hom).obj
        ((baseModulePresheaf snd N).obj W) := by
  let e : (baseModulePresheaf (snd ≫ g) N).obj W ≃ₗ[Γ(Z, ⊤)]
      (ModuleCat.restrictScalars g.appTop.hom).obj
        ((baseModulePresheaf snd N).obj W) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e.toModuleIso

@[reassoc]
theorem baseModulePresheafCompRestrictScalarsAppIso_hom_naturality
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {W W' : P.Opensᵒᵖ} (a : W ⟶ W') :
    (baseModulePresheaf (snd ≫ g) N).map a ≫
        (baseModulePresheafCompRestrictScalarsAppIso snd g N W').hom =
      (baseModulePresheafCompRestrictScalarsAppIso snd g N W).hom ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          ((baseModulePresheaf snd N).map a) := by
  ext x
  rfl

@[reassoc]
theorem baseModulePresheafCongr_compRestrictScalars_naturality
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    {q : P ⟶ Z} (h : q = snd ≫ g) (N : P.Modules)
    {W W' : P.Opensᵒᵖ} (a : W ⟶ W') :
    (baseModulePresheaf q N).map a ≫
          eqToHom (congrArg
            (fun r : P ⟶ Z ↦ (baseModulePresheaf r N).obj W') h) ≫
          (baseModulePresheafCompRestrictScalarsAppIso snd g N W').hom =
      eqToHom (congrArg
          (fun r : P ⟶ Z ↦ (baseModulePresheaf r N).obj W) h) ≫
        (baseModulePresheafCompRestrictScalarsAppIso snd g N W).hom ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          ((baseModulePresheaf snd N).map a) := by
  subst q
  simpa using
    baseModulePresheafCompRestrictScalarsAppIso_hom_naturality
      snd g N a

@[simp]
theorem baseModulePresheafCongr_compRestrictScalars_apply
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    {q : P ⟶ Z} (h : q = snd ≫ g) (N : P.Modules)
    (W : P.Opensᵒᵖ) (x : (baseModulePresheaf q N).obj W) :
    (eqToHom (congrArg
          (fun r : P ⟶ Z ↦ (baseModulePresheaf r N).obj W) h) ≫
        (baseModulePresheafCompRestrictScalarsAppIso snd g N W).hom) x = x := by
  subst q
  rfl

noncomputable def baseModulePresheafFunctorObjIso
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules) :
    (baseModulePresheafFunctor f).obj M ≅ baseModulePresheaf f M :=
  eqToIso (baseModulePresheafFunctor_obj f M)

@[simp]
theorem baseModulePresheafFunctorObjIso_hom_app
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    (W : X.Opensᵒᵖ) :
    (baseModulePresheafFunctorObjIso f M).hom.app W = 𝟙 _ := by
  rfl

@[simp]
theorem baseModulePresheafFunctorObjIso_inv_app
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    (W : X.Opensᵒᵖ) :
    (baseModulePresheafFunctorObjIso f M).inv.app W = 𝟙 _ := by
  rfl

noncomputable def baseCechComplexFunctorObjIso
    {X Z : Scheme.{u}} (f : X ⟶ Z) {i : Type u} (U : i → X.Opens)
    (M : X.Modules) :
    (baseCechComplexFunctor f U).obj M ≅ baseCechComplex f M U :=
  Iso.refl _

theorem baseCechComplexFunctorX_eq
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {i : Type u} (U : i → X.Opens) (n : ℕ) :
    ((baseCechComplexFunctor f U).obj M).X n =
      ∏ᶜ fun j : Fin (n + 1) → i ↦
        ((baseModulePresheafFunctor f).obj M).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k))) := by
  change (((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj
      ((baseModulePresheafFunctor f).obj M)).X n) = _
  exact FormalCoproduct.cochainComplexFunctor_obj_X _ _ _

theorem baseCechComplexX_eq
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {i : Type u} (U : i → X.Opens) (n : ℕ) :
    (baseCechComplex f M U).X n =
      ∏ᶜ fun j : Fin (n + 1) → i ↦ baseCechFactor f M U n j := by
  change (((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (baseModulePresheaf f M)).X n) = _
  exact FormalCoproduct.cochainComplexFunctor_obj_X _ _ _

noncomputable def baseCechProjection
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {i : Type u} (U : i → X.Opens) (n : ℕ)
    (j : Fin (n + 1) → i) :
    (baseCechComplex f M U).X n ⟶ baseCechFactor f M U n j :=
  eqToHom (baseCechComplexX_eq f M U n) ≫
    Pi.π (fun k ↦ baseCechFactor f M U n k) j

noncomputable def baseCechComplexFunctorProjection
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {i : Type u} (U : i → X.Opens) (n : ℕ)
    (j : Fin (n + 1) → i) :
    ((baseCechComplexFunctor f U).obj M).X n ⟶
      ((baseModulePresheafFunctor f).obj M).obj
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k))) := by
  exact (baseCechComplexFunctorObjIso f U M).hom.f n ≫
    baseCechProjection f M U n j ≫
    (baseModulePresheafFunctorObjIso f M).inv.app
      (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k)))

@[simp]
theorem baseCechComplexFunctorObjIso_hom_f
    {X Z : Scheme.{u}} (f : X ⟶ Z) {i : Type u} (U : i → X.Opens)
    (M : X.Modules) (n : ℕ) :
    (baseCechComplexFunctorObjIso f U M).hom.f n = 𝟙 _ := by
  rfl

@[simp]
theorem baseCechComplexFunctorObjIso_inv_f
    {X Z : Scheme.{u}} (f : X ⟶ Z) {i : Type u} (U : i → X.Opens)
    (M : X.Modules) (n : ℕ) :
    (baseCechComplexFunctorObjIso f U M).inv.f n = 𝟙 _ := by
  rfl

@[reassoc]
theorem baseCechComplexFunctorObjIso_hom_projection
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {i : Type u} (U : i → X.Opens) (n : ℕ)
    (j : Fin (n + 1) → i) :
    (baseCechComplexFunctorObjIso f U M).hom.f n ≫
        baseCechProjection f M U n j =
      baseCechComplexFunctorProjection f M U n j ≫
        (baseModulePresheafFunctorObjIso f M).hom.app
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k))) := by
  simp [baseCechComplexFunctorProjection]

@[reassoc]
theorem baseCechComplexFunctorObjIso_inv_projection
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {i : Type u} (U : i → X.Opens) (n : ℕ)
    (j : Fin (n + 1) → i) :
    (baseCechComplexFunctorObjIso f U M).inv.f n ≫
        baseCechComplexFunctorProjection f M U n j =
      baseCechProjection f M U n j ≫
        (baseModulePresheafFunctorObjIso f M).inv.app
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k))) := by
  simp [baseCechComplexFunctorProjection]

noncomputable def baseCechFactorCompRestrictScalarsIso
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    baseCechFactor (snd ≫ g) N V n i ≅
      (ModuleCat.restrictScalars g.appTop.hom).obj
        (baseCechFactor snd N V n i) :=
  baseModulePresheafCompRestrictScalarsAppIso snd g N _

noncomputable def baseCechComponentIsoPi
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex f M U).X n ≅
      ∏ᶜ fun i : Fin (n + 1) → ι ↦ baseCechFactor f M U n i :=
  eqToIso (baseCechComplexX_eq f M U n)

@[reassoc]
theorem baseCechComponentIsoPi_hom_projection
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechComponentIsoPi f M U n).hom ≫
        Pi.π (fun j ↦ baseCechFactor f M U n j) i =
      baseCechProjection f M U n i := by
  rfl

@[reassoc]
theorem baseCechComponentIsoPi_inv_projection
    {X Z : Scheme.{u}} (f : X ⟶ Z) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechComponentIsoPi f M U n).inv ≫
        baseCechProjection f M U n i =
      Pi.π (fun j ↦ baseCechFactor f M U n j) i := by
  simp [baseCechComponentIsoPi, baseCechProjection]

noncomputable def baseCechCompModuleIso
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ) :
    (baseCechComplex (snd ≫ g) N V).X n ≅
      (ModuleCat.restrictScalars g.appTop.hom).obj
        ((baseCechComplex snd N V).X n) := by
  exact baseCechComponentIsoPi (snd ≫ g) N V n ≪≫
    Pi.mapIso (fun i ↦
      baseCechFactorCompRestrictScalarsIso snd g N V n i) ≪≫
    (ModuleCat.restrictScalarsPiIso g.appTop.hom
      (fun i : Fin (n + 1) → ι ↦ baseCechFactor snd N V n i)).symm ≪≫
    (ModuleCat.restrictScalars g.appTop.hom).mapIso
      (baseCechComponentIsoPi snd N V n).symm

noncomputable def baseCechCompComponentIso
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ) :
    (baseCechComplex (snd ≫ g) N V).X n ≅
      (((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex (.up ℕ)).obj
        (baseCechComplex snd N V)).X n :=
  baseCechCompModuleIso snd g N V n ≪≫
    ModuleCat.restrictScalarsComplexComponentIso g.appTop.hom
      (baseCechComplex snd N V) n

noncomputable def baseCechCompTargetProjection
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex (.up ℕ)).obj
          (baseCechComplex snd N V)).X n ⟶
      (ModuleCat.restrictScalars g.appTop.hom).obj
        (baseCechFactor snd N V n i) :=
  (ModuleCat.restrictScalarsComplexComponentIso g.appTop.hom
      (baseCechComplex snd N V) n).inv ≫
    (ModuleCat.restrictScalars g.appTop.hom).map
      (baseCechProjection snd N V n i)

@[reassoc]
theorem baseCechCompModuleIso_hom_projection
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechCompModuleIso snd g N V n).hom ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          (baseCechProjection snd N V n i) =
      baseCechProjection (snd ≫ g) N V n i ≫
        (baseCechFactorCompRestrictScalarsIso snd g N V n i).hom := by
  let restrictedProj :
      (∏ᶜ fun j : Fin (n + 1) → ι ↦
        (ModuleCat.restrictScalars g.appTop.hom).obj
          (baseCechFactor snd N V n j)) ⟶
        (ModuleCat.restrictScalars g.appTop.hom).obj
          (baseCechFactor snd N V n i) :=
    Pi.π _ i
  have hRestrict :
      (ModuleCat.restrictScalarsPiIso g.appTop.hom
        (fun j : Fin (n + 1) → ι ↦ baseCechFactor snd N V n j)).hom ≫
          restrictedProj =
        (ModuleCat.restrictScalars g.appTop.hom).map
          (Pi.π (fun j : Fin (n + 1) → ι ↦
            baseCechFactor snd N V n j) i) := by
    exact ModuleCat.restrictScalarsPiIso_hom_π g.appTop.hom
      (fun j : Fin (n + 1) → ι ↦ baseCechFactor snd N V n j) i
  have hMap :
      (Pi.mapIso (fun j : Fin (n + 1) → ι ↦
        baseCechFactorCompRestrictScalarsIso snd g N V n j)).hom ≫
          restrictedProj =
        Pi.π (fun j : Fin (n + 1) → ι ↦
          baseCechFactor (snd ≫ g) N V n j) i ≫
          (baseCechFactorCompRestrictScalarsIso snd g N V n i).hom := by
    exact Pi.mapIso_hom_π
      (fun j ↦ baseCechFactorCompRestrictScalarsIso snd g N V n j) i
  dsimp [baseCechCompModuleIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Category.assoc]
  rw [← Functor.map_comp]
  rw [baseCechComponentIsoPi_inv_projection]
  rw [← hRestrict, Iso.inv_hom_id_assoc]
  rw [hMap]
  simp only [← Category.assoc]
  rw [baseCechComponentIsoPi_hom_projection]

@[reassoc]
theorem baseCechCompComponentIso_hom_π
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechCompComponentIso snd g N V n).hom ≫
        baseCechCompTargetProjection snd g N V n i =
      baseCechProjection (snd ≫ g) N V n i ≫
        (baseCechFactorCompRestrictScalarsIso snd g N V n i).hom := by
  dsimp [baseCechCompComponentIso, baseCechCompTargetProjection]
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact baseCechCompModuleIso_hom_projection snd g N V n i

private theorem baseCechCompModuleIso_coface_naturality
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    (baseCechCompModuleIso snd g N V n).hom ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          (baseCechCoface snd N V n k) =
      baseCechCoface (snd ≫ g) N V n k ≫
        (baseCechCompModuleIso snd g N V (n + 1)).hom := by
  let F := ModuleCat.restrictScalars g.appTop.hom
  let sourceLow := (baseCechComplex (snd ≫ g) N V).X n
  let sourceHigh := (baseCechComplex (snd ≫ g) N V).X (n + 1)
  let targetLow := (baseCechComplex snd N V).X n
  let targetHigh := (baseCechComplex snd N V).X (n + 1)
  let eLow : sourceLow ≅ F.obj targetLow :=
    baseCechCompModuleIso snd g N V n
  let eHigh : sourceHigh ≅ F.obj targetHigh :=
    baseCechCompModuleIso snd g N V (n + 1)
  let sourceCoface : sourceLow ⟶ sourceHigh :=
    baseCechCoface (snd ≫ g) N V n k
  let targetCoface : F.obj targetLow ⟶ F.obj targetHigh :=
    F.map (baseCechCoface snd N V n k)
  let eHighPi : F.obj targetHigh ≅
      ∏ᶜ fun i : Fin (n + 2) → ι ↦
        F.obj (baseCechFactor snd N V (n + 1) i) :=
    ModuleCat.restrictScalarsPiIso g.appTop.hom
      (fun i : Fin (n + 2) → ι ↦ baseCechFactor snd N V (n + 1) i)
  change eLow.hom ≫ targetCoface = sourceCoface ≫ eHigh.hom
  apply (cancel_mono eHighPi.hom).1
  apply Pi.hom_ext
  intro a
  change Fin (n + 2) → ι at a
  let sourceLowProj : sourceLow ⟶
      baseCechFactor (snd ≫ g) N V n
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
    baseCechProjection (snd ≫ g) N V n
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  let sourceHighProj : sourceHigh ⟶
      baseCechFactor (snd ≫ g) N V (n + 1) a :=
    baseCechProjection (snd ≫ g) N V (n + 1) a
  let targetLowProj : F.obj targetLow ⟶
      F.obj (baseCechFactor snd N V n
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)) :=
    F.map (baseCechProjection snd N V n
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  let targetHighProj : F.obj targetHigh ⟶
      F.obj (baseCechFactor snd N V (n + 1) a) :=
    F.map (baseCechProjection snd N V (n + 1) a)
  let sourceMap :
      baseCechFactor (snd ≫ g) N V n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) ⟶
        baseCechFactor (snd ≫ g) N V (n + 1) a :=
    (baseModulePresheaf (snd ≫ g) N).map
      (((FormalCoproduct.mk _ V).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a).op
  let targetMap :
      F.obj (baseCechFactor snd N V n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)) ⟶
        F.obj (baseCechFactor snd N V (n + 1) a) :=
    F.map ((baseModulePresheaf snd N).map
      (((FormalCoproduct.mk _ V).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a).op)
  let factorLow :
      baseCechFactor (snd ≫ g) N V n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≅
        F.obj (baseCechFactor snd N V n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)) :=
    baseCechFactorCompRestrictScalarsIso snd g N V n
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  let factorHigh : baseCechFactor (snd ≫ g) N V (n + 1) a ≅
      F.obj (baseCechFactor snd N V (n + 1) a) :=
    baseCechFactorCompRestrictScalarsIso snd g N V (n + 1) a
  have hTargetCoface :
      targetCoface ≫ targetHighProj = targetLowProj ≫ targetMap := by
    simp only [targetCoface, targetHighProj, targetLowProj, targetMap,
      ← Functor.map_comp]
    exact congrArg F.map (baseCechCoface_comp_π snd N V n k a)
  have hSourceCoface :
      sourceCoface ≫ sourceHighProj = sourceLowProj ≫ sourceMap :=
    baseCechCoface_comp_π (snd ≫ g) N V n k a
  have hLowIso : eLow.hom ≫ targetLowProj =
      sourceLowProj ≫ factorLow.hom :=
    baseCechCompModuleIso_hom_projection snd g N V n
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  have hHighIso : eHigh.hom ≫ targetHighProj =
      sourceHighProj ≫ factorHigh.hom :=
    baseCechCompModuleIso_hom_projection snd g N V (n + 1) a
  have hFactor : sourceMap ≫ factorHigh.hom =
      factorLow.hom ≫ targetMap :=
    baseModulePresheafCompRestrictScalarsAppIso_hom_naturality
      snd g N _
  have hHighPi : eHighPi.hom ≫
        Pi.π (fun i : Fin (n + 2) → ι ↦
          F.obj (baseCechFactor snd N V (n + 1) i)) a =
      targetHighProj := by
    exact ModuleCat.restrictScalarsPiIso_hom_π g.appTop.hom
      (fun i : Fin (n + 2) → ι ↦ baseCechFactor snd N V (n + 1) i) a
  simp only [Category.assoc]
  rw [hHighPi]
  calc
    eLow.hom ≫ targetCoface ≫ targetHighProj =
        sourceLowProj ≫ (factorLow.hom ≫ targetMap) := by
      rw [hTargetCoface, ← Category.assoc, hLowIso, Category.assoc]
    _ = sourceLowProj ≫ (sourceMap ≫ factorHigh.hom) := by rw [hFactor]
    _ = sourceCoface ≫ sourceHighProj ≫ factorHigh.hom := by
      rw [← Category.assoc, ← hSourceCoface, Category.assoc]
    _ = sourceCoface ≫ eHigh.hom ≫ targetHighProj := by
      rw [← hHighIso]

private theorem baseCechCompModuleIso_differential_naturality
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ) :
    (baseCechCompModuleIso snd g N V n).hom ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          ((baseCechComplex snd N V).d n (n + 1)) =
      (baseCechComplex (snd ≫ g) N V).d n (n + 1) ≫
        (baseCechCompModuleIso snd g N V (n + 1)).hom := by
  rw [baseCechComplex_d_eq_sum_cofaces,
    baseCechComplex_d_eq_sum_cofaces]
  simp only [Functor.map_sum, Functor.map_zsmul]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    (baseCechCompModuleIso_coface_naturality snd g N V n k)

private theorem baseCechCompComponentIso_differential_naturality
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ) :
    (baseCechCompComponentIso snd g N V n).hom ≫
        (((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj (baseCechComplex snd N V)).d n (n + 1) =
      (baseCechComplex (snd ≫ g) N V).d n (n + 1) ≫
        (baseCechCompComponentIso snd g N V (n + 1)).hom := by
  dsimp [baseCechCompComponentIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [ModuleCat.restrictScalarsComplexComponentIso_hom_naturality]
  rw [← Category.assoc,
    baseCechCompModuleIso_differential_naturality, Category.assoc]

/-- The base-linear Cech complex over a composite morphism is the
restriction of scalars of the Cech complex over the intermediate base. -/
noncomputable def baseCechComplexCompRestrictScalarsIso
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) :
    baseCechComplex (snd ≫ g) N V ≅
      ((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex (.up ℕ)).obj
        (baseCechComplex snd N V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ baseCechCompComponentIso snd g N V n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      exact baseCechCompComponentIso_differential_naturality snd g N V i)

@[simp]
theorem baseCechComplexCompRestrictScalarsIso_hom_f
    {P Y Z : Scheme.{u}} (snd : P ⟶ Y) (g : Y ⟶ Z)
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ) :
    (baseCechComplexCompRestrictScalarsIso snd g N V).hom.f n =
      (baseCechCompComponentIso snd g N V n).hom :=
  rfl

/-- The canonical map from a base-linear Cech complex to the restricted-scalars
Cech complex after pullback around a commutative square. -/
noncomputable def baseChangeCechHom
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    baseCechComplex f M U ⟶
      ((ModuleCat.restrictScalars g.appTop.hom).mapHomologicalComplex (.up ℕ)).obj
        (baseCechComplex snd ((pullback fst).obj M)
          (fun i ↦ fst ⁻¹ᵁ U i)) :=
  (baseCechComplexFunctorObjIso f U M).inv ≫
    (baseCechComplexFunctor f U).map
      ((pullbackPushforwardAdjunction fst).unit.app M) ≫
    (baseCechComplexFunctorObjIso f U
      ((pushforward fst).obj ((pullback fst).obj M))).hom ≫
    (baseCechComplexPushforwardIso fst f ((pullback fst).obj M) U).inv ≫
    eqToHom (congrArg
      (fun q : P ⟶ Z ↦ baseCechComplex q ((pullback fst).obj M)
        (fun i ↦ fst ⁻¹ᵁ U i)) h) ≫
    (baseCechComplexCompRestrictScalarsIso snd g ((pullback fst).obj M)
      (fun i ↦ fst ⁻¹ᵁ U i)).hom

@[reassoc]
theorem baseCechComplexFunctor_map_f_π
    {X Z : Scheme.{u}} (f : X ⟶ Z) {M N : X.Modules} (q : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).I) :
    ((baseCechComplexFunctor f U).map q).f n ≫
        Pi.π (fun j => ((baseModulePresheafFunctor f).obj N).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i =
      Pi.π (fun j => ((baseModulePresheafFunctor f).obj M).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i ≫
        ((baseModulePresheafFunctor f).map q).app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj i)) := by
  change Limits.Pi.map (fun j => ((baseModulePresheafFunctor f).map q).app
      (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
        (SimplexCategory.mk n))).obj j))) ≫ _ = _
  exact Pi.map_π _ i

@[reassoc]
theorem baseCechComplexFunctor_map_f_π_factor
    {X Z : Scheme.{u}} (f : X ⟶ Z) {M N : X.Modules} (q : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    ((baseCechComplexFunctor f U).map q).f n ≫
        baseCechComplexFunctorProjection f N U n i =
      baseCechComplexFunctorProjection f M U n i ≫
        ((baseModulePresheafFunctor f).map q).app
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) := by
  change Limits.Pi.map (fun j ↦
      ((baseModulePresheafFunctor f).map q).app
        (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
          (SimplexCategory.mk n))).obj j))) ≫ _ = _
  exact Pi.map_π _ i

@[reassoc]
theorem baseCechComplexFunctor_map_pullbackUnit_f_π
    {P X Z : Scheme.{u}} (fst : P ⟶ X) (f : X ⟶ Z)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    ((baseCechComplexFunctor f U).map
        ((pullbackPushforwardAdjunction fst).unit.app M)).f n ≫
      baseCechComplexFunctorProjection f
        ((pushforward fst).obj ((pullback fst).obj M)) U n i =
    baseCechComplexFunctorProjection f M U n i ≫
      ((baseModulePresheafFunctor f).map
        ((pullbackPushforwardAdjunction fst).unit.app M)).app
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) := by
  exact baseCechComplexFunctor_map_f_π_factor f
    ((pullbackPushforwardAdjunction fst).unit.app M) U n i

@[reassoc]
theorem baseCechComplexPushforwardIso_inv_f_π
    {P X Z : Scheme.{u}} (fst : P ⟶ X) (f : X ⟶ Z)
    (N : P.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechComplexPushforwardIso fst f N U).inv.f n ≫
        baseCechProjection (fst ≫ f) N (fun a ↦ fst ⁻¹ᵁ U a) n i =
      baseCechProjection f ((pushforward fst).obj N) U n i ≫
        (baseCechFactorPushforwardIso fst f N U n i).inv := by
  exact Pi.mapIso_inv_π
    (fun j ↦ baseCechFactorPushforwardIso fst f N U n j) i

@[reassoc]
theorem baseCechComplexCongr_f_π
    {P Z : Scheme.{u}} {q q' : P ⟶ Z} (h : q = q')
    (N : P.Modules) {ι : Type u} (V : ι → P.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (eqToHom (congrArg (fun r : P ⟶ Z ↦ baseCechComplex r N V) h)).f n ≫
        baseCechProjection q' N V n i =
      baseCechProjection q N V n i ≫
        eqToHom (congrArg
          (fun r : P ⟶ Z ↦ baseCechFactor r N V n i) h) := by
  subst q'
  simp

noncomputable def baseChangeCechFactorHom
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    baseCechFactor f M U n i ⟶
      (ModuleCat.restrictScalars g.appTop.hom).obj
        (baseCechFactor snd ((pullback fst).obj M)
          (fun a ↦ fst ⁻¹ᵁ U a) n i) :=
  (baseModulePresheafFunctorObjIso f M).inv.app
      (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) ≫
    ((baseModulePresheafFunctor f).map
      ((pullbackPushforwardAdjunction fst).unit.app M)).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) ≫
    (baseModulePresheafFunctorObjIso f
      ((pushforward fst).obj ((pullback fst).obj M))).hom.app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) ≫
    (baseCechFactorPushforwardIso fst f ((pullback fst).obj M) U n i).inv ≫
    eqToHom (congrArg
      (fun q : P ⟶ Z ↦ baseCechFactor q ((pullback fst).obj M)
        (fun a ↦ fst ⁻¹ᵁ U a) n i) h) ≫
    (baseCechFactorCompRestrictScalarsIso snd g ((pullback fst).obj M)
      (fun a ↦ fst ⁻¹ᵁ U a) n i).hom

theorem baseChangeCechHom_f_π
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseChangeCechHom fst snd f g h M U).f n ≫
        baseCechCompTargetProjection snd g ((pullback fst).obj M)
          (fun a ↦ fst ⁻¹ᵁ U a) n i =
      baseCechProjection f M U n i ≫
        baseChangeCechFactorHom fst snd f g h M U n i := by
  simp only [baseChangeCechHom, HomologicalComplex.comp_f, Category.assoc,
    baseCechComplexCompRestrictScalarsIso_hom_f]
  rw [baseCechCompComponentIso_hom_π,
    baseCechComplexCongr_f_π_assoc,
    baseCechComplexPushforwardIso_inv_f_π_assoc]
  · rw [baseCechComplexFunctorObjIso_hom_projection_assoc,
      baseCechComplexFunctor_map_pullbackUnit_f_π_assoc]
    simp only [← Category.assoc]
    rw [baseCechComplexFunctorObjIso_inv_projection]
    simp only [Category.assoc]
    simp only [baseChangeCechFactorHom,
      baseModulePresheafFunctorObjIso_hom_app,
      baseModulePresheafFunctorObjIso_inv_app]
  · exact h

/-- The affine-local model of the section pullback map over an open in the upper-right
corner of a Cartesian square. -/
noncomputable def baseChangeOpenAffineModel
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) (U : X.Opens) :
    (baseModulePresheaf f M).obj (op U) ⟶
      (ModuleCat.restrictScalars g.appTop.hom).obj
        ((baseModulePresheaf snd ((pullback fst).obj M)).obj
          (op (fst ⁻¹ᵁ U))) := by
  let fstU := fst ∣_ U
  let sndU := (fst ⁻¹ᵁ U).ι ≫ snd
  let fU := U.ι ≫ f
  let MU := M.restrict U.ι
  let NU := (pullback fstU).obj MU
  let hU : IsPullback fstU sndU fU g :=
    (isPullback_morphismRestrict fst U).paste_vert h
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let eSource := baseSectionsRestrictIso f M U
  let eTarget := pullbackBaseSectionsRestrictIso fst snd M U
  exact eSource.inv ≫
    pullbackUnitBaseLinearHom fstU sndU fU g hU.w MU ≫
    (ModuleCat.restrictScalars g.appTop.hom).map eTarget.hom

/-- On an affine open in the upper-right corner, the local model of the section map is
extension of scalars along the lower horizontal morphism. -/
theorem baseChangeOpenAffineModel_isBaseChange
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) [IsAffine U.toScheme] :
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
        ((ModuleCat.restrictScalars g.appTop.hom).obj
          ((baseModulePresheaf snd ((pullback fst).obj M)).obj
            (op (fst ⁻¹ᵁ U)))) :=
      ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom _
    IsBaseChange Γ(Y, ⊤) (baseChangeOpenAffineModel fst snd f g h M U).hom := by
  let fstU := fst ∣_ U
  let sndU := (fst ⁻¹ᵁ U).ι ≫ snd
  let fU := U.ι ≫ f
  let MU := M.restrict U.ι
  let NU := (pullback fstU).obj MU
  let hU : IsPullback fstU sndU fU g :=
    (isPullback_morphismRestrict fst U).paste_vert h
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let target := (baseModulePresheaf snd ((pullback fst).obj M)).obj
    (op (fst ⁻¹ᵁ U))
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
      ((ModuleCat.restrictScalars g.appTop.hom).obj target) :=
    ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom target
  letI : Module Γ(Z, ⊤) (baseSections sndU NU) :=
    baseSectionsFurtherBaseModule sndU g NU
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) (baseSections sndU NU) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hLocal : IsBaseChange Γ(Y, ⊤)
      (pullbackUnitBaseLinearMap fstU sndU fU g hU.w MU) :=
    pullbackUnitBaseLinearMap_isBaseChange_of_isPullback
      fstU sndU fU g hU MU
  let eSource := (baseSectionsRestrictIso f M U).toLinearEquiv
  let eTarget :=
    (pullbackBaseSectionsRestrictIso fst snd M U).toLinearEquiv.trans
      (ModuleCat.restrictScalarsSourceIso g.appTop.hom target).symm.toLinearEquiv
  have hSource : IsBaseChange Γ(Y, ⊤)
      ((pullbackUnitBaseLinearMap fstU sndU fU g hU.w MU).comp
        eSource.symm.toLinearMap) :=
    hLocal.comp_equiv eSource.symm _
  have hTarget := hSource.comp (IsBaseChange.ofEquiv eTarget)
  have hMap : (baseChangeOpenAffineModel fst snd f g h M U).hom =
      (eTarget.toLinearMap.restrictScalars Γ(Z, ⊤)).comp
        ((pullbackUnitBaseLinearMap fstU sndU fU g hU.w MU).comp
          eSource.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    simp only [baseChangeOpenAffineModel, eTarget, eSource,
      ModuleCat.comp_apply, LinearMap.comp_apply,
      ModuleCat.restrictScalars.map_apply]
    rfl
  rw [hMap]
  exact hTarget

noncomputable def baseChangeOpenHom
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules) (U : X.Opens) :
    (baseModulePresheaf f M).obj (op U) ⟶
      (ModuleCat.restrictScalars g.appTop.hom).obj
        ((baseModulePresheaf snd ((pullback fst).obj M)).obj
          (op (fst ⁻¹ᵁ U))) :=
  (baseModulePresheafFunctorObjIso f M).inv.app (op U) ≫
    ((baseModulePresheafFunctor f).map
      ((pullbackPushforwardAdjunction fst).unit.app M)).app (op U) ≫
    (baseModulePresheafFunctorObjIso f
      ((pushforward fst).obj ((pullback fst).obj M))).hom.app (op U) ≫
    (baseModulePresheafPushforwardAppIso fst f
      ((pullback fst).obj M) U).inv ≫
    eqToHom (congrArg
      (fun q : P ⟶ Z ↦ (baseModulePresheaf q ((pullback fst).obj M)).obj
        (op (fst ⁻¹ᵁ U))) h) ≫
    (baseModulePresheafCompRestrictScalarsAppIso snd g
      ((pullback fst).obj M) (op (fst ⁻¹ᵁ U))).hom

private noncomputable def topSectionAsBaseSection
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : baseSections f M := by
  exact x

private theorem localPullbackUnit_eq_pushforwardTopSection
    {P X : Scheme.{u}} (fst : P ⟶ X) (M : X.Modules) (U : X.Opens)
    (xLocal : Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) :
    (((((pullbackPushforwardAdjunction (fst ∣_ U)).unit.app
          (M.restrict U.ι)) ≫
        (pushforward (fst ∣_ U)).map
          ((openPullbackSquareExplicitIsoT fst U).hom.app M)).app
            (⊤ : U.toScheme.Opens)).hom) xLocal =
      (baseSectionsPushforwardTopIso (fst ∣_ U)
        (((pullback fst).obj M).restrict (fst ⁻¹ᵁ U).ι)).hom
        (topSectionAsBaseSection (fst ∣_ U)
          (((pullback fst).obj M).restrict (fst ⁻¹ᵁ U).ι)
          (((((openPullbackSquareExplicitIsoT fst U).hom.app M).app
            (⊤ : (fst ⁻¹ᵁ U).toScheme.Opens)).hom)
            (pullbackUnitTop (fst ∣_ U) (M.restrict U.ι) xLocal))) := by
  rw [baseSectionsPushforwardTopIso_hom_apply]
  let q := (openPullbackSquareExplicitIsoT fst U).hom.app M
  let htop :
      (Opens.map (fst ∣_ U).base).op.obj
          (op (⊤ : U.toScheme.Opens)) =
        op (⊤ : (fst ⁻¹ᵁ U).toScheme.Opens) := by
    simp
  let raw := ((pullbackPushforwardAdjunction (fst ∣_ U)).unit.app
      (M.restrict U.ι)).val.app (op (⊤ : U.toScheme.Opens)) xLocal
  let back : op (⊤ : (fst ⁻¹ᵁ U).toScheme.Opens) ⟶
      (Opens.map (fst ∣_ U).base).op.obj
        (op (⊤ : U.toScheme.Opens)) :=
    eqToHom htop.symm
  have hcancel :
      ((restrictFunctor U.ι ⋙ pullback (fst ∣_ U)).obj M).val.map back
        (pullbackUnitTop (fst ∣_ U) (M.restrict U.ι) xLocal) = raw := by
    rw [pullbackUnitTop_eq_unit_app_top]
    rw [show back = 𝟙 _ from Subsingleton.elim _ _]
    simp
    rfl
  have hq := PresheafOfModules.naturality_apply q.val back
    (pullbackUnitTop (fst ∣_ U) (M.restrict U.ι) xLocal)
  rw [hcancel] at hq
  dsimp only [q, raw, topSectionAsBaseSection] at hq ⊢
  simp only [Hom.comp_app, pushforward_map_app, pushforwardTopSection] at ⊢
  exact hq

theorem baseChangeOpenHom_eq_baseChangeOpenAffineModel
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) (U : X.Opens) :
    baseChangeOpenHom fst snd f g h.w M U =
      baseChangeOpenAffineModel fst snd f g h M U := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let N := (pullback fst).obj M
  let fstU := fst ∣_ U
  let MU := M.restrict U.ι
  let eRestr := baseSectionsRestrictIso snd N (fst ⁻¹ᵁ U)
  let ePush := baseSectionsPushforwardTopIso fstU
    (N.restrict (fst ⁻¹ᵁ U).ι)
  let pushTop :=
    (baseModulePresheaf (𝟙 U.toScheme)
      ((pushforward fstU).obj (N.restrict (fst ⁻¹ᵁ U).ι))).obj
        (op (⊤ : U.toScheme.Opens))
  let sourceLocal : Γ((restrictFunctor U.ι).obj M,
      (⊤ : U.toScheme.Opens)) :=
    (baseSectionsRestrictIso f M U).inv x
  have hn := restrict_pullbackPushforward_unit_naturality fst U M
  have hnTop := congrArg
    (fun q ↦ (q.app (⊤ : U.toScheme.Opens)).hom) hn
  have hnApply := congrArg (fun q ↦ q sourceLocal) hnTop
  let leftValue : pushTop :=
    (((((restrictFunctor U.ι).map
        ((pullbackPushforwardAdjunction fst).unit.app M)) ≫
      (restrictPushforwardIsoOfIsPullback fst (fst ∣_ U)
        (fst ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict fst U)).hom.app
          ((pullback fst).obj M)).app (⊤ : U.toScheme.Opens)).hom)
      sourceLocal
  let rightValue : pushTop :=
    (((((pullbackPushforwardAdjunction (fst ∣_ U)).unit.app
        ((restrictFunctor U.ι).obj M)) ≫
      (pushforward (fst ∣_ U)).map
        ((openPullbackSquareExplicitIsoT fst U).hom.app M)).app
          (⊤ : U.toScheme.Opens)).hom)
      sourceLocal
  have hnValues : leftValue = rightValue := hnApply
  let post (y : pushTop) :
      (baseModulePresheaf snd ((pullback fst).obj M)).obj
        (op (fst ⁻¹ᵁ U)) :=
    eRestr.hom (ePush.inv y)
  have hnPost : post leftValue = post rightValue := congrArg post hnValues
  have hLeft : (baseChangeOpenHom fst snd f g h.w M U).hom x =
      post leftValue := by
    let globalValue :
        (baseModulePresheaf snd ((pullback fst).obj M)).obj
          (op (fst ⁻¹ᵁ U)) :=
      ((pullbackPushforwardAdjunction fst).unit.app M).val.app (op U) x
    have hCanonical : (baseChangeOpenHom fst snd f g h.w M U).hom x =
        globalValue := by
      let a : (baseModulePresheaf f M).obj (op U) ⟶
          (baseModulePresheaf f ((pushforward fst).obj N)).obj (op U) :=
        (baseModulePresheafFunctorObjIso f M).inv.app (op U) ≫
          ((baseModulePresheafFunctor f).map
            ((pullbackPushforwardAdjunction fst).unit.app M)).app (op U) ≫
          (baseModulePresheafFunctorObjIso f
            ((pushforward fst).obj N)).hom.app (op U)
      let b := (baseModulePresheafPushforwardAppIso fst f N U).inv
      let c := eqToHom (congrArg
        (fun q : P ⟶ Z ↦ (baseModulePresheaf q N).obj
          (op (fst ⁻¹ᵁ U))) h.w)
      let d := (baseModulePresheafCompRestrictScalarsAppIso snd g N
        (op (fst ⁻¹ᵁ U))).hom
      let middleValue :
          (baseModulePresheaf snd N).obj (op (fst ⁻¹ᵁ U)) :=
        b (a x)
      change d (c (b (a x))) = globalValue
      have hcd : d (c (b (a x))) = middleValue := by
        simpa only [c, d, middleValue, ModuleCat.comp_apply] using
          baseModulePresheafCongr_compRestrictScalars_apply
            snd g h.w N (op (fst ⁻¹ᵁ U)) (b (a x))
      have hba : middleValue = globalValue := by
        dsimp only [middleValue, a, b, globalValue,
          baseModulePresheafPushforwardAppIso]
        rfl
      exact hcd.trans hba
    have hRestricted : post leftValue = globalValue := by
      let restrictedGlobal : baseSections fstU
          (N.restrict (fst ⁻¹ᵁ U).ι) :=
        eRestr.inv globalValue
      have hLeftValue : leftValue =
          ePush.hom restrictedGlobal := by
        rw [baseSectionsPushforwardTopIso_hom_apply]
        dsimp only [leftValue]
        simp only [Hom.comp_app, AddCommGrpCat.hom_comp,
          AddMonoidHom.comp_apply]
        rw [restrictPushforwardIsoOfIsPullback_hom_app_app_apply]
        let u := (pullbackPushforwardAdjunction fst).unit.app M
        let imageTop := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
        let hImage : imageTop = U := U.ι_image_top
        let a : op U ⟶ op imageTop := (eqToHom hImage).op
        have hSourceLocal : sourceLocal = M.val.map a x := by
          dsimp only [sourceLocal, a, hImage, imageTop,
            baseSectionsRestrictIso,
            baseModulePresheafRestrictAppIso]
          rfl
        have hu := PresheafOfModules.naturality_apply u.val a x
        have hu' :
            u.val.app (op imageTop) (M.val.map a x) =
              ((pullback fst ⋙ pushforward fst).obj M).val.map a
                (u.val.app (op U) x) := by
          simpa only [Functor.id_obj] using hu
        rw [hSourceLocal]
        have hRestrictMap :
            (((restrictFunctor U.ι).map u).app
              (⊤ : U.toScheme.Opens)).hom (M.val.map a x) =
              u.val.app (op imageTop) (M.val.map a x) := by
          rfl
        rw [hRestrictMap]
        rw [hu']
        dsimp only [restrictedGlobal, eRestr]
        rw [baseSectionsRestrictIso_inv_apply]
        dsimp only [globalValue]
        dsimp only [a, hImage, imageTop]
        exact pullbackSquare_pushforwardTopSection_apply fst U N
          (u.val.app (op U) x)
      dsimp only [post]
      calc
        eRestr.hom (ePush.inv leftValue) =
            eRestr.hom (ePush.inv (ePush.hom restrictedGlobal)) :=
          congrArg (fun z ↦ eRestr.hom (ePush.inv z)) hLeftValue
        _ = eRestr.hom restrictedGlobal :=
          congrArg (fun z ↦ eRestr.hom z)
            (ePush.hom_inv_id_apply restrictedGlobal)
        _ = eRestr.hom (eRestr.inv globalValue) := by rfl
        _ = globalValue := eRestr.inv_hom_id_apply globalValue
    exact hCanonical.trans hRestricted.symm
  have hRight : post rightValue =
      (baseChangeOpenAffineModel fst snd f g h M U).hom x := by
    let localMapped : baseSections fstU
        (N.restrict (fst ⁻¹ᵁ U).ι) :=
      topSectionAsBaseSection fstU (N.restrict (fst ⁻¹ᵁ U).ι)
        (((((openPullbackSquareExplicitIsoT fst U).hom.app M).app
          (⊤ : (fst ⁻¹ᵁ U).toScheme.Opens)).hom)
          (pullbackUnitTop fstU MU
            ((baseSectionsRestrictIso f M U).inv x)))
    change eRestr.hom (ePush.inv rightValue) =
      eRestr.hom localMapped
    refine congrArg (fun z ↦ eRestr.hom z) ?_
    have hRightValue : rightValue = ePush.hom localMapped := by
      let xLocal : Γ(MU, (⊤ : U.toScheme.Opens)) :=
        (baseSectionsRestrictIso f M U).inv x
      dsimp only [rightValue, localMapped, fstU, MU, N, xLocal]
      exact localPullbackUnit_eq_pushforwardTopSection fst M U xLocal
    exact (congrArg ePush.inv hRightValue).trans
      (ePush.hom_inv_id_apply localMapped)
  exact hLeft.trans (hnPost.trans hRight)

theorem baseChangeCechFactorHom_eq_baseChangeOpenHom
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    baseChangeCechFactorHom fst snd f g h M U n i =
      baseChangeOpenHom fst snd f g h M
          (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          (((baseModulePresheaf snd ((pullback fst).obj M)).mapIso
            (eqToIso (fst.preimage_cechIntersection U n i)).op).inv) := by
  let W : X.Opens := ∏ᶜ fun k : Fin (n + 1) ↦ U (i k)
  let V : P.Opens := ∏ᶜ fun k : Fin (n + 1) ↦ fst ⁻¹ᵁ U (i k)
  let N := (pullback fst).obj M
  let a : op (fst ⁻¹ᵁ W) ⟶ op V :=
    ((eqToIso (fst.preimage_cechIntersection U n i)).op).inv
  let initialMap : (baseModulePresheaf f M).obj (op W) ⟶
      (baseModulePresheaf (fst ≫ f) N).obj (op (fst ⁻¹ᵁ W)) :=
    (baseModulePresheafFunctorObjIso f M).inv.app (op W) ≫
      ((baseModulePresheafFunctor f).map
        ((pullbackPushforwardAdjunction fst).unit.app M)).app (op W) ≫
      (baseModulePresheafFunctorObjIso f
        ((pushforward fst).obj N)).hom.app (op W) ≫
      (baseModulePresheafPushforwardAppIso fst f N W).inv
  let tailFactor :
      (baseModulePresheaf (fst ≫ f) N).obj (op (fst ⁻¹ᵁ W)) ⟶
        (ModuleCat.restrictScalars g.appTop.hom).obj
          ((baseModulePresheaf snd N).obj (op V)) :=
    (baseModulePresheaf (fst ≫ f) N).map a ≫
      eqToHom (congrArg
        (fun q : P ⟶ Z ↦ (baseModulePresheaf q N).obj (op V)) h) ≫
      (baseModulePresheafCompRestrictScalarsAppIso snd g N (op V)).hom
  let tailOpen :
      (baseModulePresheaf (fst ≫ f) N).obj (op (fst ⁻¹ᵁ W)) ⟶
        (ModuleCat.restrictScalars g.appTop.hom).obj
          ((baseModulePresheaf snd N).obj (op V)) :=
    eqToHom (congrArg
        (fun q : P ⟶ Z ↦
          (baseModulePresheaf q N).obj (op (fst ⁻¹ᵁ W))) h) ≫
      (baseModulePresheafCompRestrictScalarsAppIso snd g N
        (op (fst ⁻¹ᵁ W))).hom ≫
      (ModuleCat.restrictScalars g.appTop.hom).map
        ((baseModulePresheaf snd N).map a)
  have hTail : tailFactor = tailOpen := by
    exact baseModulePresheafCongr_compRestrictScalars_naturality
      snd g h N a
  calc
    baseChangeCechFactorHom fst snd f g h M U n i =
        initialMap ≫ tailFactor := by
      simp only [baseChangeCechFactorHom, initialMap, tailFactor, W, V, N, a,
        baseCechFactorPushforwardIso, baseCechFactorCompRestrictScalarsIso,
        Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    _ = initialMap ≫ tailOpen :=
      congrArg (fun q ↦ initialMap ≫ q) hTail
    _ = baseChangeOpenHom fst snd f g h M
          (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          (((baseModulePresheaf snd ((pullback fst).obj M)).mapIso
            (eqToIso (fst.preimage_cechIntersection U n i)).op).inv) := by
      simp only [baseChangeOpenHom, initialMap, tailOpen, W, V, N, a,
        Functor.mapIso_inv, Category.assoc]

theorem baseChangeCechFactorHom_eq_baseChangeOpenAffineModel
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    baseChangeCechFactorHom fst snd f g h.w M U n i =
      baseChangeOpenAffineModel fst snd f g h M
          (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          (((baseModulePresheaf snd ((pullback fst).obj M)).mapIso
            (eqToIso (fst.preimage_cechIntersection U n i)).op).inv) := by
  rw [baseChangeCechFactorHom_eq_baseChangeOpenHom]
  rw [baseChangeOpenHom_eq_baseChangeOpenAffineModel]

theorem baseChangeCechFactorHom_isBaseChange
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι)
    [IsAffine (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)).toScheme] :
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
        ((ModuleCat.restrictScalars g.appTop.hom).obj
          (baseCechFactor snd ((pullback fst).obj M)
            (fun a ↦ fst ⁻¹ᵁ U a) n i)) :=
      ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom _
    IsBaseChange Γ(Y, ⊤)
      (baseChangeCechFactorHom fst snd f g h.w M U n i).hom := by
  let W : X.Opens := ∏ᶜ fun k : Fin (n + 1) ↦ U (i k)
  let V : P.Opens := ∏ᶜ fun k : Fin (n + 1) ↦ fst ⁻¹ᵁ U (i k)
  let N := (pullback fst).obj M
  let targetW := (baseModulePresheaf snd N).obj (op (fst ⁻¹ᵁ W))
  let targetV := (baseModulePresheaf snd N).obj (op V)
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
      ((ModuleCat.restrictScalars g.appTop.hom).obj targetW) :=
    ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom targetW
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
      ((ModuleCat.restrictScalars g.appTop.hom).obj targetV) :=
    ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom targetV
  letI : Module Γ(Z, ⊤) targetV :=
    inferInstanceAs (Module Γ(Z, ⊤)
      ((ModuleCat.restrictScalars g.appTop.hom).obj targetV))
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) targetV :=
    inferInstanceAs (IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
      ((ModuleCat.restrictScalars g.appTop.hom).obj targetV))
  have hOpen : IsBaseChange Γ(Y, ⊤)
      (baseChangeOpenAffineModel fst snd f g h M W).hom :=
    baseChangeOpenAffineModel_isBaseChange fst snd f g h M W
  let eTarget : targetW ≃ₗ[Γ(Y, ⊤)] targetV :=
    ((baseModulePresheaf snd N).mapIso
      (eqToIso (fst.preimage_cechIntersection U n i)).op).symm.toLinearEquiv
  have hResult := hOpen.comp (IsBaseChange.ofEquiv eTarget)
  rw [baseChangeCechFactorHom_eq_baseChangeOpenAffineModel]
  exact hResult

theorem baseChangeCechHom_component_isBaseChange
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤)
        ((ModuleCat.restrictScalars g.appTop.hom).obj
          ((baseCechComplex snd ((pullback fst).obj M)
            (fun a ↦ fst ⁻¹ᵁ U a)).X n)) :=
      ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom _
    IsBaseChange Γ(Y, ⊤)
      (ModuleCat.restrictScalarsComplexComponentLinearMap g.appTop.hom
        (baseChangeCechHom fst snd f g h.w M U) n) := by
  let R := Γ(Z, ⊤)
  let S := Γ(Y, ⊤)
  let N := (pullback fst).obj M
  let sourceFactor (i : Fin (n + 1) → ι) :=
    baseCechFactor f M U n i
  let targetFactor (i : Fin (n + 1) → ι) :=
    baseCechFactor snd N (fun a ↦ fst ⁻¹ᵁ U a) n i
  let restrictedTargetFactor (i : Fin (n + 1) → ι) :=
    (ModuleCat.restrictScalars g.appTop.hom).obj (targetFactor i)
  letI : Algebra R S := g.appTop.hom.toAlgebra
  letI (i : Fin (n + 1) → ι) :
      IsScalarTower R S
        ((ModuleCat.restrictScalars g.appTop.hom).obj (targetFactor i)) :=
    ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom _
  let factorMap (i : Fin (n + 1) → ι) :
      sourceFactor i →ₗ[R]
        restrictedTargetFactor i :=
    (baseChangeCechFactorHom fst snd f g h.w M U n i).hom
  have hFactor (i : Fin (n + 1) → ι) :
      IsBaseChange S (factorMap i) := by
    letI : IsAffine (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)).toScheme :=
      IsAffineOpen.cechIntersection U hU n i
    exact baseChangeCechFactorHom_isBaseChange
      fst snd f g h M U n i
  let piMap : (∀ i, sourceFactor i) →ₗ[R]
      (∀ i, restrictedTargetFactor i) :=
    LinearMap.pi fun i ↦ (factorMap i).comp (LinearMap.proj i)
  have hPi : IsBaseChange S piMap := by
    with_reducible_and_instances
      exact IsBaseChange.pi factorMap hFactor
  let sourceIso : (baseCechComplex f M U).X n ≃ₗ[R]
      (∀ i, sourceFactor i) :=
    (ModuleCat.piIsoPi sourceFactor).toLinearEquiv
  let targetObject :=
    (baseCechComplex snd N (fun a ↦ fst ⁻¹ᵁ U a)).X n
  letI : IsScalarTower R S
      ((ModuleCat.restrictScalars g.appTop.hom).obj targetObject) :=
    ModuleCat.restrictScalarsSource_isScalarTower g.appTop.hom targetObject
  let targetIsoBack : (∀ i, restrictedTargetFactor i) ≃ₗ[S]
      (ModuleCat.restrictScalars g.appTop.hom).obj targetObject :=
    (ModuleCat.piIsoPi targetFactor).symm.toLinearEquiv
  let targetIsoR :
      (ModuleCat.restrictScalars g.appTop.hom).obj targetObject ≃ₗ[R]
        (∀ i, restrictedTargetFactor i) :=
    targetIsoBack.symm.restrictScalars R
  have hSource : IsBaseChange S
      (piMap.comp sourceIso.toLinearMap) :=
    IsBaseChange.comp_equiv sourceIso piMap hPi
  let assembledMap : (baseCechComplex f M U).X n →ₗ[R]
      (ModuleCat.restrictScalars g.appTop.hom).obj targetObject :=
    (targetIsoBack.toLinearMap.restrictScalars R).comp
      (piMap.comp sourceIso.toLinearMap)
  have hAssembled : IsBaseChange S assembledMap := by
    exact hSource.comp (IsBaseChange.ofEquiv targetIsoBack)
  have hSourceIsoApply (x : (baseCechComplex f M U).X n)
      (i : Fin (n + 1) → ι) :
      sourceIso x i = (baseCechProjection f M U n i) x := by
    exact ModuleCat.piIsoPi_hom_ker_subtype_apply sourceFactor i x
  have hTargetIsoApply
      (x : (ModuleCat.restrictScalars g.appTop.hom).obj targetObject)
      (i : Fin (n + 1) → ι) :
      targetIsoR x i =
        ((ModuleCat.restrictScalars g.appTop.hom).map
          (baseCechProjection snd N (fun a ↦ fst ⁻¹ᵁ U a) n i)) x := by
    exact ModuleCat.piIsoPi_hom_ker_subtype_apply targetFactor i x
  have hPiMapApply (x : ∀ i, sourceFactor i)
      (i : Fin (n + 1) → ι) :
      piMap x i = factorMap i (x i) := by
    rfl
  have hAssembledApply (x : (baseCechComplex f M U).X n) :
      targetIsoR (assembledMap x) = piMap (sourceIso x) := by
    dsimp only [assembledMap]
    exact targetIsoR.apply_symm_apply _
  have hMap :
      ModuleCat.restrictScalarsComplexComponentLinearMap g.appTop.hom
          (baseChangeCechHom fst snd f g h.w M U) n =
        assembledMap := by
    apply LinearMap.ext
    intro x
    apply targetIsoR.injective
    funext i
    have hAA := congrArg (fun z ↦ z i) (hAssembledApply x)
    rw [hAA, hTargetIsoApply, hPiMapApply,
      hSourceIsoApply]
    exact ConcreteCategory.congr_hom
      (baseChangeCechHom_f_π fst snd f g h.w M U n i) x
  rw [hMap]
  exact hAssembled

/-- Over a finite affine family on a separated scheme, scalar extension of the
base-linear Cech complex is the Cech complex of the pulled-back module. -/
noncomputable def baseChangeCechComplexIso
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    ((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex (.up ℕ)).obj
        (baseCechComplex f M U) ≅
      baseCechComplex snd ((pullback fst).obj M)
        (fun i ↦ fst ⁻¹ᵁ U i) :=
  ModuleCat.homologicalComplexExtendScalarsIsoOfIsBaseChange
    g.appTop.hom
    (baseCechComplex f M U)
    (baseCechComplex snd ((pullback fst).obj M)
      (fun i ↦ fst ⁻¹ᵁ U i))
    (baseChangeCechHom fst snd f g h.w M U)
    (fun n ↦ baseChangeCechHom_component_isBaseChange
      fst snd f g h M U hU n)

/-- Flat base change commutes with the homology of the finite affine Cech
complex through the canonical pullback map. -/
noncomputable def baseChangeCechHomologyIso
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (hg : g.appTop.hom.Flat)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (ModuleCat.extendScalars g.appTop.hom).obj
        ((baseCechComplex f M U).homology n) ≅
      (baseCechComplex snd ((pullback fst).obj M)
        (fun i ↦ fst ⁻¹ᵁ U i)).homology n :=
  ModuleCat.homologyExtendScalarsIsoOfIsBaseChange
    g.appTop.hom hg
    (baseCechComplex f M U)
    (baseCechComplex snd ((pullback fst).obj M)
      (fun i ↦ fst ⁻¹ᵁ U i))
    (baseChangeCechHom fst snd f g h.w M U)
    (fun k ↦ baseChangeCechHom_component_isBaseChange
      fst snd f g h M U hU k) n

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- A paired degree-zero and degree-one base-change comparison.  This is the
small facade consumed by field-extension specializations; it deliberately
contains no relative proper-flat or semicontinuity assertion. -/
structure LowDegreeBaseChangeData
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (sourceZero sourceOne : ModuleCat.{u} R)
    (targetZero targetOne : ModuleCat.{u} S) where
  zero : (ModuleCat.extendScalars φ).obj sourceZero ≅ targetZero
  one : (ModuleCat.extendScalars φ).obj sourceOne ≅ targetOne

/-- The map on top sections induced by a morphism into the spectrum of a
field is flat. -/
theorem specField_appTop_flat
    (K L : Type u) [Field K] [Field L]
    (g : Spec (.of L) ⟶ Spec (.of K)) : g.appTop.hom.Flat := by
  letI : Field Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  exact RingHom.Flat.of_isField (Field.toIsField _) g.appTop.hom

/-- Flat base change in genuine degree zero, obtained by composing the native
Cech comparison on an affine cover with the canonical Cech base-change map. -/
noncomputable def hZeroFlatBaseChangeLinearEquivOfAffineOpenCover
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (hg : g.appTop.hom.Flat)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHZeroModule f M
    letI := baseSectionsHZeroModule snd N
    (ModuleCat.extendScalars g.appTop.hom).obj
        (ModuleCat.of Γ(Z, ⊤) (H M 0)) ≃ₗ[Γ(Y, ⊤)] H N 0 := by
  let N := (Scheme.Modules.pullback fst).obj M
  let V : ι → P.Opens := fun i ↦ fst ⁻¹ᵁ U i
  let hVcover : IsOpenCover V := hUcover.comap fst.base.hom
  letI := baseSectionsHZeroModule f M
  letI := baseSectionsHZeroModule snd N
  let eSource := nativeBaseCechHZeroLinearEquivCanonicalOfOpenCover
    f M U hUcover
  let eTarget := nativeBaseCechHZeroLinearEquivCanonicalOfOpenCover
    snd N V hVcover
  exact (((ModuleCat.extendScalars g.appTop.hom).mapIso
      eSource.symm.toModuleIso) ≪≫
    baseChangeCechHomologyIso fst snd f g h hg M U hU 0 ≪≫
    eTarget.toModuleIso).toLinearEquiv

/-- Flat base change in genuine degree one, obtained from the affine-cover
Cech comparison on the source and its inverse-image cover. -/
noncomputable def hOneFlatBaseChangeLinearEquivOfAffineOpenCover
    {P X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (hg : g.appTop.hom.Flat)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHOneModule f M
    letI := baseSectionsHOneModule snd N
    (ModuleCat.extendScalars g.appTop.hom).obj
        (ModuleCat.of Γ(Z, ⊤) (H M 1)) ≃ₗ[Γ(Y, ⊤)] H N 1 := by
  let N := (Scheme.Modules.pullback fst).obj M
  let V : ι → P.Opens := fun i ↦ fst ⁻¹ᵁ U i
  let hVcover : IsOpenCover V := hUcover.comap fst.base.hom
  letI : IsAffineHom fst :=
    MorphismProperty.of_isPullback h.flip (inferInstance : IsAffineHom g)
  let hV : ∀ i, IsAffineOpen (V i) := fun i ↦ (hU i).preimage fst
  letI : N.IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffineHom fst M
  letI := baseSectionsHOneModule f M
  letI := baseSectionsHOneModule snd N
  let eSource := nativeBaseCechHOneLinearEquivCanonicalOfAffineOpenCover
    f M U hUcover hU
  let eTarget := nativeBaseCechHOneLinearEquivCanonicalOfAffineOpenCover
    snd N V hVcover hV
  exact (((ModuleCat.extendScalars g.appTop.hom).mapIso
      eSource.symm.toModuleIso) ≪≫
    baseChangeCechHomologyIso fst snd f g h hg M U hU 1 ≪≫
    eTarget.toModuleIso).toLinearEquiv

/-- Degree-zero cohomology commutes with a Cartesian extension between two
field spectra, expressed over their canonical global-section rings. -/
noncomputable def hZeroFieldExtensionBaseChangeLinearEquivOfAffineOpenCover
    {P X : Scheme.{u}} (K L : Type u) [Field K] [Field L]
    [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of K)) (g : Spec (.of L) ⟶ Spec (.of K))
    (h : IsPullback fst snd f g)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHZeroModule f M
    letI := baseSectionsHZeroModule snd N
    (ModuleCat.extendScalars g.appTop.hom).obj
        (ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0))
      ≃ₗ[Γ(Spec (.of L), ⊤)] H N 0 :=
  hZeroFlatBaseChangeLinearEquivOfAffineOpenCover
    fst snd f g h (specField_appTop_flat K L g) M U hU hUcover

/-- Degree-one cohomology commutes with a Cartesian extension between two
field spectra, expressed over their canonical global-section rings. -/
noncomputable def hOneFieldExtensionBaseChangeLinearEquivOfAffineOpenCover
    {P X : Scheme.{u}} (K L : Type u) [Field K] [Field L]
    [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of K)) (g : Spec (.of L) ⟶ Spec (.of K))
    (h : IsPullback fst snd f g)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHOneModule f M
    letI := baseSectionsHOneModule snd N
    (ModuleCat.extendScalars g.appTop.hom).obj
        (ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1))
      ≃ₗ[Γ(Spec (.of L), ⊤)] H N 1 :=
  hOneFlatBaseChangeLinearEquivOfAffineOpenCover
    fst snd f g h (specField_appTop_flat K L g) M U hU hUcover

/-- The checked low-degree field-extension facade.  Its two fields are the
genuine `H⁰` and `H¹` comparisons, and it is the named downstream consumer
of the Cech-complex base-change assembly in this module. -/
noncomputable def fieldExtensionLowDegreeBaseChange
    {P X : Scheme.{u}} (K L : Type u) [Field K] [Field L]
    [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of K)) (g : Spec (.of L) ⟶ Spec (.of K))
    (h : IsPullback fst snd f g)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHZeroModule f M
    letI := baseSectionsHZeroModule snd N
    let sourceZero := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0)
    let targetZero := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 0)
    letI := baseSectionsHOneModule f M
    letI := baseSectionsHOneModule snd N
    let sourceOne := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1)
    let targetOne := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 1)
    LowDegreeBaseChangeData g.appTop.hom
      sourceZero sourceOne targetZero targetOne := by
  let N := (Scheme.Modules.pullback fst).obj M
  letI := baseSectionsHZeroModule f M
  letI := baseSectionsHZeroModule snd N
  let sourceZero := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0)
  let targetZero := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 0)
  letI := baseSectionsHOneModule f M
  letI := baseSectionsHOneModule snd N
  let sourceOne := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1)
  let targetOne := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 1)
  exact
    { zero :=
        (hZeroFieldExtensionBaseChangeLinearEquivOfAffineOpenCover
          K L fst snd f g h M U hU hUcover).toModuleIso
      one :=
        (hOneFieldExtensionBaseChangeLinearEquivOfAffineOpenCover
          K L fst snd f g h M U hU hUcover).toModuleIso }

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
