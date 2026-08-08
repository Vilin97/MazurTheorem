/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechPushforward

/-!
# Cech complexes and pushforward

This file identifies the native all-tuples base-linear Cech complex of a module on an
inverse-image cover with the Cech complex of its pushforward.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The native Cech object of an inverse-image cover agrees with the native Cech object of
the pushforward. -/
noncomputable def baseCechObjectPushforwardIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) :
    (baseCechComplex (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j)).X n ≅
      (baseCechComplex π ((pushforward f).obj M) U).X n :=
  Pi.mapIso (fun i : Fin (n + 1) → ι =>
    baseCechFactorPushforwardIso f π M U n i)

@[reassoc]
theorem baseCechObjectPushforwardIso_hom_π
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (baseCechObjectPushforwardIso f π M U n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor π ((pushforward f).obj M) U n j) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
          baseCechFactor (f ≫ π) M (fun a ↦ f ⁻¹ᵁ U a) n j) i ≫
        (baseCechFactorPushforwardIso f π M U n i).hom :=
  Pi.mapIso_hom_π _ i

private theorem baseCechObjectPushforwardIso_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (k : Fin (n + 2)) :
    (baseCechObjectPushforwardIso f π M U n).hom ≫
        baseCechCoface π ((pushforward f).obj M) U n k =
      baseCechCoface (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n k ≫
        (baseCechObjectPushforwardIso f π M U (n + 1)).hom := by
  let sourceLow :=
    (baseCechComplex (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j)).X n
  let sourceHigh :=
    (baseCechComplex (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j)).X (n + 1)
  let targetLow :=
    (baseCechComplex π ((pushforward f).obj M) U).X n
  let targetHigh :=
    (baseCechComplex π ((pushforward f).obj M) U).X (n + 1)
  let eLow : sourceLow ≅ targetLow :=
    baseCechObjectPushforwardIso f π M U n
  let eHigh : sourceHigh ≅ targetHigh :=
    baseCechObjectPushforwardIso f π M U (n + 1)
  let sourceCoface : sourceLow ⟶ sourceHigh :=
    baseCechCoface (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n k
  let targetCoface : targetLow ⟶ targetHigh :=
    baseCechCoface π ((pushforward f).obj M) U n k
  change eLow.hom ≫ targetCoface = sourceCoface ≫ eHigh.hom
  apply Pi.hom_ext
  intro a
  change Fin (n + 2) → ι at a
  let sourceLowProj : sourceLow ⟶
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
    Pi.π (fun b : Fin (n + 1) → ι =>
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n b)
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  let sourceHighProj : sourceHigh ⟶
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a :=
    Pi.π (fun b : Fin (n + 2) → ι =>
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) b) a
  let targetLowProj : targetLow ⟶
      baseCechFactor π ((pushforward f).obj M) U n
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
    Pi.π (fun b : Fin (n + 1) → ι =>
      baseCechFactor π ((pushforward f).obj M) U n b)
        (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  let targetHighProj : targetHigh ⟶
      baseCechFactor π ((pushforward f).obj M) U (n + 1) a :=
    Pi.π (fun b : Fin (n + 2) → ι =>
      baseCechFactor π ((pushforward f).obj M) U (n + 1) b) a
  let sourceMap :
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) ⟶
        baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a :=
    (baseModulePresheaf (f ≫ π) M).map
      (((FormalCoproduct.mk _ (fun j ↦ f ⁻¹ᵁ U j)).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a).op
  let targetMap :
      baseCechFactor π ((pushforward f).obj M) U n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) ⟶
        baseCechFactor π ((pushforward f).obj M) U (n + 1) a :=
    (baseModulePresheaf π ((pushforward f).obj M)).map
      (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a).op
  let factorLow :
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) ⟶
        baseCechFactor π ((pushforward f).obj M) U n
          (a ∘ (SimplexCategory.δ k).toOrderHom.toFun) :=
    (baseCechFactorPushforwardIso f π M U n
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom
  let factorHigh :
      baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a ⟶
        baseCechFactor π ((pushforward f).obj M) U (n + 1) a :=
    (baseCechFactorPushforwardIso f π M U (n + 1) a).hom
  have hTargetCoface :
      targetCoface ≫ targetHighProj = targetLowProj ≫ targetMap :=
    baseCechCoface_comp_π π ((pushforward f).obj M) U n k a
  have hSourceCoface :
      sourceCoface ≫ sourceHighProj = sourceLowProj ≫ sourceMap :=
    baseCechCoface_comp_π
      (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n k a
  have hLowIso :
      eLow.hom ≫ targetLowProj = sourceLowProj ≫ factorLow :=
    baseCechObjectPushforwardIso_hom_π f π M U n
      (a ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  have hHighIso :
      eHigh.hom ≫ targetHighProj = sourceHighProj ≫ factorHigh :=
    baseCechObjectPushforwardIso_hom_π f π M U (n + 1) a
  have hFactor :
      sourceMap ≫ factorHigh = factorLow ≫ targetMap :=
    baseCechFactorPushforwardIso_naturality f π M U n k a
  calc
    (eLow.hom ≫ targetCoface) ≫ targetHighProj =
        sourceLowProj ≫ (factorLow ≫ targetMap) := by
      rw [Category.assoc, hTargetCoface, ← Category.assoc, hLowIso,
        Category.assoc]
    _ = sourceLowProj ≫ (sourceMap ≫ factorHigh) := by rw [← hFactor]
    _ = (sourceCoface ≫ eHigh.hom) ≫ targetHighProj := by
      rw [← Category.assoc, ← hSourceCoface, Category.assoc,
        ← hHighIso, ← Category.assoc]

private theorem baseCechObjectPushforwardIso_differential_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) :
    (baseCechObjectPushforwardIso f π M U n).hom ≫
        (baseCechComplex π ((pushforward f).obj M) U).d n (n + 1) =
      (baseCechComplex (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j)).d n (n + 1) ≫
        (baseCechObjectPushforwardIso f π M U (n + 1)).hom := by
  rw [baseCechComplex_d_eq_sum_cofaces,
    baseCechComplex_d_eq_sum_cofaces]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    (baseCechObjectPushforwardIso_naturality f π M U n k)

/-- Pushforward identifies the native base-linear Cech complex on a cover with the complex on
its inverse-image cover. -/
noncomputable def baseCechComplexPushforwardIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) :
    baseCechComplex (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) ≅
      baseCechComplex π ((pushforward f).obj M) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => baseCechObjectPushforwardIso f π M U n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      exact baseCechObjectPushforwardIso_differential_naturality
        f π M U i)

@[simp]
theorem baseCechComplexPushforwardIso_hom_f
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) :
    (baseCechComplexPushforwardIso f π M U).hom.f n =
      (baseCechObjectPushforwardIso f π M U n).hom :=
  rfl

end AlgebraicGeometry.Scheme.Modules
