/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorBaseChange

/-!
# Cross-chart naturality of affine divisor tensor addition

Equality-induced comparisons between extended inverse ideals commute with multiplication.  After
passing through affine tilde and its tensor comparison, the resulting cross-chart isomorphism for
a divisor sum commutes with the deterministic sum-to-tensor isomorphisms.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped TensorProduct

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForOverlapTensorNaturality (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Multiplication of extended inverse ideals is natural for two equality-induced comparisons. -/
private theorem extendedInverseIdealTensorAddEquiv_naturality
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (D₁ E₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ E₂ : WeilDivisor (HeightOneSpectrum R₂))
    (hD : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (hE : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K E₁ E₂) :
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
    (TensorProduct.congr
        (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ hD)
        (extendedInverseIdealEquiv R₁ R₂ B K E₁ E₂ hE)).trans
      (extendedInverseIdealTensorAddEquiv R₂ B K D₂ E₂) =
    (extendedInverseIdealTensorAddEquiv R₁ B K D₁ E₁).trans
      (extendedInverseIdealEquiv R₁ R₂ B K
        (D₁ + E₁) (D₂ + E₂) hDE) := by
  dsimp only
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      apply Subtype.ext
      simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        extendedInverseIdealTensorAddEquiv_tmul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The same module square in the sum-to-tensor orientation used by the tilde isomorphism. -/
private theorem extendedInverseIdealTensorAddEquiv_symm_naturality
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (D₁ E₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ E₂ : WeilDivisor (HeightOneSpectrum R₂))
    (hD : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (hE : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K E₁ E₂) :
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
    (extendedInverseIdealEquiv R₁ R₂ B K
        (D₁ + E₁) (D₂ + E₂) hDE).trans
      (extendedInverseIdealTensorAddEquiv R₂ B K D₂ E₂).symm =
    (extendedInverseIdealTensorAddEquiv R₁ B K D₁ E₁).symm.trans
      (TensorProduct.congr
        (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ hD)
        (extendedInverseIdealEquiv R₁ R₂ B K E₁ E₂ hE)) := by
  dsimp only
  apply LinearEquiv.ext
  intro z
  let m₂ := extendedInverseIdealTensorAddEquiv R₂ B K D₂ E₂
  apply m₂.injective
  dsimp only [m₂]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hz := LinearEquiv.congr_fun
    (extendedInverseIdealTensorAddEquiv_naturality
      R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE)
    ((extendedInverseIdealTensorAddEquiv R₁ B K D₁ E₁).symm z)
  simpa only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hz.symm

/-- Equality-induced cross-chart comparison commutes with the deterministic addition
isomorphism for extended inverse-ideal tilde sheaves. -/
theorem extendedInverseIdealAddIso_naturality
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (D₁ E₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ E₂ : WeilDivisor (HeightOneSpectrum R₂))
    (hD : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (hE : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K E₁ E₂) :
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
    extendedInverseIdealTildeIso R₁ R₂ B K
          (D₁ + E₁) (D₂ + E₂) hDE ≪≫
        extendedInverseIdealAddIso R₂ B K D₂ E₂ =
      extendedInverseIdealAddIso R₁ B K D₁ E₁ ≪≫
        (extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ hD ⊗ᵢ
          extendedInverseIdealTildeIso R₁ R₂ B K E₁ E₂ hE) := by
  dsimp only
  let T := _root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)
  let qD := (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ hD).toModuleIso.hom
  let qE := (extendedInverseIdealEquiv R₁ R₂ B K E₁ E₂ hE).toModuleIso.hom
  let hDE := Boundary.overlapInverseIdealExtensionEq_add
    R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
  let qS := (extendedInverseIdealEquiv R₁ R₂ B K
    (D₁ + E₁) (D₂ + E₂) hDE).toModuleIso.hom
  let m₁ : ModuleCat.of B (extendedInverseIdeal R₁ B K (D₁ + E₁)) ⟶
      ModuleCat.of B
        (extendedInverseIdeal R₁ B K D₁ ⊗[B] extendedInverseIdeal R₁ B K E₁) :=
    (extendedInverseIdealTensorAddEquiv R₁ B K D₁ E₁).symm.toModuleIso.hom
  let m₂ : ModuleCat.of B (extendedInverseIdeal R₂ B K (D₂ + E₂)) ⟶
      ModuleCat.of B
        (extendedInverseIdeal R₂ B K D₂ ⊗[B] extendedInverseIdeal R₂ B K E₂) :=
    (extendedInverseIdealTensorAddEquiv R₂ B K D₂ E₂).symm.toModuleIso.hom
  let qP := qD ⊗ₘ qE
  let τ₁ := AffineTilde.tildeTensorIso B
    (extendedInverseIdeal R₁ B K D₁) (extendedInverseIdeal R₁ B K E₁)
  let τ₂ := AffineTilde.tildeTensorIso B
    (extendedInverseIdeal R₂ B K D₂) (extendedInverseIdeal R₂ B K E₂)
  have hs := extendedInverseIdealTensorAddEquiv_symm_naturality
    R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
  dsimp only at hs
  have hmodule : qS ≫ m₂ = m₁ ≫ qP := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    dsimp only [qS, m₂, m₁, qP, qD, qE, CategoryTheory.comp_apply,
      LinearEquiv.toModuleIso, LinearEquiv.toModuleIso_hom]
    exact LinearEquiv.congr_fun hs z
  have hmap : T.map qS ≫ T.map m₂ = T.map m₁ ≫ T.map qP := by
    exact (T.map_comp qS m₂).symm |>.trans
      ((congrArg (fun z ↦ T.map z) hmodule).trans (T.map_comp m₁ qP))
  have hnat := AffineTilde.tildeTensorIso_inv_naturality B qD qE
  change T.map qP ≫ τ₂.inv = τ₁.inv ≫ (T.map qD ⊗ₘ T.map qE) at hnat
  apply Iso.ext
  dsimp only [extendedInverseIdealTildeIso, extendedInverseIdealAddIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change (T.map qS ≫ T.map m₂) ≫ τ₂.inv =
    (T.map m₁ ≫ τ₁.inv) ≫ (T.map qD ⊗ₘ T.map qE)
  have h₁ := congrArg (fun z ↦ z ≫ τ₂.inv) hmap
  have h₂ := congrArg (fun z ↦ T.map m₁ ≫ z) hnat
  exact h₁.trans ((Category.assoc _ _ _).trans
    (h₂.trans (Category.assoc _ _ _).symm))

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension
