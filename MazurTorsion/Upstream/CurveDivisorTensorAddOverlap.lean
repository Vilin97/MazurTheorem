/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorRestrictionOverlapNaturality
import MazurTorsion.Upstream.CurveLineBundleTripleTower

/-!
# Tensor addition on a curve-chart overlap

The cross-chart naturality square for extended inverse-ideal tilde sheaves is specialized to a
common affine subopen of two curve charts.  The two equality witnesses are obtained by first
comparing on the full pairwise intersection and then applying the checked scalar-tower theorem,
so this is the equality provenance used by the chosen pairwise overlap transition.

Combining that raw square with the two one-leg restriction squares proves tensor/addition
naturality for the actual chosen restriction comparisons between the coordinate-divisor line
bundles.  Alignment with the separately proof-defined global-divisor transition family and
assembly into a morphism of descent data remain separate.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open scoped AlgebraicGeometry TensorProduct

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForDivisorTensorOverlap (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- On a common affine subopen of two proper-smooth curve charts, the equality-induced
inverse-ideal comparison commutes with deterministic divisor addition.  Both factorwise
equalities retain their pairwise-intersection provenance. -/
theorem localExtendedInverseIdealAddIso_naturalityViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE
    extendedInverseIdealTildeIso
          Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
          (d₁ + e₁) (d₂ + e₂) hDE ≪≫
        extendedInverseIdealAddIso Γ(X, U₂) Γ(X, W) X.functionField d₂ e₂ =
      extendedInverseIdealAddIso Γ(X, U₁) Γ(X, W) X.functionField d₁ e₁ ≪≫
        (extendedInverseIdealTildeIso
            Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField d₁ d₂ hD ⊗ᵢ
          extendedInverseIdealTildeIso
            Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField e₁ e₂ hE) := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  let d₁ := localDivisor X U₁ hU₁ h₁ D
  let e₁ := localDivisor X U₁ hU₁ h₁ E
  let d₂ := localDivisor X U₂ hU₂ h₂ D
  let e₂ := localDivisor X U₂ hU₂ h₂ E
  let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  exact extendedInverseIdealAddIso_naturality
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE

/-- On a common affine subopen of two proper-smooth curve charts, deterministic divisor
addition commutes with the chosen restriction comparisons whose equality witnesses come from
the pairwise chart intersection. -/
theorem localLineBundleAddIso_restrictViaPullback_naturalityViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
      restrictionTorsionFree X U₁ W hWU₁
    letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
      restrictionTorsionFree X U₂ W hWU₂
    letI : IsFractionRing Γ(X, U₁) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
    letI : IsFractionRing Γ(X, U₂) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    let d₁ := localDivisor X U₁ hU₁ h₁ D
    let e₁ := localDivisor X U₁ hU₁ h₁ E
    let d₂ := localDivisor X U₂ hU₂ h₂ D
    let e₂ := localDivisor X U₂ hU₂ h₂ E
    let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
    let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE
    let A₁ :=
      (Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₁) Γ(X, W))).mapIso
          (ExplicitIdeal.lineBundleAddIso Γ(X, U₁) X.functionField d₁ e₁) ≪≫
        lineBundleTensorRestrictionIsoViaPullback
          Γ(X, U₁) Γ(X, W) X.functionField d₁ e₁
    let A₂ :=
      (Scheme.Modules.restrictFunctor (extensionMap Γ(X, U₂) Γ(X, W))).mapIso
          (ExplicitIdeal.lineBundleAddIso Γ(X, U₂) X.functionField d₂ e₂) ≪≫
        lineBundleTensorRestrictionIsoViaPullback
          Γ(X, U₂) Γ(X, W) X.functionField d₂ e₂
    let tD := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField d₁ d₂ hD
    let tE := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField e₁ e₂ hE
    let tDE := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      (d₁ + e₁) (d₂ + e₂) hDE
    A₁ ≪≫ (tD ⊗ᵢ tE) = tDE ≪≫ A₂ := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  let d₁ := localDivisor X U₁ hU₁ h₁ D
  let e₁ := localDivisor X U₁ hU₁ h₁ E
  let d₂ := localDivisor X U₂ hU₂ h₂ D
  let e₂ := localDivisor X U₂ hU₂ h₂ E
  let hD := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D
  let hE := localDivisorOverlapExtensionEqViaPairwiseIntersection
    K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ E
  exact lineBundleAddIso_restrict_viaPullback_naturality
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      d₁ e₁ d₂ e₂ hD hE

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
