/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleTripleNaturality

/-!
# Tower compatibility for divisor transitions on triple intersections

Pairwise divisor transitions are defined from equality of inverse ideals over a pairwise affine
intersection.  This file proves the algebraic tower step needed on triple intersections: the
pairwise equality extends to any common affine subopen, and the resulting comparison agrees with
the comparison constructed directly on that common affine ring.

This does not yet identify the surrounding `restrictFunctorIsoPullback` and pseudofunctor
composition isomorphisms.  That final sheaf-level naturality statement is kept separate from the
checked inverse-ideal tower law proved here.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped AlgebraicGeometry

universe u v

/-- Construct the inverse-ideal equality on a common affine subopen by first constructing it on
the full pairwise intersection and then applying the checked scalar-tower base-change theorem.
This records the precise provenance of the equality consumed by the pairwise overlap model. -/
theorem localDivisorOverlapExtensionEqViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D : WeilDivisor (CodimensionOnePoint X)) :
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
    Boundary.OverlapInverseIdealExtensionEq
      Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField
      (localDivisor X U₁ hU₁ h₁ D) (localDivisor X U₂ hU₂ h₂ D) := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let V := U₁ ⊓ U₂
  let hV : IsAffineOpen V := hU₁.inf hU₂
  let hWV : W ≤ V := le_inf hWU₁ hWU₂
  letI : Nonempty V := nonempty_inf_of_isIntegral X U₁ U₂
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  let hcompatV := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f V hV
  let hcompatW := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW
  letI : IsDedekindDomain Γ(X, V) := hcompatV.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) := hcompatW.isDedekindDomain
  letI := restrictionAlgebra X U₁ V inf_le_left
  letI := restrictionAlgebra X U₂ V inf_le_right
  letI := restrictionAlgebra X V W hWV
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, V) :=
    restrictionTorsionFree X U₁ V inf_le_left
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, V) :=
    restrictionTorsionFree X U₂ V inf_le_right
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, V)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ V hU₁ hV inf_le_left
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, V)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ V hU₂ hV inf_le_right
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsScalarTower Γ(X, U₁) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X U₁ V W inf_le_left hWV hWU₁
  letI : IsScalarTower Γ(X, U₂) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X U₂ V W inf_le_right hWV hWU₂
  letI : IsScalarTower Γ(X, V) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X V W hWV
  let hPair := overlapInverseIdealExtensionEq_localDivisor_of_commonMap
    X U₁ U₂ hU₁ hU₂ h₁ h₂ Γ(X, V)
      (restrictionFunctionFieldTower X U₁ V inf_le_left)
      (restrictionFunctionFieldTower X U₂ V inf_le_right)
      hV.fromSpec
      (restrictionExtensionMap_comp_fromSpec X U₁ V hU₁ hV inf_le_left)
      (restrictionExtensionMap_comp_fromSpec X U₂ V hU₂ hV inf_le_right) D
  exact overlapInverseIdealExtensionEq_baseChange
    Γ(X, U₁) Γ(X, U₂) Γ(X, V) Γ(X, W) X.functionField _ _ hPair

/-- The line-bundle comparison on `W` whose inverse-ideal equality is explicitly obtained by
base-changing the pairwise-intersection equality.  This has the same source and target as the
direct common-affine comparison, but records the pairwise provenance needed by the chosen
overlap transition. -/
noncomputable def localLineBundleRestrictionIsoViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    (localLineBundle X U₁ hU₁ h₁ D).obj.restrict
        (extensionMap Γ(X, U₁) Γ(X, W)) ≅
      (localLineBundle X U₂ hU₂ h₂ D).obj.restrict
        (extensionMap Γ(X, U₂) Γ(X, W)) := by
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  let hcompatW := AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW
  letI : IsDedekindDomain Γ(X, W) := hcompatW.isDedekindDomain
  letI : Module.IsTorsionFree Γ(X, U₁) Γ(X, W) :=
    restrictionTorsionFree X U₁ W hWU₁
  letI : Module.IsTorsionFree Γ(X, U₂) Γ(X, W) :=
    restrictionTorsionFree X U₂ W hWU₂
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  letI : IsFractionRing Γ(X, U₁) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₁ hU₁
  letI : IsFractionRing Γ(X, U₂) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U₂ hU₂
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  change
    (AffineDedekind.lineBundle Γ(X, U₁) X.functionField
        (localDivisor X U₁ hU₁ h₁ D)).obj.restrict
        (extensionMap Γ(X, U₁) Γ(X, W)) ≅
      (AffineDedekind.lineBundle Γ(X, U₂) X.functionField
        (localDivisor X U₂ hU₂ h₂ D)).obj.restrict
        (extensionMap Γ(X, U₂) Γ(X, W))
  exact chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    Γ(X, U₁) Γ(X, U₂) Γ(X, W) X.functionField _ _
      (localDivisorOverlapExtensionEqViaPairwiseIntersection
        K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D)

/-- The comparison obtained by extending the pairwise-intersection inverse-ideal equality is
the directly constructed common-affine comparison.  Since both constructions use the same
specified inverse ideals and equality-induced map, proof irrelevance removes the different
provenance proofs after the scalar-tower theorem has aligned their data. -/
theorem localLineBundleRestrictionIsoViaPairwiseIntersection_eq_direct
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    localLineBundleRestrictionIsoViaPairwiseIntersection
        K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D =
      localLineBundleRestrictionIsoOnCommonAffineOpen
        X U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  rfl

/-- The pairwise-intersection comparison over `W`, expressed between module pullbacks rather
than open-immersion restriction functors.  This is the direct common-affine model to which the
further pullback of `localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve` must be
compared. -/
noncomputable def localLineBundlePullbackIsoViaPairwiseIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ W : X.Opens) [Nonempty U₁] [Nonempty U₂] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    (Scheme.Modules.pullback (extensionMap Γ(X, U₁) Γ(X, W))).obj
        (localLineBundle X U₁ hU₁ h₁ D).obj ≅
      (Scheme.Modules.pullback (extensionMap Γ(X, U₂) Γ(X, W))).obj
        (localLineBundle X U₂ hU₂ h₂ D).obj := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  exact ((Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap Γ(X, U₁) Γ(X, W))).app
        (localLineBundle X U₁ hU₁ h₁ D).obj).symm ≪≫
    localLineBundleRestrictionIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap Γ(X, U₂) Γ(X, W))).app
        (localLineBundle X U₂ hU₂ h₂ D).obj

/-- The three module-pullback comparisons whose inverse-ideal equalities come from the three
pairwise intersections satisfy transitivity on one common affine subopen.  This is a downstream
cocycle consumer of the inverse-ideal tower theorem and the identification with the direct
common-affine comparisons. -/
theorem localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (U₁ U₂ U₃ W : X.Opens)
    [Nonempty U₁] [Nonempty U₂] [Nonempty U₃] [Nonempty W]
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (hU₃ : IsAffineOpen U₃) (hW : IsAffineOpen W)
    (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂) (hWU₃ : W ≤ U₃)
    (h₁ : AffineChart.DedekindOrderCompatibility X U₁ hU₁)
    (h₂ : AffineChart.DedekindOrderCompatibility X U₂ hU₂)
    (h₃ : AffineChart.DedekindOrderCompatibility X U₃ hU₃)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
    letI : IsDedekindDomain Γ(X, U₃) := h₃.isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI := restrictionAlgebra X U₃ W hWU₃
    letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
    letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
    letI : IsOpenImmersion (extensionMap Γ(X, U₃) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U₃ W hU₃ hW hWU₃
    (localLineBundlePullbackIsoViaPairwiseIntersection
      K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom ≫
      (localLineBundlePullbackIsoViaPairwiseIntersection
        K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom =
    (localLineBundlePullbackIsoViaPairwiseIntersection
      K X f U₁ U₃ W hU₁ hU₃ hW hWU₁ hWU₃ h₁ h₃ D).hom := by
  letI : IsDedekindDomain Γ(X, U₁) := h₁.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₂) := h₂.isDedekindDomain
  letI : IsDedekindDomain Γ(X, U₃) := h₃.isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI := restrictionAlgebra X U₃ W hWU₃
  letI : IsOpenImmersion (extensionMap Γ(X, U₁) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₁ W hU₁ hW hWU₁
  letI : IsOpenImmersion (extensionMap Γ(X, U₂) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₂ W hU₂ hW hWU₂
  letI : IsOpenImmersion (extensionMap Γ(X, U₃) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U₃ W hU₃ hW hWU₃
  unfold localLineBundlePullbackIsoViaPairwiseIntersection
  rw [localLineBundleRestrictionIsoViaPairwiseIntersection_eq_direct,
    localLineBundleRestrictionIsoViaPairwiseIntersection_eq_direct,
    localLineBundleRestrictionIsoViaPairwiseIntersection_eq_direct]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  let e₁ := (Scheme.Modules.restrictFunctorIsoPullback
    (extensionMap Γ(X, U₁) Γ(X, W))).app
      (localLineBundle X U₁ hU₁ h₁ D).obj
  let e₃ := (Scheme.Modules.restrictFunctorIsoPullback
    (extensionMap Γ(X, U₃) Γ(X, W))).app
      (localLineBundle X U₃ hU₃ h₃ D).obj
  have htrans := localLineBundleRestrictionIsoOnCommonAffineOpen_hom_trans
    X U₁ U₂ U₃ W hU₁ hU₂ hU₃ hW hWU₁ hWU₂ hWU₃ h₁ h₂ h₃ D
  simpa only [e₁, e₃, Category.assoc] using
    congrArg (fun z ↦ e₁.inv ≫ z ≫ e₃.hom) htrans

/-- On the actual affine triple chart intersection, the three direct module-pullback models
obtained from the pairwise inverse-ideal equalities satisfy the cocycle equation.  This is the
common-model cocycle consumed by the remaining pseudofunctorial comparison with Mathlib's
chosen triple overlap. -/
theorem localLineBundlePullbackIsoViaPairwiseIntersection_triple_hom_trans
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let W := (U i ⊓ U j) ⊓ U k
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let hW : IsAffineOpen W := ((hU i).inf (hU j)).inf (hU k)
    let hWi : W ≤ U i := inf_le_left.trans inf_le_left
    let hWj : W ≤ U j := inf_le_left.trans inf_le_right
    let hWk : W ≤ U k := inf_le_right
    letI : Nonempty (U i) := hnonempty i
    letI : Nonempty (U j) := hnonempty j
    letI : Nonempty (U k) := hnonempty k
    letI : Nonempty ↑(U i ⊓ U j : X.Opens) :=
      nonempty_inf_of_isIntegral X (U i) (U j)
    letI : Nonempty ↑W := nonempty_inf_of_isIntegral X (U i ⊓ U j) (U k)
    letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
    letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
    letI : IsDedekindDomain Γ(X, U k) := (h k).isDedekindDomain
    letI : IsDedekindDomain Γ(X, W) :=
      (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
    letI := restrictionAlgebra X (U i) W hWi
    letI := restrictionAlgebra X (U j) W hWj
    letI := restrictionAlgebra X (U k) W hWk
    letI : IsOpenImmersion (extensionMap Γ(X, U i) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW hWi
    letI : IsOpenImmersion (extensionMap Γ(X, U j) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW hWj
    letI : IsOpenImmersion (extensionMap Γ(X, U k) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X (U k) W (hU k) hW hWk
    (localLineBundlePullbackIsoViaPairwiseIntersection
      K X f (U i) (U j) W (hU i) (hU j) hW hWi hWj (h i) (h j) D).hom ≫
      (localLineBundlePullbackIsoViaPairwiseIntersection
        K X f (U j) (U k) W (hU j) (hU k) hW hWj hWk (h j) (h k) D).hom =
    (localLineBundlePullbackIsoViaPairwiseIntersection
      K X f (U i) (U k) W (hU i) (hU k) hW hWi hWk (h i) (h k) D).hom := by
  let W := (U i ⊓ U j) ⊓ U k
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hW : IsAffineOpen W := ((hU i).inf (hU j)).inf (hU k)
  let hWi : W ≤ U i := inf_le_left.trans inf_le_left
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWk : W ≤ U k := inf_le_right
  letI : Nonempty (U i) := hnonempty i
  letI : Nonempty (U j) := hnonempty j
  letI : Nonempty (U k) := hnonempty k
  letI : Nonempty ↑(U i ⊓ U j : X.Opens) :=
    nonempty_inf_of_isIntegral X (U i) (U j)
  letI : Nonempty ↑W := nonempty_inf_of_isIntegral X (U i ⊓ U j) (U k)
  letI : IsDedekindDomain Γ(X, U i) := (h i).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U j) := (h j).isDedekindDomain
  letI : IsDedekindDomain Γ(X, U k) := (h k).isDedekindDomain
  letI : IsDedekindDomain Γ(X, W) :=
    (AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurve K X f W hW).isDedekindDomain
  letI := restrictionAlgebra X (U i) W hWi
  letI := restrictionAlgebra X (U j) W hWj
  letI := restrictionAlgebra X (U k) W hWk
  letI : IsOpenImmersion (extensionMap Γ(X, U i) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U i) W (hU i) hW hWi
  letI : IsOpenImmersion (extensionMap Γ(X, U j) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U j) W (hU j) hW hWj
  letI : IsOpenImmersion (extensionMap Γ(X, U k) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X (U k) W (hU k) hW hWk
  exact localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
    K X f (U i) (U j) (U k) W (hU i) (hU j) (hU k) hW hWi hWj hWk
      (h i) (h j) (h k) D

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
