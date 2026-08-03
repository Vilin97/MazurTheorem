/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleTripleTower

/-!
# Pullback coherence boundary for divisor transition maps

The inverse-ideal comparison underlying a pairwise divisor transition is already compatible with
scalar towers.  This file proves the surrounding pseudofunctorial composition statement: pulling
the pairwise model first to a common affine open and then to a test scheme agrees with pulling it
along the composite map.

It also exposes the independently constructed direct comparison on the common affine open and
packages the exact remaining compatibility predicate between the two constructions.  A checked
consumer transports that predicate through every further pullback.  Establishing the predicate in
full generality requires a naturality law for `restrictFunctorIsoPullback` and the independently
constructed inverse-ideal base-change isomorphisms; it is not asserted here.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped AlgebraicGeometry

universe u v

/-- The pairwise-intersection model pulled once to a smaller common affine open. -/
noncomputable def localLineBundlePairwiseModelHomOnCommonAffine
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hWab : W ≤ U a ⊓ U b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    (Scheme.Modules.pullback (extensionMap Γ(X, U a) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D a).obj ⟶
      (Scheme.Modules.pullback (extensionMap Γ(X, U b) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj := by
  let V := U a ⊓ U b
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) V inf_le_left
  letI := restrictionAlgebra X (U b) V inf_le_right
  letI := restrictionAlgebra X V W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI : IsScalarTower Γ(X, U a) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X (U a) V W inf_le_left hWab hWa
  letI : IsScalarTower Γ(X, U b) Γ(X, V) Γ(X, W) :=
    restrictionAlgebraTower X (U b) V W inf_le_right hWab hWb
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
    (extensionMap Γ(X, V) Γ(X, W))
    (extensionMap Γ(X, U a) Γ(X, W))
    (extensionMap Γ(X, U b) Γ(X, W))
    (restrictionExtensionMap_comp X (U a) V W inf_le_left hWab hWa)
    (restrictionExtensionMap_comp X (U b) V W inf_le_right hWab hWb)

/-- Pulling the pairwise model in two stages is its pullback along the composite map. -/
theorem pullHom_localLineBundlePairwiseModelHomOnCommonAffine
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ (coordinateCover U hcover hU).X a)
    (q_b : Y ⟶ (coordinateCover U hcover hU).X b)
    (hgₐ :
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hgPairₐ :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hWab)
        g qₐ q_b hgₐ hg_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b
        hgPairₐ hgPair_b := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI : IsScalarTower Γ(X, U a) Γ(X, U a ⊓ U b) Γ(X, W) :=
    restrictionAlgebraTower X (U a) (U a ⊓ U b) W inf_le_left hWab hWa
  letI : IsScalarTower Γ(X, U b) Γ(X, U a ⊓ U b) Γ(X, W) :=
    restrictionAlgebraTower X (U b) (U a ⊓ U b) W inf_le_right hWab hWb
  unfold localLineBundlePairwiseModelHomOnCommonAffine
  exact pullHom_pullHom
    (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
    (extensionMap Γ(X, U a ⊓ U b) Γ(X, W))
    (extensionMap Γ(X, U a) Γ(X, W))
    (extensionMap Γ(X, U b) Γ(X, W)) g qₐ q_b
    (restrictionExtensionMap_comp X (U a) (U a ⊓ U b) W
      inf_le_left hWab hWa)
    (restrictionExtensionMap_comp X (U b) (U a ⊓ U b) W
      inf_le_right hWab hWb)
    hgₐ hg_b

/-- The separately constructed direct inverse-ideal comparison on a common affine open. -/
noncomputable def localLineBundleDirectModelHomOnCommonAffine
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    (Scheme.Modules.pullback (extensionMap Γ(X, U a) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D a).obj ⟶
      (Scheme.Modules.pullback (extensionMap Γ(X, U b) Γ(X, W))).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI : Nonempty (U a) := hnonempty a
  letI : Nonempty (U b) := hnonempty b
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  exact (localLineBundlePullbackIsoViaPairwiseIntersection
    K X f (U a) (U b) W (hU a) (hU b) hW hWa hWb (h a) (h b) D).hom

/-- The remaining common-affine API law: pullback of the pairwise model is the independently
constructed direct comparison on the smaller common affine open. -/
def PairwiseCommonAffinePullbackCompatibility
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b) : Prop :=
  localLineBundlePairwiseModelHomOnCommonAffine
      K X f U hnonempty hcover hU h D a b W hWab =
    localLineBundleDirectModelHomOnCommonAffine
      K X f U hnonempty hcover hU h D a b W hW hWab

/-- Once the common-affine compatibility law is supplied, the pairwise model pulled along the
composite is the direct common-affine comparison pulled along the same map. -/
theorem pairwiseModelPullHom_eq_directPullHom_of_compatibility
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ (coordinateCover U hcover hU).X a)
    (q_b : Y ⟶ (coordinateCover U hcover hU).X b)
    (hgₐ :
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hgPairₐ :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b)
    (hcompat : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a b W hW hWab) :
    let hWa : W ≤ U a := hWab.trans inf_le_left
    let hWb : W ≤ U b := hWab.trans inf_le_right
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b hgPairₐ hgPair_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleDirectModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hW hWab)
        g qₐ q_b hgₐ hg_b := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  have hn := pullHom_localLineBundlePairwiseModelHomOnCommonAffine
    K X f U hnonempty hcover hU h D a b W hWab g qₐ q_b hgₐ hg_b hgPairₐ hgPair_b
  have hc := congrArg
    (fun z ↦ pullHom (F := LineBundleDescent.modulesPseudofunctor)
      z g qₐ q_b hgₐ hg_b) hcompat
  exact hn.symm.trans hc

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
