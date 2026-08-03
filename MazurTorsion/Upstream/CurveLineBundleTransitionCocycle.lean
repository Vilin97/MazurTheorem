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

universe u u' v v'

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

private theorem pullHom_comp_same_map
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X₁ X₂ X₃ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {M₃ : F.obj (.mk (.op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (e₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (e₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom e₁₂ g gf₁ gf₂ hgf₁ hgf₂ ≫
      pullHom e₂₃ g gf₂ gf₃ hgf₂ hgf₃ =
      pullHom (e₁₂ ≫ e₂₃) g gf₁ gf₃ hgf₁ hgf₃ := by
  subst gf₁
  subst gf₂
  subst gf₃
  simp [pullHom, Functor.map_comp]

/-- The checked common-affine cocycle remains a cocycle after pullback along any map to that
common affine. -/
theorem pullHom_localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
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
    (D : WeilDivisor (CodimensionOnePoint X))
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (q₁ : Y ⟶ Spec (.of Γ(X, U₁)))
    (q₂ : Y ⟶ Spec (.of Γ(X, U₂)))
    (q₃ : Y ⟶ Spec (.of Γ(X, U₃)))
    (hg₁ :
      letI := restrictionAlgebra X U₁ W hWU₁
      g ≫ extensionMap Γ(X, U₁) Γ(X, W) = q₁)
    (hg₂ :
      letI := restrictionAlgebra X U₂ W hWU₂
      g ≫ extensionMap Γ(X, U₂) Γ(X, W) = q₂)
    (hg₃ :
      letI := restrictionAlgebra X U₃ W hWU₃
      g ≫ extensionMap Γ(X, U₃) Γ(X, W) = q₃) :
    letI := restrictionAlgebra X U₁ W hWU₁
    letI := restrictionAlgebra X U₂ W hWU₂
    letI := restrictionAlgebra X U₃ W hWU₃
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePullbackIsoViaPairwiseIntersection
            K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom
          g q₁ q₂ hg₁ hg₂ ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePullbackIsoViaPairwiseIntersection
            K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom
          g q₂ q₃ hg₂ hg₃ =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₁ U₃ W hU₁ hU₃ hW hWU₁ hWU₃ h₁ h₃ D).hom
        g q₁ q₃ hg₁ hg₃ := by
  letI := restrictionAlgebra X U₁ W hWU₁
  letI := restrictionAlgebra X U₂ W hWU₂
  letI := restrictionAlgebra X U₃ W hWU₃
  calc
    _ = pullHom (F := LineBundleDescent.modulesPseudofunctor)
        ((localLineBundlePullbackIsoViaPairwiseIntersection
              K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom ≫
          (localLineBundlePullbackIsoViaPairwiseIntersection
              K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom)
        g q₁ q₃ hg₁ hg₃ := by
      exact pullHom_comp_same_map
        (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₁ U₂ W hU₁ hU₂ hW hWU₁ hWU₂ h₁ h₂ D).hom
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₂ U₃ W hU₂ hU₃ hW hWU₂ hWU₃ h₂ h₃ D).hom
        g q₁ q₂ q₃ hg₁ hg₂ hg₃
    _ = pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f U₁ U₃ W hU₁ hU₃ hW hWU₁ hWU₃ h₁ h₃ D).hom
        g q₁ q₃ hg₁ hg₃ := by
      exact congrArg
        (fun z ↦ pullHom (F := LineBundleDescent.modulesPseudofunctor)
          z g q₁ q₃ hg₁ hg₃)
        (localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
          K X f U₁ U₂ U₃ W hU₁ hU₂ hU₃ hW hWU₁ hWU₂ hWU₃ h₁ h₂ h₃ D)

private theorem pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWa : W ≤ U a) (hWb : W ≤ U b) (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ Spec (.of Γ(X, U a)))
    (q_b : Y ⟶ Spec (.of Γ(X, U b)))
    (hgₐ :
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b) :
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleDirectModelHomOnCommonAffine
          K X f U hnonempty hcover hU h D a b W hW hWab)
        g qₐ q_b hgₐ hg_b =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePullbackIsoViaPairwiseIntersection
          K X f (U a) (U b) W (hU a) (hU b) hW hWa hWb (h a) (h b) D).hom
        g qₐ q_b hgₐ hg_b := by
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  rfl

/-- The three pairwise models form a cocycle after arbitrary further pullback once their three
common-affine compatibility predicates are supplied.  Thus the compatibility predicates are the
only remaining inputs between the checked pairwise transitions and the checked common-affine
cocycle. -/
theorem pairwiseModelPullHom_cocycle_of_compatibilities
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b c : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
    (hWa : W ≤ U a) (hWb : W ≤ U b) (hWc : W ≤ U c)
    (hWab : W ≤ U a ⊓ U b) (hWbc : W ≤ U b ⊓ U c)
    (hWac : W ≤ U a ⊓ U c)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ Spec (.of Γ(X, U a)))
    (q_b : Y ⟶ Spec (.of Γ(X, U b)))
    (q_c : Y ⟶ Spec (.of Γ(X, U c)))
    (hgₐ :
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hg_c :
      letI := restrictionAlgebra X (U c) W hWc
      g ≫ extensionMap Γ(X, U c) Γ(X, W) = q_c)
    (hgPair_ab_a :
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = qₐ)
    (hgPair_ab_b :
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U b) W hWab
      (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q_b)
    (hgPair_bc_b :
      letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
      letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
      (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U b) Γ(X, U b ⊓ U c) = q_b)
    (hgPair_bc_c :
      letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
      letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
      (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U c) Γ(X, U b ⊓ U c) = q_c)
    (hgPair_ac_a :
      letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
      letI := restrictionAlgebra X (U a ⊓ U c) W hWac
      (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U a) Γ(X, U a ⊓ U c) = qₐ)
    (hgPair_ac_c :
      letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
      letI := restrictionAlgebra X (U a ⊓ U c) W hWac
      (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) ≫
        extensionMap Γ(X, U c) Γ(X, U a ⊓ U c) = q_c)
    (hcompat_ab : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a b W hW hWab)
    (hcompat_bc : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D b c W hW hWbc)
    (hcompat_ac : PairwiseCommonAffinePullbackCompatibility
      K X f U hnonempty hcover hU h D a c W hW hWac) :
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hWab
    letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
    letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
    letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
    letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
    letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U c) W hWac
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    letI := restrictionAlgebra X (U c) W hWc
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D a b).hom
          (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W))
          qₐ q_b hgPair_ab_a hgPair_ab_b ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D b c).hom
          (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W))
          q_b q_c hgPair_bc_b hgPair_bc_c =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a c).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W))
        qₐ q_c hgPair_ac_a hgPair_ac_c := by
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U b) (U b ⊓ U c) inf_le_left
  letI := restrictionAlgebra X (U c) (U b ⊓ U c) inf_le_right
  letI := restrictionAlgebra X (U b ⊓ U c) W hWbc
  letI := restrictionAlgebra X (U a) (U a ⊓ U c) inf_le_left
  letI := restrictionAlgebra X (U c) (U a ⊓ U c) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U c) W hWac
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  letI := restrictionAlgebra X (U c) W hWc
  rw [pairwiseModelPullHom_eq_directPullHom_of_compatibility
      K X f U hnonempty hcover hU h D a b W hW hWab
      g qₐ q_b hgₐ hg_b hgPair_ab_a hgPair_ab_b hcompat_ab,
    pairwiseModelPullHom_eq_directPullHom_of_compatibility
      K X f U hnonempty hcover hU h D b c W hW hWbc
      g q_b q_c hg_b hg_c hgPair_bc_b hgPair_bc_c hcompat_bc,
    pairwiseModelPullHom_eq_directPullHom_of_compatibility
      K X f U hnonempty hcover hU h D a c W hW hWac
      g qₐ q_c hgₐ hg_c hgPair_ac_a hgPair_ac_c hcompat_ac]
  rw [pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
      K X f U hnonempty hcover hU h D a b W hW hWa hWb hWab
      g qₐ q_b hgₐ hg_b,
    pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
      K X f U hnonempty hcover hU h D b c W hW hWb hWc hWbc
      g q_b q_c hg_b hg_c,
    pullHom_localLineBundleDirectModelHomOnCommonAffine_eq_viaPairwise
      K X f U hnonempty hcover hU h D a c W hW hWa hWc hWac
      g qₐ q_c hgₐ hg_c]
  exact pullHom_localLineBundlePullbackIsoViaPairwiseIntersection_hom_trans
    K X f (U a) (U b) (U c) W (hU a) (hU b) (hU c) hW
      hWa hWb hWc (h a) (h b) (h c) D g qₐ q_b q_c hgₐ hg_b hg_c

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
