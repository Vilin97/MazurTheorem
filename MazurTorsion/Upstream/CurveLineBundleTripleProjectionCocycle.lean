/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleTransitionCocycle

/-!
# Triple projections for divisor transition cocycles

This file connects the common-affine divisor cocycle to the three canonical chart projections
from Mathlib's chosen triple overlap.  It proves the projection equations and packages the
common-affine cocycle using only those direct projection equations.  Comparing this result with
all three transported chosen-overlap morphisms at once remains a separate elaboration boundary.
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
open scoped AlgebraicGeometry

universe u v

/-- The canonical map from the chosen triple overlap to the actual triple affine intersection,
followed by restriction to the first chart, is the first chosen projection. -/
theorem tripleOverlapComparisonToIntersection_comp_first
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let W := (U i ⊓ U j) ⊓ U k
    let hWi : W ≤ U i := inf_le_left.trans inf_le_left
    letI := restrictionAlgebra X (U i) W hWi
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        extensionMap Γ(X, U i) Γ(X, W) =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁ := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  let hWi : W ≤ U i := inf_le_left.trans inf_le_left
  let hWij : W ≤ U i ⊓ U j := inf_le_left
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U i ⊓ U j) W hWij
  letI := restrictionAlgebra X (U i) W hWi
  dsimp only
  rw [← restrictionExtensionMap_comp X (U i) (U i ⊓ U j) W
    inf_le_left hWij hWi, ← Category.assoc,
    tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
    Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
  exact (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k).p₁₂_p₁

/-- The canonical map from the chosen triple overlap to the actual triple affine intersection,
followed by restriction to the second chart, is the second chosen projection. -/
theorem tripleOverlapComparisonToIntersection_comp_second
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let W := (U i ⊓ U j) ⊓ U k
    let hWj : W ≤ U j := inf_le_left.trans inf_le_right
    letI := restrictionAlgebra X (U j) W hWj
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        extensionMap Γ(X, U j) Γ(X, W) =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₂ := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWij : W ≤ U i ⊓ U j := inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U j) W hWij
  letI := restrictionAlgebra X (U j) W hWj
  dsimp only
  rw [← restrictionExtensionMap_comp X (U j) (U i ⊓ U j) W
    inf_le_right hWij hWj, ← Category.assoc,
    tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
    Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
  exact (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k).p₁₂_p₂

/-- The canonical map from the chosen triple overlap to the actual triple affine intersection,
followed by restriction to the third chart, is the third chosen projection. -/
theorem tripleOverlapComparisonToIntersection_comp_third
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let W := (U i ⊓ U j) ⊓ U k
    let hWk : W ≤ U k := inf_le_right
    letI := restrictionAlgebra X (U k) W hWk
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        extensionMap Γ(X, U k) Γ(X, W) =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₃ := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWk : W ≤ U k := inf_le_right
  let hWjk : W ≤ U j ⊓ U k := le_inf hWj hWk
  letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
  letI := restrictionAlgebra X (U k) W hWk
  dsimp only
  rw [← restrictionExtensionMap_comp X (U k) (U j ⊓ U k) W
    inf_le_right hWjk hWk, ← Category.assoc,
    tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
    Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
  exact (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k).p₂₃_p₃

/-- The three canonical chart projection equations from the chosen triple overlap, packaged as a
single downstream consumer of the individual comparison theorems. -/
theorem tripleOverlapComparisonToIntersection_comp_projections
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    let W := (U i ⊓ U j) ⊓ U k
    let hWi : W ≤ U i := inf_le_left.trans inf_le_left
    let hWj : W ≤ U j := inf_le_left.trans inf_le_right
    let hWk : W ≤ U k := inf_le_right
    letI := restrictionAlgebra X (U i) W hWi
    letI := restrictionAlgebra X (U j) W hWj
    letI := restrictionAlgebra X (U k) W hWk
    let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    g ≫ extensionMap Γ(X, U i) Γ(X, W) = T.p₁ ∧
      g ≫ extensionMap Γ(X, U j) Γ(X, W) = T.p₂ ∧
      g ≫ extensionMap Γ(X, U k) Γ(X, W) = T.p₃ := by
  exact ⟨tripleOverlapComparisonToIntersection_comp_first
      K X f U hcover hU i j k,
    tripleOverlapComparisonToIntersection_comp_second
      K X f U hcover hU i j k,
    tripleOverlapComparisonToIntersection_comp_third
      K X f U hcover hU i j k⟩

/-- A direct projection equation to the left chart implies the corresponding equation through
the pairwise intersection, by functoriality of restriction maps. -/
theorem pairwiseCompositeLeftEqOfDirect
    (X : Scheme.{u}) (U₁ U₂ W : X.Opens)
    (hW₁₂ : W ≤ U₁ ⊓ U₂)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (q₁ : Y ⟶ Spec (.of Γ(X, U₁)))
    (hg₁ :
      let hW₁ : W ≤ U₁ := hW₁₂.trans inf_le_left
      letI := restrictionAlgebra X U₁ W hW₁
      g ≫ extensionMap Γ(X, U₁) Γ(X, W) = q₁) :
    let _hW₁ : W ≤ U₁ := hW₁₂.trans inf_le_left
    letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
    letI := restrictionAlgebra X (U₁ ⊓ U₂) W hW₁₂
    (g ≫ extensionMap Γ(X, U₁ ⊓ U₂) Γ(X, W)) ≫
        extensionMap Γ(X, U₁) Γ(X, U₁ ⊓ U₂) = q₁ := by
  let hW₁ : W ≤ U₁ := hW₁₂.trans inf_le_left
  letI := restrictionAlgebra X U₁ (U₁ ⊓ U₂) inf_le_left
  letI := restrictionAlgebra X (U₁ ⊓ U₂) W hW₁₂
  letI := restrictionAlgebra X U₁ W hW₁
  dsimp only
  rw [Category.assoc,
    restrictionExtensionMap_comp X U₁ (U₁ ⊓ U₂) W
      inf_le_left hW₁₂ hW₁]
  exact hg₁

/-- A direct projection equation to the right chart implies the corresponding equation through
the pairwise intersection, by functoriality of restriction maps. -/
theorem pairwiseCompositeRightEqOfDirect
    (X : Scheme.{u}) (U₁ U₂ W : X.Opens)
    (hW₁₂ : W ≤ U₁ ⊓ U₂)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (q₂ : Y ⟶ Spec (.of Γ(X, U₂)))
    (hg₂ :
      let hW₂ : W ≤ U₂ := hW₁₂.trans inf_le_right
      letI := restrictionAlgebra X U₂ W hW₂
      g ≫ extensionMap Γ(X, U₂) Γ(X, W) = q₂) :
    let _hW₂ : W ≤ U₂ := hW₁₂.trans inf_le_right
    letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
    letI := restrictionAlgebra X (U₁ ⊓ U₂) W hW₁₂
    (g ≫ extensionMap Γ(X, U₁ ⊓ U₂) Γ(X, W)) ≫
        extensionMap Γ(X, U₂) Γ(X, U₁ ⊓ U₂) = q₂ := by
  let hW₂ : W ≤ U₂ := hW₁₂.trans inf_le_right
  letI := restrictionAlgebra X U₂ (U₁ ⊓ U₂) inf_le_right
  letI := restrictionAlgebra X (U₁ ⊓ U₂) W hW₁₂
  letI := restrictionAlgebra X U₂ W hW₂
  dsimp only
  rw [Category.assoc,
    restrictionExtensionMap_comp X U₂ (U₁ ⊓ U₂) W
      inf_le_right hW₁₂ hW₂]
  exact hg₂

/-- The pairwise-model cocycle needs only the three direct projection equations to a common
affine model; the six pairwise composite equations are derived by scalar-tower functoriality. -/
theorem pairwiseModelPullHom_cocycle_of_directProjections
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
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b)
    (hg_c :
      let hWc : W ≤ U c := hWbc.trans inf_le_right
      letI := restrictionAlgebra X (U c) W hWc
      g ≫ extensionMap Γ(X, U c) Γ(X, W) = q_c) :
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
          (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b
          (pairwiseCompositeLeftEqOfDirect X (U a) (U b) W hWab g qₐ hgₐ)
          (pairwiseCompositeRightEqOfDirect X (U a) (U b) W hWab g q_b hg_b) ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D b c).hom
          (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) q_b q_c
          (pairwiseCompositeLeftEqOfDirect X (U b) (U c) W hWbc g q_b hg_b)
          (pairwiseCompositeRightEqOfDirect X (U b) (U c) W hWbc g q_c hg_c) =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a c).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) qₐ q_c
        (pairwiseCompositeLeftEqOfDirect X (U a) (U c) W hWac g qₐ hgₐ)
        (pairwiseCompositeRightEqOfDirect X (U a) (U c) W hWac g q_c hg_c) := by
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
  exact pairwiseModelPullHom_cocycle
    K X f U hnonempty hcover hU h D a b c W hW hWa hWb hWc
      hWab hWbc hWac g qₐ q_b q_c hgₐ hg_b hg_c
      (pairwiseCompositeLeftEqOfDirect X (U a) (U b) W hWab g qₐ hgₐ)
      (pairwiseCompositeRightEqOfDirect X (U a) (U b) W hWab g q_b hg_b)
      (pairwiseCompositeLeftEqOfDirect X (U b) (U c) W hWbc g q_b hg_b)
      (pairwiseCompositeRightEqOfDirect X (U b) (U c) W hWbc g q_c hg_c)
      (pairwiseCompositeLeftEqOfDirect X (U a) (U c) W hWac g qₐ hgₐ)
      (pairwiseCompositeRightEqOfDirect X (U a) (U c) W hWac g q_c hg_c)

/-- A pairwise model on the actual triple intersection is the direct-projection formulation
used by the checked common-affine cocycle. This one-transition boundary stays below the chosen
pullback normalization bottleneck. -/
theorem localLineBundlePairwiseModelHomOnTripleIntersection_eq_directProjections
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k a b : I)
    (hsub : (U i ⊓ U j) ⊓ U k ≤ U a ⊓ U b)
    (qₐ : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (coordinateCover U hcover hU).X a)
    (q_b : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (coordinateCover U hcover hU).X b)
    (hqₐ :
      let W := (U i ⊓ U j) ⊓ U k
      let hWa : W ≤ U a := hsub.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hq_b :
      let W := (U i ⊓ U j) ⊓ U k
      let hWb : W ≤ U b := hsub.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        extensionMap Γ(X, U b) Γ(X, W) = q_b) :
    let W := (U i ⊓ U j) ⊓ U k
    let hWa : W ≤ U a := hsub.trans inf_le_left
    let hWb : W ≤ U b := hsub.trans inf_le_right
    let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
    letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
    letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
    letI := restrictionAlgebra X (U a ⊓ U b) W hsub
    letI := restrictionAlgebra X (U a) W hWa
    letI := restrictionAlgebra X (U b) W hWb
    localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k a b hsub qₐ q_b
        (pairwiseCompositeLeftEqOfDirect X (U a) (U b) W hsub g qₐ hqₐ)
        (pairwiseCompositeRightEqOfDirect X (U a) (U b) W hsub g q_b hq_b) =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b
        (pairwiseCompositeLeftEqOfDirect X (U a) (U b) W hsub g qₐ hqₐ)
        (pairwiseCompositeRightEqOfDirect X (U a) (U b) W hsub g q_b hq_b) := by
  rfl

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
