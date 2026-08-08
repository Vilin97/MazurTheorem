/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleTripleProjectionCocycle

/-!
# Opaque pairwise comparisons on a chosen triple overlap

Each theorem in this file specializes one pairwise inverse-ideal model to the direct chart
projections from the chosen triple overlap. They are separated so downstream cocycle assembly
never unfolds all three chosen pullback comparisons simultaneously.
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

/-- The `12` pairwise model agrees with its direct-projection presentation on the chosen triple
overlap. -/
theorem pairwiseModelOnTripleIntersection_eq_direct₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let W := (U i ⊓ U j) ⊓ U k
    let hWi : W ≤ U i := inf_le_left.trans inf_le_left
    let hWj : W ≤ U j := inf_le_left.trans inf_le_right
    let hWij : W ≤ U i ⊓ U j := inf_le_left
    let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    let hgᵢ := tripleOverlapComparisonToIntersection_comp_first
      K X f U hcover hU i j k
    let hgⱼ := tripleOverlapComparisonToIntersection_comp_second
      K X f U hcover hU i j k
    letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
    letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U j) W hWij
    letI := restrictionAlgebra X (U i) W hWi
    letI := restrictionAlgebra X (U j) W hWj
    localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k i j hWij T.p₁ T.p₂
        (pairwiseCompositeLeftEqOfDirect X (U i) (U j) W hWij g T.p₁ hgᵢ)
        (pairwiseCompositeRightEqOfDirect X (U i) (U j) W hWij g T.p₂ hgⱼ) =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j).hom
        (g ≫ extensionMap Γ(X, U i ⊓ U j) Γ(X, W)) T.p₁ T.p₂
        (pairwiseCompositeLeftEqOfDirect X (U i) (U j) W hWij g T.p₁ hgᵢ)
        (pairwiseCompositeRightEqOfDirect X (U i) (U j) W hWij g T.p₂ hgⱼ) := by
  exact localLineBundlePairwiseModelHomOnTripleIntersection_eq_directProjections
    K X f U hnonempty hcover hU h D i j k i j inf_le_left
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₂
      (tripleOverlapComparisonToIntersection_comp_first
        K X f U hcover hU i j k)
      (tripleOverlapComparisonToIntersection_comp_second
        K X f U hcover hU i j k)

/-- The `23` pairwise model agrees with its direct-projection presentation on the chosen triple
overlap. -/
theorem pairwiseModelOnTripleIntersection_eq_direct₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let W := (U i ⊓ U j) ⊓ U k
    let hWj : W ≤ U j := inf_le_left.trans inf_le_right
    let hWk : W ≤ U k := inf_le_right
    let hWjk : W ≤ U j ⊓ U k := le_inf hWj hWk
    let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    let hgⱼ := tripleOverlapComparisonToIntersection_comp_second
      K X f U hcover hU i j k
    let hgₖ := tripleOverlapComparisonToIntersection_comp_third
      K X f U hcover hU i j k
    letI := restrictionAlgebra X (U j) (U j ⊓ U k) inf_le_left
    letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
    letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
    letI := restrictionAlgebra X (U j) W hWj
    letI := restrictionAlgebra X (U k) W hWk
    localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k j k hWjk T.p₂ T.p₃
        (pairwiseCompositeLeftEqOfDirect X (U j) (U k) W hWjk g T.p₂ hgⱼ)
        (pairwiseCompositeRightEqOfDirect X (U j) (U k) W hWjk g T.p₃ hgₖ) =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D j k).hom
        (g ≫ extensionMap Γ(X, U j ⊓ U k) Γ(X, W)) T.p₂ T.p₃
        (pairwiseCompositeLeftEqOfDirect X (U j) (U k) W hWjk g T.p₂ hgⱼ)
        (pairwiseCompositeRightEqOfDirect X (U j) (U k) W hWjk g T.p₃ hgₖ) := by
  exact localLineBundlePairwiseModelHomOnTripleIntersection_eq_directProjections
    K X f U hnonempty hcover hU h D i j k j k
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₂
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₃
      (tripleOverlapComparisonToIntersection_comp_second
        K X f U hcover hU i j k)
      (tripleOverlapComparisonToIntersection_comp_third
        K X f U hcover hU i j k)

/-- The `13` pairwise model agrees with its direct-projection presentation on the chosen triple
overlap. -/
theorem pairwiseModelOnTripleIntersection_eq_direct₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let W := (U i ⊓ U j) ⊓ U k
    let hWi : W ≤ U i := inf_le_left.trans inf_le_left
    let hWk : W ≤ U k := inf_le_right
    let hWik : W ≤ U i ⊓ U k := le_inf hWi hWk
    let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    let hgᵢ := tripleOverlapComparisonToIntersection_comp_first
      K X f U hcover hU i j k
    let hgₖ := tripleOverlapComparisonToIntersection_comp_third
      K X f U hcover hU i j k
    letI := restrictionAlgebra X (U i) (U i ⊓ U k) inf_le_left
    letI := restrictionAlgebra X (U k) (U i ⊓ U k) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U k) W hWik
    letI := restrictionAlgebra X (U i) W hWi
    letI := restrictionAlgebra X (U k) W hWk
    localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k i k hWik T.p₁ T.p₃
        (pairwiseCompositeLeftEqOfDirect X (U i) (U k) W hWik g T.p₁ hgᵢ)
        (pairwiseCompositeRightEqOfDirect X (U i) (U k) W hWik g T.p₃ hgₖ) =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i k).hom
        (g ≫ extensionMap Γ(X, U i ⊓ U k) Γ(X, W)) T.p₁ T.p₃
        (pairwiseCompositeLeftEqOfDirect X (U i) (U k) W hWik g T.p₁ hgᵢ)
        (pairwiseCompositeRightEqOfDirect X (U i) (U k) W hWik g T.p₃ hgₖ) := by
  exact localLineBundlePairwiseModelHomOnTripleIntersection_eq_directProjections
    K X f U hnonempty hcover hU h D i j k i k
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₃
      (tripleOverlapComparisonToIntersection_comp_first
        K X f U hcover hU i j k)
      (tripleOverlapComparisonToIntersection_comp_third
        K X f U hcover hU i j k)

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
