/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleNormalizedTransition

/-!
# Named transition morphisms on a triple chart overlap

The raw transported overlap transitions and their common-affine presentations have large
definitional normal forms.  This file gives each face a separately elaborated opaque name before
assembling the three faces.  The resulting cocycle theorem therefore depends on the checked
one-face comparisons and common-affine cocycle without unfolding all three constructions at once.
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

private theorem comp_eq_of_eq
    {C : Type*} [Category C] {A B C' : C}
    {f f' : A ⟶ B} {g g' : B ⟶ C'} {h h' : A ⟶ C'}
    (hf : f = f') (hg : g = g') (hh : h = h') (hcocycle : f' ≫ g' = h') :
    f ≫ g = h := by
  subst f'
  subst g'
  subst h'
  exact hcocycle

private theorem comp_eq_of_eq_after_cocycle
    {C : Type*} [Category C] {A B C' : C}
    {f f' : A ⟶ B} {g g' : B ⟶ C'} {h h' : A ⟶ C'}
    (hcocycle : f' ≫ g' = h') (hf : f = f') (hg : g = g') (hh : h = h') :
    f ≫ g = h :=
  comp_eq_of_eq hf hg hh hcocycle


/-- The divisor module on chart `i`, pulled directly to the chosen triple overlap. -/
noncomputable abbrev localLineBundleTripleModule₁
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback.Modules :=
  (Scheme.Modules.pullback
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁).obj
    (localLineBundles X U hnonempty hcover hU h D i).obj

/-- The divisor module on chart `j`, pulled directly to the chosen triple overlap. -/
noncomputable abbrev localLineBundleTripleModule₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback.Modules :=
  (Scheme.Modules.pullback
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂).obj
    (localLineBundles X U hnonempty hcover hU h D j).obj

/-- The divisor module on chart `k`, pulled directly to the chosen triple overlap. -/
noncomputable abbrev localLineBundleTripleModule₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback.Modules :=
  (Scheme.Modules.pullback
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₃).obj
    (localLineBundles X U hnonempty hcover hU h D k).obj


/-- The chosen `(i,j)` transition pulled to the `12` face of the chosen triple overlap. -/
noncomputable def localLineBundleRawTransition₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₁ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₂ K X f U hnonempty hcover hU h D i j k :=
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j)
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂_p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂_p₂

/-- The chosen `(j,k)` transition pulled to the `23` face of the chosen triple overlap. -/
noncomputable def localLineBundleRawTransition₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₂ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₃ K X f U hnonempty hcover hU h D i j k :=
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D j k)
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃_p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃_p₃

/-- The chosen `(i,k)` transition pulled to the `13` face of the chosen triple overlap. -/
noncomputable def localLineBundleRawTransition₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₁ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₃ K X f U hnonempty hcover hU h D i j k :=
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i k)
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃_p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃_p₃


/-- The direct common-affine presentation of the `12` transition. -/
noncomputable def localLineBundleDirectTransition₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₁ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₂ K X f U hnonempty hcover hU h D i j k := by
  let W := (U i ⊓ U j) ⊓ U k
  let hWi : W ≤ U i := inf_le_left.trans inf_le_left
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWij : W ≤ U i ⊓ U j := inf_le_left
  let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
  let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
  let hgᵢ := tripleOverlapComparisonToIntersection_comp_first
    K X f U hcover hU i j k
  let hgⱼ := tripleOverlapComparisonToIntersection_comp_second
    K X f U hcover hU i j k
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U j) W hWij
  letI := restrictionAlgebra X (U i) W hWi
  letI := restrictionAlgebra X (U j) W hWj
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j).hom
    (g ≫ extensionMap Γ(X, U i ⊓ U j) Γ(X, W)) T.p₁ T.p₂
    (pairwiseCompositeLeftEqOfDirect X (U i) (U j) W hWij g T.p₁ hgᵢ)
    (pairwiseCompositeRightEqOfDirect X (U i) (U j) W hWij g T.p₂ hgⱼ)

/-- The direct common-affine presentation of the `23` transition. -/
noncomputable def localLineBundleDirectTransition₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₂ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₃ K X f U hnonempty hcover hU h D i j k := by
  let W := (U i ⊓ U j) ⊓ U k
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWk : W ≤ U k := inf_le_right
  let hWjk : W ≤ U j ⊓ U k := le_inf hWj hWk
  let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
  let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
  let hgⱼ := tripleOverlapComparisonToIntersection_comp_second
    K X f U hcover hU i j k
  let hgₖ := tripleOverlapComparisonToIntersection_comp_third
    K X f U hcover hU i j k
  letI := restrictionAlgebra X (U j) (U j ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
  letI := restrictionAlgebra X (U j) W hWj
  letI := restrictionAlgebra X (U k) W hWk
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D j k).hom
    (g ≫ extensionMap Γ(X, U j ⊓ U k) Γ(X, W)) T.p₂ T.p₃
    (pairwiseCompositeLeftEqOfDirect X (U j) (U k) W hWjk g T.p₂ hgⱼ)
    (pairwiseCompositeRightEqOfDirect X (U j) (U k) W hWjk g T.p₃ hgₖ)

/-- The direct common-affine presentation of the `13` transition. -/
noncomputable def localLineBundleDirectTransition₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₁ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₃ K X f U hnonempty hcover hU h D i j k := by
  let W := (U i ⊓ U j) ⊓ U k
  let hWi : W ≤ U i := inf_le_left.trans inf_le_left
  let hWk : W ≤ U k := inf_le_right
  let hWik : W ≤ U i ⊓ U k := le_inf hWi hWk
  let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
  let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
  let hgᵢ := tripleOverlapComparisonToIntersection_comp_first
    K X f U hcover hU i j k
  let hgₖ := tripleOverlapComparisonToIntersection_comp_third
    K X f U hcover hU i j k
  letI := restrictionAlgebra X (U i) (U i ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U i ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U k) W hWik
  letI := restrictionAlgebra X (U i) W hWi
  letI := restrictionAlgebra X (U k) W hWk
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i k).hom
    (g ≫ extensionMap Γ(X, U i ⊓ U k) Γ(X, W)) T.p₁ T.p₃
    (pairwiseCompositeLeftEqOfDirect X (U i) (U k) W hWik g T.p₁ hgᵢ)
    (pairwiseCompositeRightEqOfDirect X (U i) (U k) W hWik g T.p₃ hgₖ)

/-- The raw `12` transition is the direct common-affine transition. -/
theorem localLineBundleRawTransition₁₂_eq_direct
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleRawTransition₁₂
        K X f U hnonempty hcover hU h D i j k =
      localLineBundleDirectTransition₁₂
        K X f U hnonempty hcover hU h D i j k := by
  unfold localLineBundleRawTransition₁₂ localLineBundleDirectTransition₁₂
  rw [pullHom_localLineBundleChosenOverlapHom_comp_pairwise₁₂]
  exact pairwiseModelOnTripleIntersection_eq_direct₁₂
    K X f U hnonempty hcover hU h D i j k

/-- The raw `23` transition is the direct common-affine transition. -/
theorem localLineBundleRawTransition₂₃_eq_direct
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleRawTransition₂₃
        K X f U hnonempty hcover hU h D i j k =
      localLineBundleDirectTransition₂₃
        K X f U hnonempty hcover hU h D i j k := by
  unfold localLineBundleRawTransition₂₃ localLineBundleDirectTransition₂₃
  rw [pullHom_localLineBundleChosenOverlapHom_comp_pairwise₂₃]
  exact pairwiseModelOnTripleIntersection_eq_direct₂₃
    K X f U hnonempty hcover hU h D i j k

/-- The raw `13` transition is the direct common-affine transition. -/
theorem localLineBundleRawTransition₁₃_eq_direct
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleRawTransition₁₃
        K X f U hnonempty hcover hU h D i j k =
      localLineBundleDirectTransition₁₃
        K X f U hnonempty hcover hU h D i j k := by
  unfold localLineBundleRawTransition₁₃ localLineBundleDirectTransition₁₃
  rw [pullHom_localLineBundleChosenOverlapHom_comp_pairwise₁₃]
  exact pairwiseModelOnTripleIntersection_eq_direct₁₃
    K X f U hnonempty hcover hU h D i j k

/-- The opaque direct `12` name unfolds to the common-affine presentation in one isolated
elaboration command. -/
theorem localLineBundleDirectTransition₁₂_eq_explicit
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
    let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
    let hgᵢ := tripleOverlapComparisonToIntersection_comp_first
      K X f U hcover hU i j k
    let hgⱼ := tripleOverlapComparisonToIntersection_comp_second
      K X f U hcover hU i j k
    letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
    letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U j) W hWij
    letI := restrictionAlgebra X (U i) W hWi
    letI := restrictionAlgebra X (U j) W hWj
    localLineBundleDirectTransition₁₂
        K X f U hnonempty hcover hU h D i j k =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j).hom
        (g ≫ extensionMap Γ(X, U i ⊓ U j) Γ(X, W)) T.p₁ T.p₂
        (pairwiseCompositeLeftEqOfDirect X (U i) (U j) W hWij g T.p₁ hgᵢ)
        (pairwiseCompositeRightEqOfDirect X (U i) (U j) W hWij g T.p₂ hgⱼ) := by
  rfl

/-- The opaque direct `23` name unfolds to the common-affine presentation in one isolated
elaboration command. -/
theorem localLineBundleDirectTransition₂₃_eq_explicit
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
    let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
    let hgⱼ := tripleOverlapComparisonToIntersection_comp_second
      K X f U hcover hU i j k
    let hgₖ := tripleOverlapComparisonToIntersection_comp_third
      K X f U hcover hU i j k
    letI := restrictionAlgebra X (U j) (U j ⊓ U k) inf_le_left
    letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
    letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
    letI := restrictionAlgebra X (U j) W hWj
    letI := restrictionAlgebra X (U k) W hWk
    localLineBundleDirectTransition₂₃
        K X f U hnonempty hcover hU h D i j k =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D j k).hom
        (g ≫ extensionMap Γ(X, U j ⊓ U k) Γ(X, W)) T.p₂ T.p₃
        (pairwiseCompositeLeftEqOfDirect X (U j) (U k) W hWjk g T.p₂ hgⱼ)
        (pairwiseCompositeRightEqOfDirect X (U j) (U k) W hWjk g T.p₃ hgₖ) := by
  rfl

/-- The opaque direct `13` name unfolds to the common-affine presentation in one isolated
elaboration command. -/
theorem localLineBundleDirectTransition₁₃_eq_explicit
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
    let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
    let hgᵢ := tripleOverlapComparisonToIntersection_comp_first
      K X f U hcover hU i j k
    let hgₖ := tripleOverlapComparisonToIntersection_comp_third
      K X f U hcover hU i j k
    letI := restrictionAlgebra X (U i) (U i ⊓ U k) inf_le_left
    letI := restrictionAlgebra X (U k) (U i ⊓ U k) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U k) W hWik
    letI := restrictionAlgebra X (U i) W hWi
    letI := restrictionAlgebra X (U k) W hWk
    localLineBundleDirectTransition₁₃
        K X f U hnonempty hcover hU h D i j k =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i k).hom
        (g ≫ extensionMap Γ(X, U i ⊓ U k) Γ(X, W)) T.p₁ T.p₃
        (pairwiseCompositeLeftEqOfDirect X (U i) (U k) W hWik g T.p₁ hgᵢ)
        (pairwiseCompositeRightEqOfDirect X (U i) (U k) W hWik g T.p₃ hgₖ) := by
  rfl

/-- The three named common-affine transitions satisfy the cocycle law. -/
theorem localLineBundleDirectTransition_cocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleDirectTransition₁₂
          K X f U hnonempty hcover hU h D i j k ≫
        localLineBundleDirectTransition₂₃
          K X f U hnonempty hcover hU h D i j k =
      localLineBundleDirectTransition₁₃
        K X f U hnonempty hcover hU h D i j k := by
  let W := (U i ⊓ U j) ⊓ U k
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hW : IsAffineOpen W := ((hU i).inf (hU j)).inf (hU k)
  let hWi : W ≤ U i := inf_le_left.trans inf_le_left
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWk : W ≤ U k := inf_le_right
  let hWij : W ≤ U i ⊓ U j := inf_le_left
  let hWjk : W ≤ U j ⊓ U k := le_inf hWj hWk
  let hWik : W ≤ U i ⊓ U k := le_inf hWi hWk
  letI : Nonempty (U i) := hnonempty i
  letI : Nonempty (U j) := hnonempty j
  letI : Nonempty (U k) := hnonempty k
  letI : Nonempty (U i ⊓ U j : X.Opens) :=
    nonempty_inf_of_isIntegral X (U i) (U j)
  letI : Nonempty W := nonempty_inf_of_isIntegral X (U i ⊓ U j) (U k)
  let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
  let T := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k
  apply comp_eq_of_eq_after_cocycle
    (pairwiseModelPullHom_cocycle_of_directProjections
      K X f U hnonempty hcover hU h D i j k W hW hWi hWj hWk
        hWij hWjk hWik g T.p₁ T.p₂ T.p₃
        (tripleOverlapComparisonToIntersection_comp_first
          K X f U hcover hU i j k)
        (tripleOverlapComparisonToIntersection_comp_second
          K X f U hcover hU i j k)
        (tripleOverlapComparisonToIntersection_comp_third
          K X f U hcover hU i j k))
  · exact localLineBundleDirectTransition₁₂_eq_explicit
      K X f U hnonempty hcover hU h D i j k
  · exact localLineBundleDirectTransition₂₃_eq_explicit
      K X f U hnonempty hcover hU h D i j k
  · exact localLineBundleDirectTransition₁₃_eq_explicit
      K X f U hnonempty hcover hU h D i j k

/-- The three raw chosen-overlap transitions satisfy the cocycle law on the chosen triple
overlap. -/
theorem localLineBundleRawTransition_cocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleRawTransition₁₂
          K X f U hnonempty hcover hU h D i j k ≫
        localLineBundleRawTransition₂₃
          K X f U hnonempty hcover hU h D i j k =
      localLineBundleRawTransition₁₃
        K X f U hnonempty hcover hU h D i j k := by
  apply comp_eq_of_eq_after_cocycle
    (localLineBundleDirectTransition_cocycle
      K X f U hnonempty hcover hU h D i j k)
  · exact localLineBundleRawTransition₁₂_eq_direct
      K X f U hnonempty hcover hU h D i j k
  · exact localLineBundleRawTransition₂₃_eq_direct
      K X f U hnonempty hcover hU h D i j k
  · exact localLineBundleRawTransition₁₃_eq_direct
      K X f U hnonempty hcover hU h D i j k

/-- The full raw chosen-overlap cocycle, stated directly in the `pullHom` API consumed by
line-bundle descent. -/
theorem localLineBundleChosenOverlapHom_raw_cocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundleChosenOverlapHomOnProperSmoothCurve
            K X f U hnonempty hcover hU h D i j)
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₂
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₂_p₁
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₂_p₂ ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundleChosenOverlapHomOnProperSmoothCurve
            K X f U hnonempty hcover hU h D j k)
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂₃
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₃
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂₃_p₂
          (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂₃_p₃ =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i k)
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁₃
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₃
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁₃_p₁
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁₃_p₃ := by
  apply comp_eq_of_eq_after_cocycle
    (localLineBundleRawTransition_cocycle
      K X f U hnonempty hcover hU h D i j k)
  · rfl
  · rfl
  · rfl

/-- The normalized `(i,j)` transition pulled to the `12` face. -/
noncomputable def localLineBundleNormalizedTransition₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₁ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₂ K X f U hnonempty hcover hU h D i j k :=
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j).hom
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂_p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂_p₂

/-- Off the diagonal, the normalized `12` transition is the raw chosen transition. -/
theorem localLineBundleNormalizedTransition₁₂_eq_raw
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) (hij : i ≠ j) :
    localLineBundleNormalizedTransition₁₂
        K X f U hnonempty hcover hU h D i j k =
      localLineBundleRawTransition₁₂
        K X f U hnonempty hcover hU h D i j k := by
  unfold localLineBundleNormalizedTransition₁₂ localLineBundleRawTransition₁₂
  exact pullHom_localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_of_ne
    K X f U hnonempty hcover hU h D i j hij
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂_p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₂_p₂

/-- The normalized `(j,k)` transition pulled to the `23` face. -/
noncomputable def localLineBundleNormalizedTransition₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₂ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₃ K X f U hnonempty hcover hU h D i j k :=
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D j k).hom
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃_p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃_p₃

/-- Off the diagonal, the normalized `23` transition is the raw chosen transition. -/
theorem localLineBundleNormalizedTransition₂₃_eq_raw
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) (hjk : j ≠ k) :
    localLineBundleNormalizedTransition₂₃
        K X f U hnonempty hcover hU h D i j k =
      localLineBundleRawTransition₂₃
        K X f U hnonempty hcover hU h D i j k := by
  unfold localLineBundleNormalizedTransition₂₃ localLineBundleRawTransition₂₃
  exact pullHom_localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_of_ne
    K X f U hnonempty hcover hU h D j k hjk
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃_p₂
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂₃_p₃

/-- The normalized `(i,k)` transition pulled to the `13` face. -/
noncomputable def localLineBundleNormalizedTransition₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    localLineBundleTripleModule₁ K X f U hnonempty hcover hU h D i j k ⟶
      localLineBundleTripleModule₃ K X f U hnonempty hcover hU h D i j k :=
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i k).hom
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃_p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃_p₃

/-- Off the diagonal, the normalized `13` transition is the raw chosen transition. -/
theorem localLineBundleNormalizedTransition₁₃_eq_raw
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) (hik : i ≠ k) :
    localLineBundleNormalizedTransition₁₃
        K X f U hnonempty hcover hU h D i j k =
      localLineBundleRawTransition₁₃
        K X f U hnonempty hcover hU h D i j k := by
  unfold localLineBundleNormalizedTransition₁₃ localLineBundleRawTransition₁₃
  exact pullHom_localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_of_ne
    K X f U hnonempty hcover hU h D i k hik
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃_p₁
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁₃_p₃

/-- The normalized transitions satisfy the triple cocycle whenever all three faces are
off-diagonal.  Diagonal cases require the separate coherent self-overlap comparison. -/
theorem localLineBundleNormalizedTransition_cocycle_of_pairwise_ne
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    localLineBundleNormalizedTransition₁₂
          K X f U hnonempty hcover hU h D i j k ≫
        localLineBundleNormalizedTransition₂₃
          K X f U hnonempty hcover hU h D i j k =
      localLineBundleNormalizedTransition₁₃
        K X f U hnonempty hcover hU h D i j k := by
  apply comp_eq_of_eq_after_cocycle
    (localLineBundleRawTransition_cocycle
      K X f U hnonempty hcover hU h D i j k)
  · exact localLineBundleNormalizedTransition₁₂_eq_raw
      K X f U hnonempty hcover hU h D i j k hij
  · exact localLineBundleNormalizedTransition₂₃_eq_raw
      K X f U hnonempty hcover hU h D i j k hjk
  · exact localLineBundleNormalizedTransition₁₃_eq_raw
      K X f U hnonempty hcover hU h D i j k hik

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
