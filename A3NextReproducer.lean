import MazurTorsion.Upstream.CurveLineBundleTransitionCocycle

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

theorem triple_comp_first_test
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

theorem triple_comp_second_test
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

theorem triple_comp_third_test
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

theorem pairwise_composite_left_eq_of_direct_test
    (X : Scheme.{u}) (U₁ U₂ W : X.Opens)
    (hW₁₂ : W ≤ U₁ ⊓ U₂)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (q₁ : Y ⟶ Spec (.of Γ(X, U₁)))
    (hg₁ :
      let hW₁ : W ≤ U₁ := hW₁₂.trans inf_le_left
      letI := restrictionAlgebra X U₁ W hW₁
      g ≫ extensionMap Γ(X, U₁) Γ(X, W) = q₁) :
    let hW₁ : W ≤ U₁ := hW₁₂.trans inf_le_left
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
    restrictionExtensionMap_comp X U₁ (U₁ ⊓ U₂) W inf_le_left hW₁₂ hW₁]
  exact hg₁

theorem pairwise_composite_right_eq_of_direct_test
    (X : Scheme.{u}) (U₁ U₂ W : X.Opens)
    (hW₁₂ : W ≤ U₁ ⊓ U₂)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (q₂ : Y ⟶ Spec (.of Γ(X, U₂)))
    (hg₂ :
      let hW₂ : W ≤ U₂ := hW₁₂.trans inf_le_right
      letI := restrictionAlgebra X U₂ W hW₂
      g ≫ extensionMap Γ(X, U₂) Γ(X, W) = q₂) :
    let hW₂ : W ≤ U₂ := hW₁₂.trans inf_le_right
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
    restrictionExtensionMap_comp X U₂ (U₁ ⊓ U₂) W inf_le_right hW₁₂ hW₂]
  exact hg₂

theorem pairwiseModelPullHom_cocycle_of_direct_projections_test
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
          (pairwise_composite_left_eq_of_direct_test
            X (U a) (U b) W hWab g qₐ hgₐ)
          (pairwise_composite_right_eq_of_direct_test
            X (U a) (U b) W hWab g q_b hg_b) ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
            K X f U hnonempty hcover hU h D b c).hom
          (g ≫ extensionMap Γ(X, U b ⊓ U c) Γ(X, W)) q_b q_c
          (pairwise_composite_left_eq_of_direct_test
            X (U b) (U c) W hWbc g q_b hg_b)
          (pairwise_composite_right_eq_of_direct_test
            X (U b) (U c) W hWbc g q_c hg_c) =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a c).hom
        (g ≫ extensionMap Γ(X, U a ⊓ U c) Γ(X, W)) qₐ q_c
        (pairwise_composite_left_eq_of_direct_test
          X (U a) (U c) W hWac g qₐ hgₐ)
        (pairwise_composite_right_eq_of_direct_test
          X (U a) (U c) W hWac g q_c hg_c) := by
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
    K X f U hnonempty hcover hU h D a b c W hW hWa hWb hWc hWab hWbc hWac
      g qₐ q_b q_c hgₐ hg_b hg_c
      (pairwise_composite_left_eq_of_direct_test
        X (U a) (U b) W hWab g qₐ hgₐ)
      (pairwise_composite_right_eq_of_direct_test
        X (U a) (U b) W hWab g q_b hg_b)
      (pairwise_composite_left_eq_of_direct_test
        X (U b) (U c) W hWbc g q_b hg_b)
      (pairwise_composite_right_eq_of_direct_test
        X (U b) (U c) W hWbc g q_c hg_c)
      (pairwise_composite_left_eq_of_direct_test
        X (U a) (U c) W hWac g qₐ hgₐ)
      (pairwise_composite_right_eq_of_direct_test
        X (U a) (U c) W hWac g q_c hg_c)

/-
private def pairwisePullHomOnTripleIntersectionCocycleProp
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) : Prop :=
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  let hWi : W ≤ U i := inf_le_left.trans inf_le_left
  let hWj : W ≤ U j := inf_le_left.trans inf_le_right
  let hWk : W ≤ U k := inf_le_right
  let hWij : W ≤ U i ⊓ U j := inf_le_left
  let hWjk : W ≤ U j ⊓ U k := le_inf hWj hWk
  let hWik : W ≤ U i ⊓ U k := le_inf hWi hWk
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U j) W hWij
  letI := restrictionAlgebra X (U j) (U j ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
  letI := restrictionAlgebra X (U i) (U i ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U i ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U k) W hWik
  letI := restrictionAlgebra X (U i) W hWi
  letI := restrictionAlgebra X (U j) W hWj
  letI := restrictionAlgebra X (U k) W hWk
  let g := tripleOverlapComparisonToIntersection K X f U hcover hU i j k
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  let hg₁ := triple_comp_first_test K X f U hcover hU i j k
  let hg₂ := triple_comp_second_test K X f U hcover hU i j k
  let hg₃ := triple_comp_third_test K X f U hcover hU i j k
  pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j).hom
        (g ≫ extensionMap Γ(X, U i ⊓ U j) Γ(X, W)) T.p₁ T.p₂
        (pairwise_composite_left_eq_of_direct_test
          X (U i) (U j) W hWij g T.p₁ hg₁)
        (pairwise_composite_right_eq_of_direct_test
          X (U i) (U j) W hWij g T.p₂ hg₂) ≫
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D j k).hom
        (g ≫ extensionMap Γ(X, U j ⊓ U k) Γ(X, W)) T.p₂ T.p₃
        (pairwise_composite_left_eq_of_direct_test
          X (U j) (U k) W hWjk g T.p₂ hg₂)
        (pairwise_composite_right_eq_of_direct_test
          X (U j) (U k) W hWjk g T.p₃ hg₃) =
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
      (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i k).hom
      (g ≫ extensionMap Γ(X, U i ⊓ U k) Γ(X, W)) T.p₁ T.p₃
      (pairwise_composite_left_eq_of_direct_test
        X (U i) (U k) W hWik g T.p₁ hg₁)
      (pairwise_composite_right_eq_of_direct_test
        X (U i) (U k) W hWik g T.p₃ hg₃)

private theorem pairwisePullHomOnTripleIntersection_cocycle_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    pairwisePullHomOnTripleIntersectionCocycleProp
      K X f U hnonempty hcover hU h D i j k := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
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
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U j) W hWij
  letI := restrictionAlgebra X (U j) (U j ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
  letI := restrictionAlgebra X (U i) (U i ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U i ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U k) W hWik
  letI := restrictionAlgebra X (U i) W hWi
  letI := restrictionAlgebra X (U j) W hWj
  letI := restrictionAlgebra X (U k) W hWk
  unfold pairwisePullHomOnTripleIntersectionCocycleProp
  dsimp only
  exact pairwiseModelPullHom_cocycle_of_direct_projections_test
    K X f U hnonempty hcover hU h D i j k W hW hWi hWj hWk hWij hWjk hWik
      (tripleOverlapComparisonToIntersection K X f U hcover hU i j k)
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₂
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₃
      (triple_comp_first_test K X f U hcover hU i j k)
      (triple_comp_second_test K X f U hcover hU i j k)
      (triple_comp_third_test K X f U hcover hU i j k)
-/

private noncomputable def triplePairwiseModelHom₁₂_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    (Scheme.Modules.pullback T.p₁).obj
          (localLineBundles X U hnonempty hcover hU h D i).obj ⟶
      (Scheme.Modules.pullback T.p₂).obj
        (localLineBundles X U hnonempty hcover hU h D j).obj := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  letI := restrictionAlgebra X (U i ⊓ U j) W inf_le_left
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  exact localLineBundlePairwiseModelHomOnTripleIntersection
    K X f U hnonempty hcover hU h D i j k i j inf_le_left T.p₁ T.p₂
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
        exact T.p₁₂_p₁)
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
        exact T.p₁₂_p₂)

private noncomputable def triplePairwiseModelHom₂₃_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    (Scheme.Modules.pullback T.p₂).obj
          (localLineBundles X U hnonempty hcover hU h D j).obj ⟶
      (Scheme.Modules.pullback T.p₃).obj
        (localLineBundles X U hnonempty hcover hU h D k).obj := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  let hWjk : W ≤ U j ⊓ U k :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  exact localLineBundlePairwiseModelHomOnTripleIntersection
    K X f U hnonempty hcover hU h D i j k j k hWjk T.p₂ T.p₃
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
        exact T.p₂₃_p₂)
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
        exact T.p₂₃_p₃)

private noncomputable def triplePairwiseModelHom₁₃_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    (Scheme.Modules.pullback T.p₁).obj
          (localLineBundles X U hnonempty hcover hU h D i).obj ⟶
      (Scheme.Modules.pullback T.p₃).obj
        (localLineBundles X U hnonempty hcover hU h D k).obj := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
  let hWik : W ≤ U i ⊓ U k :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U k) W hWik
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  exact localLineBundlePairwiseModelHomOnTripleIntersection
    K X f U hnonempty hcover hU h D i j k i k hWik T.p₁ T.p₃
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
        exact T.p₁₃_p₁)
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
        exact T.p₁₃_p₃)

/-
private theorem triplePairwiseModelHom_cocycle_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    triplePairwiseModelHom₁₂_test
          K X f U hnonempty hcover hU h D i j k ≫
        triplePairwiseModelHom₂₃_test
          K X f U hnonempty hcover hU h D i j k =
      triplePairwiseModelHom₁₃_test
        K X f U hnonempty hcover hU h D i j k := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let W := (U i ⊓ U j) ⊓ U k
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
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U j) (U i ⊓ U j) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U j) W hWij
  letI := restrictionAlgebra X (U j) (U j ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U j ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) W hWjk
  letI := restrictionAlgebra X (U i) (U i ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) (U i ⊓ U k) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U k) W hWik
  letI := restrictionAlgebra X (U i) W hWi
  letI := restrictionAlgebra X (U j) W hWj
  letI := restrictionAlgebra X (U k) W hWk
  unfold triplePairwiseModelHom₁₂_test
  unfold triplePairwiseModelHom₂₃_test
  unfold triplePairwiseModelHom₁₃_test
  unfold localLineBundlePairwiseModelHomOnTripleIntersection
  exact pairwiseModelPullHom_cocycle_of_direct_projections_test
    K X f U hnonempty hcover hU h D i j k W hW hWi hWj hWk hWij hWjk hWik
      (tripleOverlapComparisonToIntersection K X f U hcover hU i j k)
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₂
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₃
      (triple_comp_first_test K X f U hcover hU i j k)
      (triple_comp_second_test K X f U hcover hU i j k)
      (triple_comp_third_test K X f U hcover hU i j k)
-/

private noncomputable abbrev pairwiseModelPullHomOfDirectProjections_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b : I)
    (W : X.Opens) (hWab : W ≤ U a ⊓ U b)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Γ(X, W)))
    (qₐ : Y ⟶ Spec (.of Γ(X, U a)))
    (q_b : Y ⟶ Spec (.of Γ(X, U b)))
    (hgₐ :
      let hWa : W ≤ U a := hWab.trans inf_le_left
      letI := restrictionAlgebra X (U a) W hWa
      g ≫ extensionMap Γ(X, U a) Γ(X, W) = qₐ)
    (hg_b :
      let hWb : W ≤ U b := hWab.trans inf_le_right
      letI := restrictionAlgebra X (U b) W hWb
      g ≫ extensionMap Γ(X, U b) Γ(X, W) = q_b) :
    (Scheme.Modules.pullback qₐ).obj
          (localLineBundles X U hnonempty hcover hU h D a).obj ⟶
      (Scheme.Modules.pullback q_b).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  letI := restrictionAlgebra X (U a ⊓ U b) W hWab
  letI := restrictionAlgebra X (U a) W hWa
  letI := restrictionAlgebra X (U b) W hWb
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
    (g ≫ extensionMap Γ(X, U a ⊓ U b) Γ(X, W)) qₐ q_b
    (pairwise_composite_left_eq_of_direct_test
      X (U a) (U b) W hWab g qₐ hgₐ)
    (pairwise_composite_right_eq_of_direct_test
      X (U a) (U b) W hWab g q_b hg_b)

private theorem pairwiseModelPullHomOfDirectProjections_cocycle_test
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (a b c : I)
    (W : X.Opens) [Nonempty W] (hW : IsAffineOpen W)
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
    pairwiseModelPullHomOfDirectProjections_test
          K X f U hnonempty hcover hU h D a b W hWab g qₐ q_b hgₐ hg_b ≫
        pairwiseModelPullHomOfDirectProjections_test
          K X f U hnonempty hcover hU h D b c W hWbc g q_b q_c hg_b hg_c =
      pairwiseModelPullHomOfDirectProjections_test
        K X f U hnonempty hcover hU h D a c W hWac g qₐ q_c hgₐ hg_c := by
  let hWa : W ≤ U a := hWab.trans inf_le_left
  let hWb : W ≤ U b := hWab.trans inf_le_right
  let hWc : W ≤ U c := hWbc.trans inf_le_right
  exact pairwiseModelPullHom_cocycle_of_direct_projections_test
    K X f U hnonempty hcover hU h D a b c W hW hWa hWb hWc hWab hWbc hWac
      g qₐ q_b q_c hgₐ hg_b hg_c

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
