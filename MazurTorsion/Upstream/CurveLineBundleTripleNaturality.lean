/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleOverlapNaturality
import MazurTorsion.Upstream.CurveLineBundleTripleIntersection

/-!
# Naturality of divisor transitions on triple chart intersections

The arbitrary-divisor transition on a chosen pairwise overlap was constructed by transporting
an explicit inverse-ideal comparison from the spectrum of the actual affine intersection.  This
file proves that pulling that chosen transition through a face of the chosen triple overlap is
the same as pulling the original inverse-ideal comparison through the canonical map to the
actual triple affine intersection.

This is a base-change statement.  It does not yet identify the resulting pullback morphism with
the separately constructed common-affine restriction isomorphism, and consequently does not
claim the full three-transition cocycle.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry

universe u v

private theorem pullHom_eq_of_map_eq
    {X₁ X₂ Y Y' : Scheme.{u}}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶
      (Scheme.Modules.pullback f₂).obj M₂)
    (g g' : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hg₁ : g ≫ f₁ = gf₁) (hg₂ : g ≫ f₂ = gf₂)
    (hg₁' : g' ≫ f₁ = gf₁) (hg₂' : g' ≫ f₂ = gf₂)
    (hgg' : g = g') :
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        φ g gf₁ gf₂ hg₁ hg₂ =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        φ g' gf₁ gf₂ hg₁' hg₂' := by
  subst g'
  rfl

/-- The explicit pairwise inverse-ideal comparison, pulled from its affine pairwise-intersection
model to the actual triple affine intersection and expressed between the requested chart
projections.  The two equations record that the map to the triple intersection has those chart
projections. -/
noncomputable def localLineBundlePairwiseModelHomOnTripleIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k a b : I)
    (hsub : (U i ⊓ U j) ⊓ U k ≤ U a ⊓ U b)
    (q₁ : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (coordinateCover U hcover hU).X a)
    (q₂ : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (coordinateCover U hcover hU).X b)
    (hq₁ :
      letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
      letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
      (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
          CommonExtension.extensionMap
            Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k)) ≫
        CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = q₁)
    (hq₂ :
      letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
      letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
      (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
          CommonExtension.extensionMap
            Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k)) ≫
        CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q₂) :
    (Scheme.Modules.pullback q₁).obj
        (localLineBundles X U hnonempty hcover hU h D a).obj ⟶
      (Scheme.Modules.pullback q₂).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj := by
  letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  exact pullHom (F := LineBundleDescent.modulesPseudofunctor)
    (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
    (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
      CommonExtension.extensionMap
        Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k))
    q₁ q₂ hq₁ hq₂

/-- Pulling a chosen arbitrary-divisor overlap transition through a map from the chosen triple
overlap agrees with pulling its explicit pairwise inverse-ideal model through the canonical map
to the actual triple affine intersection, whenever those two scheme maps agree. -/
theorem pullHom_localLineBundleChosenOverlapHom_eq_pairwiseModelOnTripleIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k a b : I)
    (hsub : (U i ⊓ U j) ⊓ U k ≤ U a ⊓ U b)
    (q : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (LineBundleDescent.overlap (coordinateCover U hcover hU) a b).pullback)
    (q₁ : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (coordinateCover U hcover hU).X a)
    (q₂ : (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).pullback ⟶
        (coordinateCover U hcover hU).X b)
    (hq₁ : q ≫ (LineBundleDescent.overlap
      (coordinateCover U hcover hU) a b).p₁ = q₁)
    (hq₂ : q ≫ (LineBundleDescent.overlap
      (coordinateCover U hcover hU) a b).p₂ = q₂)
    (hmodel :
      letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
      tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
          CommonExtension.extensionMap
            Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k) =
        q ≫ pairwiseOverlapComparisonToIntersection
          K X f U hcover hU a b) :
    letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b)
        q q₁ q₂ hq₁ hq₂ =
      localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k a b hsub q₁ q₂
        (by
          rw [hmodel, Category.assoc,
            pairwiseOverlapComparisonToIntersection_comp_left]
          exact hq₁)
        (by
          rw [hmodel, Category.assoc,
            pairwiseOverlapComparisonToIntersection_comp_right]
          exact hq₂) := by
  letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  letI := restrictionAlgebra X (U a) (U a ⊓ U b) inf_le_left
  letI := restrictionAlgebra X (U b) (U a ⊓ U b) inf_le_right
  let hpb := properCurveIntersectionSpectrumIsPullback
    K X f (U a) (U b) (hU a) (hU b)
  have hp₁ : hpb.isoPullback.inv ≫
      CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) =
        (LineBundleDescent.overlap
          (coordinateCover U hcover hU) a b).p₁ :=
    hpb.isoPullback_inv_fst
  have hp₂ : hpb.isoPullback.inv ≫
      CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) =
        (LineBundleDescent.overlap
          (coordinateCover U hcover hU) a b).p₂ :=
    hpb.isoPullback_inv_snd
  have hg₁ : (q ≫ hpb.isoPullback.inv) ≫
      CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = q₁ := by
    have hassoc : (q ≫ hpb.isoPullback.inv) ≫
        CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) =
      q ≫ (hpb.isoPullback.inv ≫
        CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b)) :=
      Category.assoc _ _ _
    have hcomp : q ≫ (hpb.isoPullback.inv ≫
        CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b)) =
      q ≫ (LineBundleDescent.overlap
        (coordinateCover U hcover hU) a b).p₁ :=
      congrArg (fun z ↦ q ≫ z) hp₁
    exact hassoc.trans (hcomp.trans hq₁)
  have hg₂ : (q ≫ hpb.isoPullback.inv) ≫
      CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q₂ := by
    have hassoc : (q ≫ hpb.isoPullback.inv) ≫
        CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) =
      q ≫ (hpb.isoPullback.inv ≫
        CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b)) :=
      Category.assoc _ _ _
    have hcomp : q ≫ (hpb.isoPullback.inv ≫
        CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b)) =
      q ≫ (LineBundleDescent.overlap
        (coordinateCover U hcover hU) a b).p₂ :=
      congrArg (fun z ↦ q ≫ z) hp₂
    exact hassoc.trans (hcomp.trans hq₂)
  rw [localLineBundleChosenOverlapHomOnProperSmoothCurve_eq_model
    K X f U hnonempty hcover hU h D a b]
  unfold localLineBundlePairwiseModelHomOnTripleIntersection
  calc
    _ = pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (q ≫ hpb.isoPullback.inv) q₁ q₂ hg₁ hg₂ :=
      LineBundleDescent.pullHom_pullbackOverlapHomOfModel
        (hU a).fromSpec (hU b).fromSpec
        (CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b))
        (CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b))
        hpb
        (localLineBundles X U hnonempty hcover hU h D a).obj
        (localLineBundles X U hnonempty hcover hU h D b).obj
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b)
        q q₁ q₂ hq₁ hq₂
    _ = _ := by
      have hg₁' :
          (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
              CommonExtension.extensionMap
                Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k)) ≫
            CommonExtension.extensionMap Γ(X, U a) Γ(X, U a ⊓ U b) = q₁ := by
        rw [hmodel, Category.assoc,
          pairwiseOverlapComparisonToIntersection_comp_left]
        exact hq₁
      have hg₂' :
          (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
              CommonExtension.extensionMap
                Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k)) ≫
            CommonExtension.extensionMap Γ(X, U b) Γ(X, U a ⊓ U b) = q₂ := by
        rw [hmodel, Category.assoc,
          pairwiseOverlapComparisonToIntersection_comp_right]
        exact hq₂
      have hmap : q ≫ hpb.isoPullback.inv =
          tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
            CommonExtension.extensionMap
              Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k) := by
        exact hmodel.symm
      exact pullHom_eq_of_map_eq
        (localLineBundlePairwiseOverlapModelIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom
        (q ≫ hpb.isoPullback.inv)
        (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
          CommonExtension.extensionMap
            Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k))
        q₁ q₂ hg₁ hg₂ hg₁' hg₂' hmap

/-- The `(i,j)` transition pulled through the `(i,j)` face is exactly its explicit
inverse-ideal model pulled to the actual triple affine intersection. -/
theorem pullHom_localLineBundleChosenOverlapHom_comp_pairwise₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j)
        T.p₁₂ T.p₁ T.p₂ T.p₁₂_p₁ T.p₁₂_p₂ =
      localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k i j inf_le_left T.p₁ T.p₂
        (by
          rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
            Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
          exact (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₂_p₁)
        (by
          rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
            Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
          exact (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₂_p₂) := by
  letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  exact pullHom_localLineBundleChosenOverlapHom_eq_pairwiseModelOnTripleIntersection
    K X f U hnonempty hcover hU h D i j k i j inf_le_left
      T.p₁₂ T.p₁ T.p₂ T.p₁₂_p₁ T.p₁₂_p₂
      (tripleOverlapComparisonToIntersection_comp_pairwise₁₂
        K X f U hcover hU i j k)

/-- The `(j,k)` transition pulled through the `(j,k)` face is exactly its explicit
inverse-ideal model pulled to the actual triple affine intersection. -/
theorem pullHom_localLineBundleChosenOverlapHom_comp_pairwise₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let hsub : (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    letI := restrictionAlgebra X (U j ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D j k)
        T.p₂₃ T.p₂ T.p₃ T.p₂₃_p₂ T.p₂₃_p₃ =
      localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k j k hsub T.p₂ T.p₃
        (by
          rw [tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
            Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
          exact (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂₃_p₂)
        (by
          rw [tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
            Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
          exact (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₂₃_p₃) := by
  let hsub : (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  letI := restrictionAlgebra X (U j ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  exact pullHom_localLineBundleChosenOverlapHom_eq_pairwiseModelOnTripleIntersection
    K X f U hnonempty hcover hU h D i j k j k hsub
      T.p₂₃ T.p₂ T.p₃ T.p₂₃_p₂ T.p₂₃_p₃
      (tripleOverlapComparisonToIntersection_comp_pairwise₂₃
        K X f U hcover hU i j k)

/-- The `(i,k)` transition pulled through the `(i,k)` face is exactly its explicit
inverse-ideal model pulled to the actual triple affine intersection. -/
theorem pullHom_localLineBundleChosenOverlapHom_comp_pairwise₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let hsub : (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i k)
        T.p₁₃ T.p₁ T.p₃ T.p₁₃_p₁ T.p₁₃_p₃ =
      localLineBundlePairwiseModelHomOnTripleIntersection
        K X f U hnonempty hcover hU h D i j k i k hsub T.p₁ T.p₃
        (by
          rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₃,
            Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
          exact (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₃_p₁)
        (by
          rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₃,
            Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
          exact (LineBundleDescent.tripleOverlap
            (coordinateCover U hcover hU) i j k).p₁₃_p₃) := by
  let hsub : (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  letI := restrictionAlgebra X (U i ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  exact pullHom_localLineBundleChosenOverlapHom_eq_pairwiseModelOnTripleIntersection
    K X f U hnonempty hcover hU h D i j k i k hsub
      T.p₁₃ T.p₁ T.p₃ T.p₁₃_p₁ T.p₁₃_p₃
      (tripleOverlapComparisonToIntersection_comp_pairwise₁₃
        K X f U hcover hU i j k)

/-- The raw chosen-overlap cocycle is equivalent to the cocycle for the three explicit
pairwise inverse-ideal models after all three are pulled to the actual triple affine
intersection.  This is the downstream consumer of the three face base-change theorems.  It
isolates the remaining algebraic task without assuming or claiming that task has been solved. -/
theorem localLineBundleChosenOverlapHom_raw_cocycle_iff_pairwiseModelOnTripleIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) (i j k : I) :
    let hsub₂₃ : (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    let hsub₁₃ : (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
    letI := restrictionAlgebra X (U j ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub₂₃
    letI := restrictionAlgebra X (U i ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub₁₃
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    let m₁₂ := localLineBundlePairwiseModelHomOnTripleIntersection
      K X f U hnonempty hcover hU h D i j k i j inf_le_left T.p₁ T.p₂
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
        exact T.p₁₂_p₁)
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₂,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
        exact T.p₁₂_p₂)
    let m₂₃ := localLineBundlePairwiseModelHomOnTripleIntersection
      K X f U hnonempty hcover hU h D i j k j k hsub₂₃ T.p₂ T.p₃
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
        exact T.p₂₃_p₂)
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₂₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
        exact T.p₂₃_p₃)
    let m₁₃ := localLineBundlePairwiseModelHomOnTripleIntersection
      K X f U hnonempty hcover hU h D i j k i k hsub₁₃ T.p₁ T.p₃
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_left]
        exact T.p₁₃_p₁)
      (by
        rw [tripleOverlapComparisonToIntersection_comp_pairwise₁₃,
          Category.assoc, pairwiseOverlapComparisonToIntersection_comp_right]
        exact T.p₁₃_p₃)
    (pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundleChosenOverlapHomOnProperSmoothCurve
            K X f U hnonempty hcover hU h D i j)
          T.p₁₂ T.p₁ T.p₂ T.p₁₂_p₁ T.p₁₂_p₂ ≫
        pullHom (F := LineBundleDescent.modulesPseudofunctor)
          (localLineBundleChosenOverlapHomOnProperSmoothCurve
            K X f U hnonempty hcover hU h D j k)
          T.p₂₃ T.p₂ T.p₃ T.p₂₃_p₂ T.p₂₃_p₃ =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i k)
        T.p₁₃ T.p₁ T.p₃ T.p₁₃_p₁ T.p₁₃_p₃) ↔
      m₁₂ ≫ m₂₃ = m₁₃ := by
  dsimp only
  rw [pullHom_localLineBundleChosenOverlapHom_comp_pairwise₁₂,
    pullHom_localLineBundleChosenOverlapHom_comp_pairwise₂₃,
    pullHom_localLineBundleChosenOverlapHom_comp_pairwise₁₃]
  constructor <;> intro hcocycle <;> exact hcocycle

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
