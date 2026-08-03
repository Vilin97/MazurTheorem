/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorDescent

/-!
# Comparing chosen triple overlaps with affine chart intersections

For a proper curve over a field, the spectrum of the intersection of two
affine charts is a pullback over the curve. This file iterates that checked
comparison. It maps Mathlib's chosen threefold overlap to the spectrum of the
actual triple chart intersection and proves compatibility with all three
pairwise faces.

These are the scheme-map identities needed to pull the three inverse-ideal
transitions to one common affine model. No line-bundle cocycle is claimed
here: compatibility of the actual inverse-ideal isomorphisms with these base
changes remains a separate step.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open scoped AlgebraicGeometry

universe u v

/-- The chosen pairwise-overlap comparison followed by the affine intersection
map is the chosen pullback's structural map to the curve. -/
theorem pairwiseOverlapComparisonToIntersection_comp_fromSpec
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j : I) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    pairwiseOverlapComparisonToIntersection K X f U hcover hU i j ≫
        ((hU i).inf (hU j)).fromSpec =
      (LineBundleDescent.overlap (coordinateCover U hcover hU) i j).p := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hWij : IsAffineOpen (U i ⊓ U j) := (hU i).inf (hU j)
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  calc
    pairwiseOverlapComparisonToIntersection K X f U hcover hU i j ≫
        hWij.fromSpec =
      (pairwiseOverlapComparisonToIntersection K X f U hcover hU i j ≫
          CommonExtension.extensionMap Γ(X, U i) Γ(X, U i ⊓ U j)) ≫
        (hU i).fromSpec := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ pairwiseOverlapComparisonToIntersection
          K X f U hcover hU i j ≫ q)
        (restrictionExtensionMap_comp_fromSpec X (U i) (U i ⊓ U j)
          (hU i) hWij inf_le_left).symm
    _ = (LineBundleDescent.overlap
          (coordinateCover U hcover hU) i j).p₁ ≫ (hU i).fromSpec := by
      exact congrArg (fun q ↦ q ≫ (hU i).fromSpec)
        (pairwiseOverlapComparisonToIntersection_comp_left
          K X f U hcover hU i j)
    _ = (LineBundleDescent.overlap
          (coordinateCover U hcover hU) i j).p := by
      exact (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).hp₁

/-- The canonical comparison from Mathlib's chosen threefold overlap to the
spectrum of the actual triple affine intersection `(Uᵢ ∩ Uⱼ) ∩ Uₖ`. -/
noncomputable def tripleOverlapComparisonToIntersection
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).pullback ⟶
      Spec (.of Γ(X, (U i ⊓ U j) ⊓ U k)) := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hUij : IsAffineOpen (U i ⊓ U j) := (hU i).inf (hU j)
  letI := restrictionAlgebra X (U i) (U i ⊓ U j) inf_le_left
  letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) ((U i ⊓ U j) ⊓ U k) inf_le_right
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i j k
  let hpb := properCurveIntersectionSpectrumIsPullback
    K X f (U i ⊓ U j) (U k) hUij (hU k)
  exact hpb.lift
    (T.p₁₂ ≫ pairwiseOverlapComparisonToIntersection
      K X f U hcover hU i j)
    T.p₃
    (by
      calc
        (T.p₁₂ ≫ pairwiseOverlapComparisonToIntersection
            K X f U hcover hU i j) ≫ hUij.fromSpec =
          T.p₁₂ ≫ (LineBundleDescent.overlap
            (coordinateCover U hcover hU) i j).p := by
            simpa only [Category.assoc] using congrArg (fun q ↦ T.p₁₂ ≫ q)
              (pairwiseOverlapComparisonToIntersection_comp_fromSpec
                K X f U hcover hU i j)
        _ = T.p := T.p₁₂_p
        _ = T.p₃ ≫ (hU k).fromSpec := by
          change T.p = T.p₃ ≫ (coordinateCover U hcover hU).f k
          exact T.w₃.symm)

/-- The triple comparison projects to the `(i,j)` affine intersection through
the chosen `(i,j)` face. -/
theorem tripleOverlapComparisonToIntersection_comp_pairwise₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        CommonExtension.extensionMap
          Γ(X, U i ⊓ U j) Γ(X, (U i ⊓ U j) ⊓ U k) =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁₂ ≫
        pairwiseOverlapComparisonToIntersection K X f U hcover hU i j := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hUij : IsAffineOpen (U i ⊓ U j) := (hU i).inf (hU j)
  letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
  letI := restrictionAlgebra X (U k) ((U i ⊓ U j) ⊓ U k) inf_le_right
  exact (properCurveIntersectionSpectrumIsPullback
    K X f (U i ⊓ U j) (U k) hUij (hU k)).lift_fst _ _ _

/-- The triple comparison followed by the triple-intersection chart map is the
chosen threefold overlap's structural map to the curve. -/
theorem tripleOverlapComparisonToIntersection_comp_fromSpec
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    letI : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from f]
      infer_instance
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        (((hU i).inf (hU j)).inf (hU k)).fromSpec =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hUij : IsAffineOpen (U i ⊓ U j) := (hU i).inf (hU j)
  let hUijk : IsAffineOpen ((U i ⊓ U j) ⊓ U k) := hUij.inf (hU k)
  letI := restrictionAlgebra X (U i ⊓ U j) ((U i ⊓ U j) ⊓ U k) inf_le_left
  calc
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        hUijk.fromSpec =
      (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
          CommonExtension.extensionMap
            Γ(X, U i ⊓ U j) Γ(X, (U i ⊓ U j) ⊓ U k)) ≫
        hUij.fromSpec := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ tripleOverlapComparisonToIntersection
          K X f U hcover hU i j k ≫ q)
        (restrictionExtensionMap_comp_fromSpec X (U i ⊓ U j)
          ((U i ⊓ U j) ⊓ U k) hUij hUijk inf_le_left).symm
    _ = ((LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁₂ ≫
        pairwiseOverlapComparisonToIntersection K X f U hcover hU i j) ≫
          hUij.fromSpec := by
      exact congrArg (fun q ↦ q ≫ hUij.fromSpec)
        (tripleOverlapComparisonToIntersection_comp_pairwise₁₂
          K X f U hcover hU i j k)
    _ = (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁₂ ≫
        (LineBundleDescent.overlap
          (coordinateCover U hcover hU) i j).p := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁₂ ≫ q)
        (pairwiseOverlapComparisonToIntersection_comp_fromSpec
          K X f U hcover hU i j)
    _ = (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p := by
      exact (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁₂_p

private theorem tripleOverlapComparisonToPairwise
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k a b : I)
    (hsub : (U i ⊓ U j) ⊓ U k ≤ U a ⊓ U b)
    (face :
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).pullback ⟶
      (LineBundleDescent.overlap (coordinateCover U hcover hU) a b).pullback)
    (hface : face ≫
        (LineBundleDescent.overlap (coordinateCover U hcover hU) a b).p =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p) :
    letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        CommonExtension.extensionMap
          Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k) =
      face ≫ pairwiseOverlapComparisonToIntersection
        K X f U hcover hU a b := by
  letI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  let hUab : IsAffineOpen (U a ⊓ U b) := (hU a).inf (hU b)
  let hUijk : IsAffineOpen ((U i ⊓ U j) ⊓ U k) :=
    ((hU i).inf (hU j)).inf (hU k)
  letI := restrictionAlgebra X (U a ⊓ U b) ((U i ⊓ U j) ⊓ U k) hsub
  apply (cancel_mono hUab.fromSpec).1
  calc
    (tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        CommonExtension.extensionMap
          Γ(X, U a ⊓ U b) Γ(X, (U i ⊓ U j) ⊓ U k)) ≫
        hUab.fromSpec =
      tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        hUijk.fromSpec := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ tripleOverlapComparisonToIntersection
          K X f U hcover hU i j k ≫ q)
        (restrictionExtensionMap_comp_fromSpec X (U a ⊓ U b)
          ((U i ⊓ U j) ⊓ U k) hUab hUijk hsub)
    _ = (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p :=
      tripleOverlapComparisonToIntersection_comp_fromSpec
        K X f U hcover hU i j k
    _ = face ≫ (LineBundleDescent.overlap
          (coordinateCover U hcover hU) a b).p := hface.symm
    _ = (face ≫ pairwiseOverlapComparisonToIntersection
          K X f U hcover hU a b) ≫ hUab.fromSpec := by
      simpa only [Category.assoc] using
        (congrArg (fun q ↦ face ≫ q)
          (pairwiseOverlapComparisonToIntersection_comp_fromSpec
            K X f U hcover hU a b)).symm

/-- Compatibility of the common triple-intersection comparison with the
chosen `(j,k)` pairwise face. -/
theorem tripleOverlapComparisonToIntersection_comp_pairwise₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    let hsub : (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    letI := restrictionAlgebra X (U j ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        CommonExtension.extensionMap
          Γ(X, U j ⊓ U k) Γ(X, (U i ⊓ U j) ⊓ U k) =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₂₃ ≫
        pairwiseOverlapComparisonToIntersection K X f U hcover hU j k := by
  let hsub : (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  exact tripleOverlapComparisonToPairwise K X f U hcover hU i j k j k hsub
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂₃
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂₃_p

/-- Compatibility of the common triple-intersection comparison with the
chosen `(i,k)` pairwise face. -/
theorem tripleOverlapComparisonToIntersection_comp_pairwise₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : I) :
    let hsub : (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    letI := restrictionAlgebra X (U i ⊓ U k) ((U i ⊓ U j) ⊓ U k) hsub
    tripleOverlapComparisonToIntersection K X f U hcover hU i j k ≫
        CommonExtension.extensionMap
          Γ(X, U i ⊓ U k) Γ(X, (U i ⊓ U j) ⊓ U k) =
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i j k).p₁₃ ≫
        pairwiseOverlapComparisonToIntersection K X f U hcover hU i k := by
  let hsub : (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  exact tripleOverlapComparisonToPairwise K X f U hcover hU i j k i k hsub
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₃
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₃_p

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
