/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime
import Mathlib.Tactic.IrreducibleDef

/-!
# Diagonal normalization of the raw curve-divisor cocycle

The explicit inverse-ideal transitions for an arbitrary divisor already satisfy the full
all-index cocycle. This file proves that their diagonal transition is forced to be the identity,
using the triple self-overlap and cancellation by the pulled raw isomorphism. All calculation
machinery is private; the sole exported theorem is the diagonal normalization intended for the
eventual effective-descent module.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry

universe u u' v v'

private theorem pullHom_comp_same_map
    {C : Type u'} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u}}
    {X₁ X₂ X₃ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {M₃ : F.obj (.mk (.op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (e₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (e₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom e₁₂ g gf₁ gf₂ hgf₁ hgf₂ ≫
      pullHom e₂₃ g gf₂ gf₃ hgf₂ hgf₃ =
      pullHom (e₁₂ ≫ e₂₃) g gf₁ gf₃ hgf₁ hgf₃ := by
  subst gf₁
  subst gf₂
  subst gf₃
  simp [pullHom, Functor.map_comp]

private theorem pullHom_comp_same_map_of_comp
    {C : Type u'} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u}}
    {X₁ X₂ X₃ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {M₃ : F.obj (.mk (.op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (e₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (e₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (e₁₃ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (hcomp : e₁₂ ≫ e₂₃ = e₁₃)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom e₁₂ g gf₁ gf₂ hgf₁ hgf₂ ≫
      pullHom e₂₃ g gf₂ gf₃ hgf₂ hgf₃ =
      pullHom e₁₃ g gf₁ gf₃ hgf₁ hgf₃ := by
  rw [pullHom_comp_same_map e₁₂ e₂₃ g gf₁ gf₂ gf₃ hgf₁ hgf₂ hgf₃,
    hcomp]

/-- The diagonal map obtained by pulling the raw self-transition back along the chart
immersion. -/
private noncomputable irreducible_def rawDiagonalEndomorphism
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :=
  Pseudofunctor.DescentData'.pullHom'
    (F := LineBundleDescent.modulesPseudofunctor)
    (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
    (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom)
    ((coordinateCover U hcover hU).f i)
    (𝟙 ((coordinateCover U hcover hU).X i))
    (𝟙 ((coordinateCover U hcover hU).X i))

/-- The diagonal endomorphism as the forward map of an isomorphism. -/
private noncomputable irreducible_def rawDiagonalIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :=
  let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i i
  LineBundleDescent.pullIso
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i i)
    (P.isPullback.lift (𝟙 _) (𝟙 _) (by simp)) (𝟙 _) (𝟙 _)
    (P.isPullback.lift_fst (𝟙 _) (𝟙 _) (by simp))
    (P.isPullback.lift_snd (𝟙 _) (𝟙 _) (by simp))

private theorem rawDiagonalIso_hom
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    (rawDiagonalIso K X f U hnonempty hcover hU h D i).hom =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  rw [rawDiagonalIso_def, rawDiagonalEndomorphism_def]
  rfl

/-- A lift from one chart to its chosen triple self-overlap. -/
private noncomputable irreducible_def rawTripleDiagonalLift
    (X : Scheme.{u}) {I : Type} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i : (coordinateCover U hcover hU).I₀) :
    (coordinateCover U hcover hU).X i ⟶
      (LineBundleDescent.tripleOverlap
        (coordinateCover U hcover hU) i i i).pullback :=
  (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i).exists_lift
      (𝟙 _) (𝟙 _) (𝟙 _) ((coordinateCover U hcover hU).f i)
      (by simp) (by simp) (by simp) |>.choose

private theorem rawTripleDiagonalLift_p₁
    (X : Scheme.{u}) {I : Type} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i : (coordinateCover U hcover hU).I₀) :
    rawTripleDiagonalLift X U hcover hU i ≫
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i i i).p₁ = 𝟙 _ := by
  rw [rawTripleDiagonalLift_def]
  exact (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i).exists_lift
      (𝟙 _) (𝟙 _) (𝟙 _) ((coordinateCover U hcover hU).f i)
      (by simp) (by simp) (by simp) |>.choose_spec.1

private theorem rawTripleDiagonalLift_p₂
    (X : Scheme.{u}) {I : Type} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i : (coordinateCover U hcover hU).I₀) :
    rawTripleDiagonalLift X U hcover hU i ≫
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i i i).p₂ = 𝟙 _ := by
  rw [rawTripleDiagonalLift_def]
  exact (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i).exists_lift
      (𝟙 _) (𝟙 _) (𝟙 _) ((coordinateCover U hcover hU).f i)
      (by simp) (by simp) (by simp) |>.choose_spec.2.1

private theorem rawTripleDiagonalLift_p₃
    (X : Scheme.{u}) {I : Type} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i : (coordinateCover U hcover hU).I₀) :
    rawTripleDiagonalLift X U hcover hU i ≫
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i i i).p₃ = 𝟙 _ := by
  rw [rawTripleDiagonalLift_def]
  exact (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i).exists_lift
      (𝟙 _) (𝟙 _) (𝟙 _) ((coordinateCover U hcover hU).f i)
      (by simp) (by simp) (by simp) |>.choose_spec.2.2

private theorem rawTripleDiagonalLift_p
    (X : Scheme.{u}) {I : Type} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i : (coordinateCover U hcover hU).I₀) :
    rawTripleDiagonalLift X U hcover hU i ≫
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i i i).p =
      (coordinateCover U hcover hU).f i := by
  rw [← (LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i).w₁,
    ← Category.assoc, rawTripleDiagonalLift_p₁, Category.id_comp]

private theorem rawPull₁₂_eq_diagonal
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i
    pullHom
        (Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D a b).hom)
          T.p T.p₁ T.p₂ T.w₁ T.w₂)
        (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _)
        (rawTripleDiagonalLift_p₁ X U hcover hU i)
        (rawTripleDiagonalLift_p₂ X U hcover hU i) =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  dsimp only
  rw [rawDiagonalEndomorphism_def]
  exact Pseudofunctor.DescentData'.pullHom_pullHom'
    (hom := fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom)
    (rawTripleDiagonalLift X U hcover hU i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p
    ((coordinateCover U hcover hU).f i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p₁
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p₂
    (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p X U hcover hU i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).w₁
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).w₂
    (rawTripleDiagonalLift_p₁ X U hcover hU i)
    (rawTripleDiagonalLift_p₂ X U hcover hU i)

private theorem rawPull₂₃_eq_diagonal
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i
    pullHom
        (Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D a b).hom)
          T.p T.p₂ T.p₃ T.w₂ T.w₃)
        (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _)
        (rawTripleDiagonalLift_p₂ X U hcover hU i)
        (rawTripleDiagonalLift_p₃ X U hcover hU i) =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  dsimp only
  rw [rawDiagonalEndomorphism_def]
  exact Pseudofunctor.DescentData'.pullHom_pullHom'
    (hom := fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom)
    (rawTripleDiagonalLift X U hcover hU i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p
    ((coordinateCover U hcover hU).f i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p₂
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p₃
    (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p X U hcover hU i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).w₂
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).w₃
    (rawTripleDiagonalLift_p₂ X U hcover hU i)
    (rawTripleDiagonalLift_p₃ X U hcover hU i)

private theorem rawPull₁₃_eq_diagonal
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i
    pullHom
        (Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D a b).hom)
          T.p T.p₁ T.p₃ T.w₁ T.w₃)
        (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _)
        (rawTripleDiagonalLift_p₁ X U hcover hU i)
        (rawTripleDiagonalLift_p₃ X U hcover hU i) =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  dsimp only
  rw [rawDiagonalEndomorphism_def]
  exact Pseudofunctor.DescentData'.pullHom_pullHom'
    (hom := fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom)
    (rawTripleDiagonalLift X U hcover hU i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p
    ((coordinateCover U hcover hU).f i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p₁
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).p₃
    (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p X U hcover hU i)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).w₁
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i i i).w₃
    (rawTripleDiagonalLift_p₁ X U hcover hU i)
    (rawTripleDiagonalLift_p₃ X U hcover hU i)

private noncomputable irreducible_def rawDiagonalFace₁₂
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :=
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i
  let raw := fun a b ↦
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
  pullHom
    (Pseudofunctor.DescentData'.pullHom'
      raw T.p T.p₁ T.p₂ T.w₁ T.w₂)
    (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p₁ X U hcover hU i)
    (rawTripleDiagonalLift_p₂ X U hcover hU i)

private noncomputable irreducible_def rawDiagonalFace₂₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :=
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i
  let raw := fun a b ↦
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
  pullHom
    (Pseudofunctor.DescentData'.pullHom'
      raw T.p T.p₂ T.p₃ T.w₂ T.w₃)
    (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p₂ X U hcover hU i)
    (rawTripleDiagonalLift_p₃ X U hcover hU i)

private noncomputable irreducible_def rawDiagonalFace₁₃
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :=
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i
  let raw := fun a b ↦
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
  pullHom
    (Pseudofunctor.DescentData'.pullHom'
      raw T.p T.p₁ T.p₃ T.w₁ T.w₃)
    (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p₁ X U hcover hU i)
    (rawTripleDiagonalLift_p₃ X U hcover hU i)

private theorem rawDiagonalFace₁₂_eq
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    rawDiagonalFace₁₂ K X f U hnonempty hcover hU h D i =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  rw [rawDiagonalFace₁₂_def]
  exact rawPull₁₂_eq_diagonal K X f U hnonempty hcover hU h D i

private theorem rawDiagonalFace₂₃_eq
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    rawDiagonalFace₂₃ K X f U hnonempty hcover hU h D i =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  rw [rawDiagonalFace₂₃_def]
  exact rawPull₂₃_eq_diagonal K X f U hnonempty hcover hU h D i

private theorem rawDiagonalFace₁₃_eq
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    rawDiagonalFace₁₃ K X f U hnonempty hcover hU h D i =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  rw [rawDiagonalFace₁₃_def]
  exact rawPull₁₃_eq_diagonal K X f U hnonempty hcover hU h D i

private theorem rawDiagonalFaces_cocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    rawDiagonalFace₁₂ K X f U hnonempty hcover hU h D i ≫
        rawDiagonalFace₂₃ K X f U hnonempty hcover hU h D i =
      rawDiagonalFace₁₃ K X f U hnonempty hcover hU h D i := by
  rw [rawDiagonalFace₁₂_def]
  rw [rawDiagonalFace₂₃_def]
  rw [rawDiagonalFace₁₃_def]
  let T := LineBundleDescent.tripleOverlap
    (coordinateCover U hcover hU) i i i
  let raw := fun a b ↦
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D a b).hom
  exact pullHom_comp_same_map_of_comp _ _ _
    (localLineBundleRawOverlapIsoFamily_cocycle_prime
      K X f U hnonempty hcover hU h D i i i)
    (rawTripleDiagonalLift X U hcover hU i) (𝟙 _) (𝟙 _) (𝟙 _)
    (rawTripleDiagonalLift_p₁ X U hcover hU i)
    (rawTripleDiagonalLift_p₂ X U hcover hU i)
    (rawTripleDiagonalLift_p₃ X U hcover hU i)

private theorem rawDiagonalEndomorphism_idempotent
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i ≫
        rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i := by
  calc
    _ = rawDiagonalFace₁₂ K X f U hnonempty hcover hU h D i ≫
        rawDiagonalFace₂₃ K X f U hnonempty hcover hU h D i := by
      rw [rawDiagonalFace₁₂_eq K X f U hnonempty hcover hU h D i,
        rawDiagonalFace₂₃_eq K X f U hnonempty hcover hU h D i]
    _ = rawDiagonalFace₁₃ K X f U hnonempty hcover hU h D i :=
      rawDiagonalFaces_cocycle K X f U hnonempty hcover hU h D i
    _ = _ := rawDiagonalFace₁₃_eq K X f U hnonempty hcover hU h D i

/-- The raw inverse-ideal overlap isomorphism restricts to the identity on every chart
diagonal. This is the sole exported result of the internal normalization calculation. -/
theorem Internal.localLineBundleRawOverlapIsoFamily_normalization
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := LineBundleDescent.modulesPseudofunctor)
      (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
      (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h D a b).hom)
      ((coordinateCover U hcover hU).f i)
      (𝟙 ((coordinateCover U hcover hU).X i))
      (𝟙 ((coordinateCover U hcover hU).X i)) = 𝟙 _ := by
  rw [← rawDiagonalEndomorphism_def]
  let E := rawDiagonalIso K X f U hnonempty hcover hU h D i
  have hE : E.hom =
      rawDiagonalEndomorphism K X f U hnonempty hcover hU h D i :=
    rawDiagonalIso_hom K X f U hnonempty hcover hU h D i
  have hee := rawDiagonalEndomorphism_idempotent
    K X f U hnonempty hcover hU h D i
  rw [← hE] at hee ⊢
  apply (cancel_epi E.hom).1
  simpa only [Category.comp_id] using hee

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
