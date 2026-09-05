/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveAssociativity

/-!
# Canonical projective-point addition compatibility

This module proves that the coordinate map from Mathlib projective
Weierstrass points to points of the concrete projective cubic preserves the
globally constructed group law.  Its design boundary is point evaluation on
the standard-by-standard product chart.  Distinct abscissas use the secant
output localization; equal abscissas away from the inverse locus use the
`D(B₁₂)` product neighbourhood and its tangent formula.  The identity and
inverse cases then complete the pointwise group-law comparison.

The public boundary is `projectivePointOverMorphism_add_canonical` together
with `canonicalPointGroupLawCompatibility`.  It also exposes
`standardChartSpecMap_comp_coveringChartMap`, identifying evaluation on the
standard affine chart with the corresponding projective coordinate point.
The named downstream consumers are the order-49 split `Gamma₀` construction,
which no longer needs a supplied group-law compatibility hypothesis, and the
level-49 eta scheme-point compatibility square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry
open scoped WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u
variable {K : Type u} [Field K]

private abbrev A (W : WeierstrassCurve K) :=
  coveringChartCoordinateRing W true

private noncomputable def standardChartPointOver
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] K) :
    AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      coveringChartMap W true) (by
        change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
            coveringChartMap W true) ≫ structureMap W =
          Spec.map (CommRingCat.ofHom (algebraMap K K))
        rw [Category.assoc, coveringChartMap_comp_structureMap,
          ← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
        ext a
        exact φ.commutes a)

private noncomputable def chartCoordinates
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] K) : Fin 3 → K :=
  φ ∘ coveringChartUniversalPoint W true

private theorem standardChartPointOver_eq_pointOver
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] K)
    (hP : W.toProjective.Nonsingular (chartCoordinates W φ)) :
    standardChartPointOver W φ =
      pointOverOfNonsingularRepresentative W (chartCoordinates W φ) hP := by
  apply overPoint_eq_of_ambientClosedPoint_eq W
  let s : Spec (.of K) := IsLocalRing.closedPoint K
  change ambientMorphismOfOverPoint W (standardChartPointOver W φ)
      s =
    ambientMorphismOfOverPoint W
      (pointOverOfNonsingularRepresentative W (chartCoordinates W φ) hP)
        s
  rw [ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative]
  change
    ((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        coveringChartMap W true) ≫ inclusion W)
        s =
      ambientPoint (chartCoordinates W φ)
        (nonsingular_ne_zero W _ hP) s
  rw [Category.assoc, coveringChartMap_comp_inclusion]
  change
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      coveringChartQuotientInclusion W true ≫ coveringChartAway K true)
        s = _
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  cases n with
  | zero =>
      rw [mem_projective_degree_zero_iff_eq_zero _ p hp,
        mem_projective_degree_zero_iff_eq_zero _ p hp]
  | succ n =>
      rw [mem_ambientPoint_closedPoint_iff _ _ p (Nat.succ_pos n) hp]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      dsimp only [coveringChartAway]
      rw [polynomial_mem_awayι_iff_awayMk_mem
        (coveringCoordinate true)
          ((coveringChartQuotientInclusion W true)
          ((Spec.map (CommRingCat.ofHom φ.toRingHom))
            s)) p hp]
      change
        HomogeneousLocalization.Away.mk (homogeneousPieces K)
            (MvPolynomial.isHomogeneous_X K (coveringCoordinate true))
            (Nat.succ n) p _ ∈
          (PrimeSpectrum.comap
            (Ideal.Quotient.mk (coveringChartIdeal W true))
            (PrimeSpectrum.comap φ.toRingHom s)).asIdeal ↔ _
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      rw [show (IsLocalRing.closedPoint K).asIdeal = ⊥ from
        IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
      change φ (Ideal.Quotient.mk (coveringChartIdeal W true)
        (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (MvPolynomial.isHomogeneous_X K (coveringCoordinate true))
          (Nat.succ n) p _)) = 0 ↔ _
      rw [coordinateChartAwayMk_eq_eval₂Hom
        (coveringCoordinate true) p hp]
      change
        (φ.toRingHom.comp (Ideal.Quotient.mk (coveringChartIdeal W true)))
            (MvPolynomial.eval₂Hom
              (coordinateChartConstantHom (coveringCoordinate true))
              (coordinateChartRatio (coveringCoordinate true)) p) = 0 ↔ _
      rw [MvPolynomial.map_eval₂Hom]
      change MvPolynomial.eval₂Hom
          (φ.toRingHom.comp
            ((Ideal.Quotient.mk (coveringChartIdeal W true)).comp
              (coordinateChartConstantHom (coveringCoordinate true))))
          (chartCoordinates W φ) p = 0 ↔ _
      have hconst :
          φ.toRingHom.comp
              ((Ideal.Quotient.mk (coveringChartIdeal W true)).comp
                (coordinateChartConstantHom (coveringCoordinate true))) =
            RingHom.id K := by
        ext a
        exact φ.commutes a
      rw [hconst]
      rfl

/-- Evaluating the represented standard-chart coordinate ring at a field
point and mapping into the projective cubic gives the projective point whose
homogeneous coordinates are the three evaluated chart ratios. -/
theorem standardChartSpecMap_comp_coveringChartMap
    (W : WeierstrassCurve K)
    (φ : coveringChartCoordinateRing W true →ₐ[K] K)
    (hP : W.toProjective.Nonsingular
      (φ ∘ coveringChartUniversalPoint W true)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ coveringChartMap W true =
      pointOfNonsingularRepresentative W
        (φ ∘ coveringChartUniversalPoint W true) hP := by
  have h := congrArg (fun f => f.left)
    (standardChartPointOver_eq_pointOver W φ hP)
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      coveringChartMap W true =
    pointOfNonsingularRepresentative W
      (φ ∘ coveringChartUniversalPoint W true) hP at h
  exact h

private theorem affineStandardPoint_equation
    (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) :
    (W.map (algebraMap K K)).toProjective.Equation ![x, y, 1] := by
  simpa using
    ((W.toProjective.nonsingular_some x y).mpr h).left.map
      (algebraMap K K)

private theorem affineStandardPoint_normalized (x y : K) :
    (![x, y, 1] : Fin 3 → K) (coveringCoordinate true) = 1 := by
  rfl

private noncomputable def affineStandardChartAlgHom
    (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) : A W →ₐ[K] K :=
  coveringChartCoordinateRingAlgHomOfNormalizedPoint W true ![x, y, 1]
    (affineStandardPoint_equation W x y h)
    (affineStandardPoint_normalized x y)

@[simp]
private theorem affineStandardChartAlgHom_coordinates
    (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) :
    chartCoordinates W (affineStandardChartAlgHom W x y h) = ![x, y, 1] := by
  funext j
  change affineStandardChartAlgHom W x y h
      (coveringChartUniversalPoint W true j) = ![x, y, 1] j
  rw [show coveringChartUniversalPoint W true j =
      Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (coveringCoordinate true) j) by rfl]
  unfold affineStandardChartAlgHom
  rw [coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio]

private theorem standardChartPointOver_affine
    (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) :
    standardChartPointOver W (affineStandardChartAlgHom W x y h) =
      affinePointOverMorphism W (.some x y h) := by
  rw [standardChartPointOver_eq_pointOver W _]
  · apply pointOverOfNonsingularRepresentative_eq_of_equiv
    rw [affineStandardChartAlgHom_coordinates]
  · rw [affineStandardChartAlgHom_coordinates]
    exact (W.toProjective.nonsingular_some x y).mpr h

private abbrev B (W : WeierstrassCurve K) :=
  TensorProduct K (A W) (A W)

private noncomputable def affinePairChartAlgHom
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) : B W →ₐ[K] K :=
  Algebra.TensorProduct.lift
    (affineStandardChartAlgHom W x₁ y₁ h₁)
    (affineStandardChartAlgHom W x₂ y₂ h₂)
    (fun _ _ ↦ Commute.all _ _)

private noncomputable def standardPairPointOver
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] K) :
    AffineCommGroupScheme.testObject (R := K) K ⟶
      toOver W ⊗ toOver W :=
  lift
    (standardChartPointOver W
      (φ.comp (Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := A W) (B := A W))))
    (standardChartPointOver W
      (φ.comp (Algebra.TensorProduct.includeRight
        (R := K) (A := A W) (B := A W))))

private theorem affinePairChartAlgHom_comp_left
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).comp
        (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A W) (B := A W)) =
      affineStandardChartAlgHom W x₁ y₁ h₁ := by
  ext a
  simp [affinePairChartAlgHom]

private theorem affinePairChartAlgHom_comp_right
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).comp
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A W) (B := A W)) =
      affineStandardChartAlgHom W x₂ y₂ h₂ := by
  ext a
  simp [affinePairChartAlgHom]

private theorem standardPairPointOver_affine
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    standardPairPointOver W
        (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) =
      lift (affinePointOverMorphism W (.some x₁ y₁ h₁))
        (affinePointOverMorphism W (.some x₂ y₂ h₂)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [standardPairPointOver, lift_fst]
    rw [affinePairChartAlgHom_comp_left,
      standardChartPointOver_affine]
  · simp only [standardPairPointOver, lift_snd]
    rw [affinePairChartAlgHom_comp_right,
      standardChartPointOver_affine]

private theorem evaluatedStandardPair_fst
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] K) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true)) ≫
        pullback.fst (structureMap W) (structureMap W) =
      Spec.map (CommRingCat.ofHom
        (φ.comp (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A W) (B := A W))).toRingHom) ≫
        coveringChartMap W true := by
  calc
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          (projectivePairChartMap W (true, true) ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartFirstInput W (true, true) := by
            simp only [projectivePairChartMap_comp_fst,
              projectivePairChartFirstInput_eq]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          ((projectivePairChartIsoSpecTensor W (true, true)).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeft
                (R := K) (S := K) (A := A W) (B := A W)).toRingHom) ≫
              coveringChartMap W true) := by rfl
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft
            (R := K) (S := K) (A := A W) (B := A W)).toRingHom) ≫
          coveringChartMap W true := by simp
    _ = _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem evaluatedStandardPair_snd
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] K) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true)) ≫
        pullback.snd (structureMap W) (structureMap W) =
      Spec.map (CommRingCat.ofHom
        (φ.comp (Algebra.TensorProduct.includeRight
          (R := K) (A := A W) (B := A W))).toRingHom) ≫
        coveringChartMap W true := by
  calc
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          (projectivePairChartMap W (true, true) ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartSecondInput W (true, true) := by
            simp only [projectivePairChartMap_comp_snd,
              projectivePairChartSecondInput_eq]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          ((projectivePairChartIsoSpecTensor W (true, true)).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight
                (R := K) (A := A W) (B := A W)).toRingHom) ≫
              coveringChartMap W true) := by rfl
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := K) (A := A W) (B := A W)).toRingHom) ≫
          coveringChartMap W true := by simp
    _ = _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem standardPairPointOver_left_eq
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] K) :
    (standardPairPointOver W φ).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true) := by
  apply pullback.hom_ext
  · have h := congrArg (fun q ↦ q.left)
        (lift_fst
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeLeft
              (R := K) (S := K) (A := A W) (B := A W))))
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeRight
              (R := K) (A := A W) (B := A W)))))
    simp only [Over.comp_left, Over.fst_left] at h
    exact h.trans (evaluatedStandardPair_fst W φ).symm
  · have h := congrArg (fun q ↦ q.left)
        (lift_snd
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeLeft
              (R := K) (S := K) (A := A W) (B := A W))))
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeRight
              (R := K) (A := A W) (B := A W)))))
    simp only [Over.comp_left, Over.snd_left] at h
    exact h.trans (evaluatedStandardPair_snd W φ).symm

private noncomputable def standardPairOutputToField
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    projectivePairChartAdditionOutputRing W (true, true) true →ₐ[K] K := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) →ₐ[K] K
  exact IsLocalization.Away.liftAlgHom
    (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) (f := φ) hZ.isUnit

private theorem standardPairOutputToField_algebraMap
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) (a : B W) :
    standardPairOutputToField W φ hZ
        (algebraMap (B W)
          (projectivePairChartAdditionOutputRing W
            (true, true) true) a) = φ a := by
  change IsLocalization.Away.liftAlgHom
      (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) hZ.isUnit
        (algebraMap (B W)
          (Localization.Away
            (projectivePairChartAdditionCoordinates W
              (true, true) (2 : Fin 3))) a) = φ a
  exact IsLocalization.Away.lift_eq
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)))
    (x := projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3))
    (g := φ.toRingHom) hZ.isUnit a

private theorem standardPairOutputToField_comp_algebraMap
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    (standardPairOutputToField W φ hZ).comp
        (IsScalarTower.toAlgHom K (B W)
          (projectivePairChartAdditionOutputRing W
            (true, true) true)) = φ := by
  apply DFunLike.ext _ _
  intro a
  exact standardPairOutputToField_algebraMap W φ hZ a

private theorem standardPairPoint_factor_output
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    Spec.map (CommRingCat.ofHom
        (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) true =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).1
  rw [Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((standardPairOutputToField W φ hZ).comp
        (IsScalarTower.toAlgHom K (B W)
          (projectivePairChartAdditionOutputRing W
            (true, true) true))).toRingHom) =
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  rw [standardPairOutputToField_comp_algebraMap]

private noncomputable def standardPairSumAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) : A W →ₐ[K] K :=
  (standardPairOutputToField W φ hZ).comp
    (projectivePairChartAdditionOutputAlgHom W
      (true, true) true)

private theorem standardPairPoint_addition
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    standardPairPointOver W φ ≫ projectiveAdditionOver W =
      standardChartPointOver W (standardPairSumAlgHom W φ hZ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, projectiveAdditionOver_left]
  rw [standardPairPointOver_left_eq]
  change _ = Spec.map (CommRingCat.ofHom
      (standardPairSumAlgHom W φ hZ).toRingHom) ≫
    coveringChartMap W true
  calc
    _ = (Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
          projectivePairChartAdditionOutputOpen W
            (true, true) true) ≫
        projectivePairChartMap W (true, true) ≫
          projectiveAdditionMorphism W := by
            exact (Category.assoc _ _ _).trans (congrArg
              (fun q ↦ q ≫ (projectivePairChartMap W (true, true) ≫
                projectiveAdditionMorphism W))
              (standardPairPoint_factor_output W φ hZ).symm)
    _ = Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) true ≫
          (projectivePairChartMap W (true, true) ≫
            projectiveAdditionMorphism W) := by simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) true ≫ standardPairAdditionMorphism W := by
            rw [projectivePairStandardChart_comp_projectiveAdditionMorphism]
    _ = Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) true := by
            simpa only [Category.assoc] using congrArg
              (fun q ↦ Spec.map (CommRingCat.ofHom
                (standardPairOutputToField W φ hZ).toRingHom) ≫ q)
              (projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism W)
    _ = Spec.map (CommRingCat.ofHom
          (standardPairSumAlgHom W φ hZ).toRingHom) ≫
        coveringChartMap W true := by
      rw [projectivePairChartAdditionOutputMorphism]
      simp only [standardPairSumAlgHom]
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem standardPairOutputToField_unit
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    standardPairOutputToField W φ hZ
        (projectivePairChartAdditionOutputUnit W
          (true, true) true) =
      φ (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) := by
  rw [projectivePairChartAdditionOutputUnit]
  rw [(IsLocalization.Away.algebraMap_isUnit
    (projectivePairChartAdditionCoordinates W
      (true, true) (coveringCoordinate true))).unit_spec]
  exact standardPairOutputToField_algebraMap W φ hZ _

private theorem standardPairSumAlgHom_universalPoint
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] K)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) (j : Fin 3) :
    standardPairSumAlgHom W φ hZ
        (coveringChartUniversalPoint W true j) =
      (φ (projectivePairChartAdditionCoordinates W
          (true, true) (2 : Fin 3)))⁻¹ *
        φ (projectivePairChartAdditionCoordinates W
          (true, true) j) := by
  rw [standardPairSumAlgHom, AlgHom.comp_apply]
  rw [show coveringChartUniversalPoint W true j =
      Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (coveringCoordinate true) j) by rfl]
  rw [projectivePairChartAdditionOutputAlgHom_ratio]
  rw [projectivePairChartAdditionOutputPoint, map_mul,
    map_units_inv, standardPairOutputToField_unit,
    standardPairOutputToField_algebraMap]

private theorem affinePairChartAlgHom_firstCoordinates
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂ ∘
        projectivePairChartFirstUniversalPoint W (true, true) =
      ![x₁, y₁, 1] := by
  funext j
  change
    ((affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).comp
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := A W) (B := A W)))
      (coveringChartUniversalPoint W true j) = _
  rw [affinePairChartAlgHom_comp_left]
  exact congrFun (affineStandardChartAlgHom_coordinates W x₁ y₁ h₁) j

private theorem affinePairChartAlgHom_secondCoordinates
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂ ∘
        projectivePairChartSecondUniversalPoint W (true, true) =
      ![x₂, y₂, 1] := by
  funext j
  change
    ((affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).comp
      (Algebra.TensorProduct.includeRight
        (R := K) (A := A W) (B := A W)))
      (coveringChartUniversalPoint W true j) = _
  rw [affinePairChartAlgHom_comp_right]
  exact congrFun (affineStandardChartAlgHom_coordinates W x₂ y₂ h₂) j

private theorem affinePairChartAlgHom_additionCoordinates
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂ ∘
        projectivePairChartAdditionCoordinates W (true, true) =
      W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1] := by
  let φ := affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
  have hmap := WeierstrassCurve.Projective.map_addXYZ
    (W' := (projectivePairChartMappedCurve W (true, true)).toProjective)
    (f := φ.toRingHom)
    (P := projectivePairChartFirstUniversalPoint W (true, true))
    (Q := projectivePairChartSecondUniversalPoint W (true, true))
  have hcoeff : φ.toRingHom.comp (algebraMap K (B W)) =
      algebraMap K K := by
    ext a
    exact φ.commutes a
  change ((W.map (algebraMap K (B W))).map φ.toRingHom).toProjective.addXYZ _ _ = _
    at hmap
  rw [WeierstrassCurve.map_map, hcoeff] at hmap
  have hW : W.map (algebraMap K K) = W := by
    ext <;> simp
  rw [hW] at hmap
  change φ ∘
      (projectivePairChartMappedCurve W (true, true)).toProjective.addXYZ
        (projectivePairChartFirstUniversalPoint W (true, true))
        (projectivePairChartSecondUniversalPoint W (true, true)) = _
  calc
    _ = W.toProjective.addXYZ
        (φ ∘ projectivePairChartFirstUniversalPoint W (true, true))
        (φ ∘ projectivePairChartSecondUniversalPoint W (true, true)) :=
      hmap.symm
    _ = _ := by
      rw [affinePairChartAlgHom_firstCoordinates W x₁ y₁ x₂ y₂ h₁ h₂,
        affinePairChartAlgHom_secondCoordinates W x₁ y₁ x₂ y₂ h₁ h₂]

private theorem affinePairChartAlgHom_rawZ_ne_zero
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (projectivePairChartAdditionCoordinates W
          (true, true) (2 : Fin 3)) ≠ 0 := by
  have hEq₁ : W.toProjective.Equation ![x₁, y₁, 1] :=
    ((W.toProjective.nonsingular_some x₁ y₁).mpr h₁).left
  have hEq₂ : W.toProjective.Equation ![x₂, y₂, 1] :=
    ((W.toProjective.nonsingular_some x₂ y₂).mpr h₂).left
  have hz := W.toProjective.addZ_ne_zero_of_X_ne hEq₁ hEq₂ (by simpa using hx)
  change W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1]
      (2 : Fin 3) ≠ 0 at hz
  rw [← congrFun
    (affinePairChartAlgHom_additionCoordinates W x₁ y₁ x₂ y₂ h₁ h₂)
      (2 : Fin 3)] at hz
  exact hz

private theorem standardPairSum_coordinates_of_X_ne
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let φ := affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
    let hZ := affinePairChartAlgHom_rawZ_ne_zero W x₁ y₁ x₂ y₂ h₁ h₂ hx
    chartCoordinates W (standardPairSumAlgHom W φ hZ) =
      ![W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂),
        W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂),
        1] := by
  dsimp only
  let φ := affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
  let hZ := affinePairChartAlgHom_rawZ_ne_zero W x₁ y₁ x₂ y₂ h₁ h₂ hx
  have hcoords := affinePairChartAlgHom_additionCoordinates
    W x₁ y₁ x₂ y₂ h₁ h₂
  have hEq₁ : W.toProjective.Equation ![x₁, y₁, 1] :=
    ((W.toProjective.nonsingular_some x₁ y₁).mpr h₁).left
  have hEq₂ : W.toProjective.Equation ![x₂, y₂, 1] :=
    ((W.toProjective.nonsingular_some x₂ y₂).mpr h₂).left
  have hformula := W.toProjective.addXYZ_of_Z_ne_zero
    hEq₁ hEq₂ one_ne_zero one_ne_zero (by simpa using hx)
  funext j
  change standardPairSumAlgHom W φ hZ
      (coveringChartUniversalPoint W true j) = _
  rw [standardPairSumAlgHom_universalPoint]
  have hzcoord := congrFun hcoords (2 : Fin 3)
  have hjcoord := congrFun hcoords j
  change φ (projectivePairChartAdditionCoordinates W (true, true) 2) = _
    at hzcoord
  change φ (projectivePairChartAdditionCoordinates W (true, true) j) = _
    at hjcoord
  rw [hzcoord, hjcoord]
  rw [hformula]
  have hz' : W.toProjective.addZ ![x₁, y₁, 1] ![x₂, y₂, 1] ≠ 0 :=
    W.toProjective.addZ_ne_zero_of_X_ne hEq₁ hEq₂ (by simpa using hx)
  simp [hz']

private theorem standardPairPoint_addition_affine_of_X_ne
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    let φ := affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
    standardPairPointOver W φ ≫ projectiveAdditionOver W =
      affinePointOverMorphism W
        (.some
          (W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.addY x₁ x₂ y₁
            (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.nonsingular_add h₁ h₂
            (fun hxy ↦ hx hxy.1))) := by
  dsimp only
  let φ := affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
  let hZ := affinePairChartAlgHom_rawZ_ne_zero W x₁ y₁ x₂ y₂ h₁ h₂ hx
  rw [standardPairPoint_addition W φ hZ]
  rw [standardChartPointOver_eq_pointOver W _]
  · change pointOverOfNonsingularRepresentative W _ _ =
      pointOverOfNonsingularRepresentative W _ _
    apply pointOverOfNonsingularRepresentative_eq_of_equiv
    rw [standardPairSum_coordinates_of_X_ne W x₁ y₁ x₂ y₂ h₁ h₂ hx]
  · rw [standardPairSum_coordinates_of_X_ne W x₁ y₁ x₂ y₂ h₁ h₂ hx]
    exact W.toProjective.nonsingular_some _ _ |>.mpr
      (W.toAffine.nonsingular_add h₁ h₂ (fun hxy ↦ hx hxy.1))

private theorem affinePointOverMorphism_add_of_X_ne
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    affinePointOverMorphism W
        ((.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) =
      affinePointOverMorphism W (.some x₁ y₁ h₁) *
        affinePointOverMorphism W (.some x₂ y₂ h₂) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  change affinePointOverMorphism W (.some _ _ _) =
    lift (affinePointOverMorphism W (.some x₁ y₁ h₁))
        (affinePointOverMorphism W (.some x₂ y₂ h₂)) ≫
      projectiveAdditionOver W
  rw [← standardPairPointOver_affine W x₁ y₁ x₂ y₂ h₁ h₂]
  exact (standardPairPoint_addition_affine_of_X_ne
    W x₁ y₁ x₂ y₂ h₁ h₂ hx).symm

private noncomputable def affinePairPresentationAlgHom
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    secantPairCoordinateRing W →ₐ[K] K :=
  (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).comp
    (standardPairCoordinateRingAlgEquiv W).toAlgHom

@[simp]
private theorem affinePairPresentationAlgHom_X₁
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (secantPairX₁ W) = x₁ := by
  rw [affinePairPresentationAlgHom, AlgHom.comp_apply]
  rw [show (standardPairCoordinateRingAlgEquiv W).toAlgHom (secantPairX₁ W) =
      projectivePairChartFirstUniversalPoint W (true, true) 0 from
    standardPairCoordinateRingAlgEquiv_X₁ W]
  exact congrFun
    (affinePairChartAlgHom_firstCoordinates W x₁ y₁ x₂ y₂ h₁ h₂) 0

@[simp]
private theorem affinePairPresentationAlgHom_Y₁
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (secantPairY₁ W) = y₁ := by
  rw [affinePairPresentationAlgHom, AlgHom.comp_apply]
  rw [show (standardPairCoordinateRingAlgEquiv W).toAlgHom (secantPairY₁ W) =
      projectivePairChartFirstUniversalPoint W (true, true) 1 from
    standardPairCoordinateRingAlgEquiv_Y₁ W]
  exact congrFun
    (affinePairChartAlgHom_firstCoordinates W x₁ y₁ x₂ y₂ h₁ h₂) 1

@[simp]
private theorem affinePairPresentationAlgHom_X₂
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (secantPairX₂ W) = x₂ := by
  rw [affinePairPresentationAlgHom, AlgHom.comp_apply]
  rw [show (standardPairCoordinateRingAlgEquiv W).toAlgHom (secantPairX₂ W) =
      projectivePairChartSecondUniversalPoint W (true, true) 0 from
    standardPairCoordinateRingAlgEquiv_X₂ W]
  exact congrFun
    (affinePairChartAlgHom_secondCoordinates W x₁ y₁ x₂ y₂ h₁ h₂) 0

@[simp]
private theorem affinePairPresentationAlgHom_Y₂
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (secantPairY₂ W) = y₂ := by
  rw [affinePairPresentationAlgHom, AlgHom.comp_apply]
  rw [show (standardPairCoordinateRingAlgEquiv W).toAlgHom (secantPairY₂ W) =
      projectivePairChartSecondUniversalPoint W (true, true) 1 from
    standardPairCoordinateRingAlgEquiv_Y₂ W]
  exact congrFun
    (affinePairChartAlgHom_secondCoordinates W x₁ y₁ x₂ y₂ h₁ h₂) 1

private theorem affinePairPresentationAlgHom_B12
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (additionB12 W) = y₁ + y₂ + W.a₁ * x₁ + W.a₃ := by
  simp only [additionB12, map_add, map_mul,
    affinePairPresentationAlgHom_X₁,
    affinePairPresentationAlgHom_Y₁,
    affinePairPresentationAlgHom_Y₂]
  rw [secantPairCoefficientHom_eq_algebraMap,
    (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).commutes,
    (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).commutes]
  simp

private theorem affinePairPresentationAlgHom_A12
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (additionA12 W) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 +
        W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ := by
  simp only [additionA12, map_add, map_sub, map_mul, map_pow,
    affinePairPresentationAlgHom_X₁,
    affinePairPresentationAlgHom_Y₂,
    affinePairPresentationAlgHom_X₂]
  rw [secantPairCoefficientHom_eq_algebraMap,
    (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).commutes,
    (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).commutes,
    (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).commutes]
  simp

private theorem affinePairPresentationAlgHom_B12_ne_zero
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hneg : y₁ ≠ W.toAffine.negY x₂ y₂) :
    affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
        (additionB12 W) ≠ 0 := by
  rw [affinePairPresentationAlgHom_B12]
  intro hzero
  apply hneg
  rw [WeierstrassCurve.Affine.negY, ← hx]
  linear_combination hzero

private noncomputable def productNeighborhoodToField
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodCoordinateRing W →ₐ[K] K := by
  change Localization.Away (additionB12 W) →ₐ[K] K
  exact IsLocalization.Away.liftAlgHom (additionB12 W) (f := ψ) hB.isUnit

private theorem productNeighborhoodToField_algebraMap
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0)
    (a : secantPairCoordinateRing W) :
    productNeighborhoodToField W ψ hB
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W) a) = ψ a := by
  exact IsLocalization.Away.lift_eq
    (S := productNeighborhoodCoordinateRing W)
    (x := additionB12 W) (g := ψ.toRingHom) hB.isUnit a

private theorem productNeighborhoodToField_slope
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodSlope W) =
      ψ (additionA12 W) / ψ (additionB12 W) := by
  rw [productNeighborhoodSlope, map_mul, productNeighborhoodA12,
    productNeighborhoodToField_algebraMap, div_eq_mul_inv]
  congr 1
  apply (mul_eq_one_iff_eq_inv₀ hB).mp
  rw [← productNeighborhoodToField_algebraMap W ψ hB
      (additionB12 W), ← map_mul, mul_comm,
    IsLocalization.Away.mul_invSelf, map_one]

private theorem productNeighborhoodToField_slope_of_X_eq
    (W : WeierstrassCurve K) [DecidableEq K]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hneg : y₁ ≠ W.toAffine.negY x₂ y₂)
    (hB : affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
      (additionB12 W) ≠ 0) :
    productNeighborhoodToField W
        (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB
        (productNeighborhoodSlope W) =
      W.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hy : y₁ = y₂ :=
    W.toAffine.Y_eq_of_Y_ne h₁.left h₂.left hx hneg
  rw [productNeighborhoodToField_slope,
    affinePairPresentationAlgHom_A12,
    affinePairPresentationAlgHom_B12,
    W.toAffine.slope_of_Y_ne hx hneg]
  rw [hx, hy]
  simp only [WeierstrassCurve.Affine.negY]
  congr 1 <;> ring

private theorem productNeighborhoodPoint_factor
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    Spec.map (CommRingCat.ofHom
        (productNeighborhoodToField W ψ hB).toRingHom) ≫
      productNeighborhoodToPair W =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  rw [productNeighborhoodToPair, ← Spec.map_comp]
  apply congrArg
  apply CommRingCat.hom_ext
  apply DFunLike.ext _ _
  intro a
  exact productNeighborhoodToField_algebraMap W ψ hB a

private theorem standardPairEvaluation_comp_affinePairIso
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    Spec.map (CommRingCat.ofHom
        (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
      (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
        (standardPairIsoAffinePair W).hom =
      Spec.map (CommRingCat.ofHom
        (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) := by
  rw [← projectivePairChartIsoSpecTensor_hom_comp_standardPairCoordinateRingAlgEquiv_specMap]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  rfl

private theorem standardPairPointOver_left_eq_affinePair
    (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    (standardPairPointOver W
      (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂)).left =
      Spec.map (CommRingCat.ofHom
          (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
        (standardPairIsoAffinePair W).inv ≫
          projectivePairChartMap W (true, true) := by
  rw [standardPairPointOver_left_eq,
    ← standardPairEvaluation_comp_affinePairIso]
  simp
  rfl

private theorem productNeighborhoodCoefficientHom_eq_algebraMap'
    (W : WeierstrassCurve K) :
    productNeighborhoodCoefficientHom W =
      algebraMap K (productNeighborhoodCoordinateRing W) := by
  rw [productNeighborhoodCoefficientHom,
    secantPairCoefficientHom_eq_algebraMap]
  exact (IsScalarTower.algebraMap_eq K (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W)).symm

@[simp]
private theorem productNeighborhoodToField_X₁
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodX₁ W) =
      ψ (secantPairX₁ W) := by
  exact productNeighborhoodToField_algebraMap W ψ hB (secantPairX₁ W)

@[simp]
private theorem productNeighborhoodToField_Y₁
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodY₁ W) =
      ψ (secantPairY₁ W) := by
  exact productNeighborhoodToField_algebraMap W ψ hB (secantPairY₁ W)

@[simp]
private theorem productNeighborhoodToField_X₂
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodX₂ W) =
      ψ (secantPairX₂ W) := by
  exact productNeighborhoodToField_algebraMap W ψ hB (secantPairX₂ W)

@[simp]
private theorem productNeighborhoodToField_Y₂
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodY₂ W) =
      ψ (secantPairY₂ W) := by
  exact productNeighborhoodToField_algebraMap W ψ hB (secantPairY₂ W)

@[simp]
private theorem productNeighborhoodToField_coefficient
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) (a : K) :
    productNeighborhoodToField W ψ hB
        (productNeighborhoodCoefficientHom W a) = a := by
  rw [productNeighborhoodCoefficientHom_eq_algebraMap']
  exact (productNeighborhoodToField W ψ hB).commutes a

private theorem productNeighborhoodToField_addX
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodAddX W) =
      W.toAffine.addX (ψ (secantPairX₁ W)) (ψ (secantPairX₂ W))
        (productNeighborhoodToField W ψ hB
          (productNeighborhoodSlope W)) := by
  simp [productNeighborhoodAddX, WeierstrassCurve.Affine.addX]

private theorem productNeighborhoodToField_addY
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    productNeighborhoodToField W ψ hB (productNeighborhoodAddY W) =
      W.toAffine.addY (ψ (secantPairX₁ W)) (ψ (secantPairX₂ W))
        (ψ (secantPairY₁ W))
        (productNeighborhoodToField W ψ hB
          (productNeighborhoodSlope W)) := by
  simp [productNeighborhoodAddY, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX]

private noncomputable def productNeighborhoodAdditionAlgHom
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →ₐ[K]
      productNeighborhoodCoordinateRing W where
  __ := productNeighborhoodAdditionToAffineRing W
  commutes' a := by
    change productNeighborhoodAdditionToAffineRing W
        (secantTargetCoefficientHom W a) =
      algebraMap K (productNeighborhoodCoordinateRing W) a
    rw [productNeighborhoodAdditionToAffineRing_coefficient,
      productNeighborhoodCoefficientHom_eq_algebraMap']

private noncomputable def productNeighborhoodSumChartAlgHom
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) : A W →ₐ[K] K :=
  (productNeighborhoodToField W ψ hB).comp
    ((productNeighborhoodAdditionAlgHom W).comp
      (standardAffineChartAlgEquiv W).symm.toAlgHom)

private theorem productNeighborhoodSumChartAlgHom_coordinates
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    chartCoordinates W (productNeighborhoodSumChartAlgHom W ψ hB) =
      ![productNeighborhoodToField W ψ hB (productNeighborhoodAddX W),
        productNeighborhoodToField W ψ hB (productNeighborhoodAddY W), 1] := by
  funext j
  fin_cases j
  · change productNeighborhoodToField W ψ hB
        (productNeighborhoodAdditionToAffineRing W
          ((standardAffineChartAlgEquiv W).symm
            (coveringChartUniversalPoint W true 0))) = _
    rw [← standardAffineChartAlgEquiv_X, AlgEquiv.symm_apply_apply]
    have hX := productNeighborhoodAdditionToAffineRing_abscissa W
    change productNeighborhoodAdditionToAffineRing W (secantTargetX W) =
      productNeighborhoodAddX W at hX
    rw [hX]
    rfl
  · change productNeighborhoodToField W ψ hB
        (productNeighborhoodAdditionToAffineRing W
          ((standardAffineChartAlgEquiv W).symm
            (coveringChartUniversalPoint W true 1))) = _
    rw [← standardAffineChartAlgEquiv_Y, AlgEquiv.symm_apply_apply]
    have hY := productNeighborhoodAdditionToAffineRing_ordinate W
    change productNeighborhoodAdditionToAffineRing W (secantTargetY W) =
      productNeighborhoodAddY W at hY
    rw [hY]
    rfl
  · change productNeighborhoodSumChartAlgHom W ψ hB
        (coveringChartUniversalPoint W true 2) = 1
    rw [show coveringChartUniversalPoint W true 2 = 1 by
        simpa [coveringCoordinate] using
          coveringChartUniversalPoint_normalized W true,
      map_one]

private theorem productNeighborhoodSum_coordinates_of_X_eq
    (W : WeierstrassCurve K) [DecidableEq K]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hneg : y₁ ≠ W.toAffine.negY x₂ y₂)
    (hB : affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
      (additionB12 W) ≠ 0) :
    chartCoordinates W
        (productNeighborhoodSumChartAlgHom W
          (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB) =
      ![W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂),
        W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂),
        1] := by
  rw [productNeighborhoodSumChartAlgHom_coordinates]
  funext j
  fin_cases j
  · rw [productNeighborhoodToField_addX,
      productNeighborhoodToField_slope_of_X_eq W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg]
    simp
  · rw [productNeighborhoodToField_addY,
      productNeighborhoodToField_slope_of_X_eq W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg]
    simp
  · rfl

private theorem productNeighborhoodSumChartAlgHom_toRingHom
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    (productNeighborhoodSumChartAlgHom W ψ hB).toRingHom =
      (productNeighborhoodToField W ψ hB).toRingHom.comp
        ((productNeighborhoodAdditionToAffineRing W).comp
          (affineEquationToStandardChartRingEquiv W).symm.toRingHom) := by
  rfl

@[reassoc]
private theorem productNeighborhoodPoint_comp_additionAffine
    (W : WeierstrassCurve K)
    (ψ : secantPairCoordinateRing W →ₐ[K] K)
    (hB : ψ (additionB12 W) ≠ 0) :
    Spec.map (CommRingCat.ofHom
          (productNeighborhoodToField W ψ hB).toRingHom) ≫
        productNeighborhoodAdditionAffineMorphism W ≫
          (affineEquationSchemeIsoStandardChart W).hom =
      Spec.map (CommRingCat.ofHom
        (productNeighborhoodSumChartAlgHom W ψ hB).toRingHom) := by
  rw [productNeighborhoodAdditionAffineMorphism]
  rw [show (affineEquationSchemeIsoStandardChart W).hom =
      Spec.map (CommRingCat.ofHom
        (affineEquationToStandardChartRingEquiv W).symm.toRingHom) from rfl]
  rw [← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← productNeighborhoodSumChartAlgHom_toRingHom]
  rfl

private theorem standardPairPoint_addition_productNeighborhood
    (W : WeierstrassCurve K) [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hB : affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
      (additionB12 W) ≠ 0) :
    standardPairPointOver W
          (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) ≫
        projectiveAdditionOver W =
      standardChartPointOver W
        (productNeighborhoodSumChartAlgHom W
          (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, projectiveAdditionOver_left]
  rw [standardPairPointOver_left_eq]
  change
    (Spec.map (CommRingCat.ofHom
          (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true)) ≫
      projectiveAdditionMorphism W =
    Spec.map (CommRingCat.ofHom
      (productNeighborhoodSumChartAlgHom W
        (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB).toRingHom) ≫
    coveringChartMap W true
  calc
    _ = Spec.map (CommRingCat.ofHom
            (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
          (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
            standardPairAdditionMorphism W := by
              simp only [Category.assoc]
              rw [projectivePairStandardChart_comp_projectiveAdditionMorphism]
    _ = (Spec.map (CommRingCat.ofHom
              (affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
            (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
              (standardPairIsoAffinePair W).hom) ≫
          (standardPairIsoAffinePair W).inv ≫
            standardPairAdditionMorphism W := by simp
    _ = Spec.map (CommRingCat.ofHom
            (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
          (standardPairIsoAffinePair W).inv ≫
            standardPairAdditionMorphism W := by
              rw [standardPairEvaluation_comp_affinePairIso]
    _ = Spec.map (CommRingCat.ofHom
            (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫
          affinePairAdditionMorphism W := by
            simpa only [Category.assoc] using congrArg
              (fun q ↦ Spec.map (CommRingCat.ofHom
                (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂).toRingHom) ≫ q)
              (standardPairIsoAffinePair_inv_comp_standardPairAdditionMorphism W)
    _ = (Spec.map (CommRingCat.ofHom
            (productNeighborhoodToField W
              (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB).toRingHom) ≫
          productNeighborhoodToPair W) ≫
            affinePairAdditionMorphism W := by
              rw [productNeighborhoodPoint_factor]
    _ = Spec.map (CommRingCat.ofHom
            (productNeighborhoodToField W
              (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB).toRingHom) ≫
          productNeighborhoodAdditionProjectiveMorphism W := by
            rw [Category.assoc,
              productNeighborhoodToPair_comp_affinePairAdditionMorphism]
    _ = Spec.map (CommRingCat.ofHom
          (productNeighborhoodSumChartAlgHom W
            (affinePairPresentationAlgHom W x₁ y₁ x₂ y₂ h₁ h₂) hB).toRingHom) ≫
        coveringChartMap W true := by
      rw [productNeighborhoodAdditionProjectiveMorphism]
      rw [productNeighborhoodPoint_comp_additionAffine_assoc]
      rfl

private theorem standardPairPoint_addition_affine_of_X_eq
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hneg : y₁ ≠ W.toAffine.negY x₂ y₂) :
    let φ := affinePairChartAlgHom W x₁ y₁ x₂ y₂ h₁ h₂
    standardPairPointOver W φ ≫ projectiveAdditionOver W =
      affinePointOverMorphism W
        (.some
          (W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.addY x₁ x₂ y₁
            (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.nonsingular_add h₁ h₂
            (fun hxy ↦ hneg hxy.2))) := by
  dsimp only
  let hB := affinePairPresentationAlgHom_B12_ne_zero
    W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg
  rw [standardPairPoint_addition_productNeighborhood
    W x₁ y₁ x₂ y₂ h₁ h₂ hB]
  rw [standardChartPointOver_eq_pointOver W _]
  · change pointOverOfNonsingularRepresentative W _ _ =
      pointOverOfNonsingularRepresentative W _ _
    apply pointOverOfNonsingularRepresentative_eq_of_equiv
    rw [productNeighborhoodSum_coordinates_of_X_eq
      W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg]
  · rw [productNeighborhoodSum_coordinates_of_X_eq
      W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg]
    exact W.toProjective.nonsingular_some _ _ |>.mpr
      (W.toAffine.nonsingular_add h₁ h₂ (fun hxy ↦ hneg hxy.2))

private theorem affinePointOverMorphism_add_of_X_eq_of_Y_ne
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hneg : y₁ ≠ W.toAffine.negY x₂ y₂) :
    affinePointOverMorphism W
        ((.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) =
      affinePointOverMorphism W (.some x₁ y₁ h₁) *
        affinePointOverMorphism W (.some x₂ y₂ h₂) := by
  rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hneg]
  change affinePointOverMorphism W (.some _ _ _) =
    lift (affinePointOverMorphism W (.some x₁ y₁ h₁))
        (affinePointOverMorphism W (.some x₂ y₂ h₂)) ≫
      projectiveAdditionOver W
  rw [← standardPairPointOver_affine W x₁ y₁ x₂ y₂ h₁ h₂]
  exact (standardPairPoint_addition_affine_of_X_eq
    W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg).symm

@[simp]
theorem projectivePointOverMorphism_zero_canonical
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePointOverMorphism W 0 =
      (1 : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) := by
  apply (cancel_epi (tensorUnitIsoSelfTestObject (K := K)).hom).1
  rw [tensorUnitIsoSelfTestObject_hom_comp_projectivePointOverMorphism_zero]
  change infinitySectionOver W =
    (tensorUnitIsoSelfTestObject (K := K)).hom ≫
      toUnit (AffineCommGroupScheme.testObject (R := K) K) ≫
        infinitySectionOver W
  simp

@[simp]
private theorem affinePointOverMorphism_zero_canonical
    (W : WeierstrassCurve K) [W.IsElliptic] :
    affinePointOverMorphism W 0 =
      (1 : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) := by
  calc
    affinePointOverMorphism W 0 =
        projectivePointOverMorphism W (0 : W.toProjective.Point) := by
      rw [projectivePointOverMorphism,
        WeierstrassCurve.Projective.Point.toAffineLift_zero]
    _ = 1 := projectivePointOverMorphism_zero_canonical W

private theorem affinePointOverMorphism_neg_canonical
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) :
    affinePointOverMorphism W (-P) =
      (affinePointOverMorphism W P)⁻¹ := by
  rw [affinePointOverMorphism_neg, CategoryTheory.Hom.inv_def]
  rfl

private theorem affinePointOverMorphism_add_of_Y_eq
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ = W.toAffine.negY x₂ y₂) :
    affinePointOverMorphism W
        ((.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) =
      affinePointOverMorphism W (.some x₁ y₁ h₁) *
        affinePointOverMorphism W (.some x₂ y₂ h₂) := by
  have hadd :
      (.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂ = 0 :=
    WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy
  have hneg : (.some x₂ y₂ h₂ : W.toAffine.Point) =
      -(.some x₁ y₁ h₁ : W.toAffine.Point) :=
    eq_neg_of_add_eq_zero_right hadd
  rw [hadd, affinePointOverMorphism_zero_canonical, hneg,
    affinePointOverMorphism_neg_canonical]
  simp

private theorem affinePointOverMorphism_add_canonical
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    (P Q : W.toAffine.Point) :
    affinePointOverMorphism W (P + Q) =
      affinePointOverMorphism W P * affinePointOverMorphism W Q := by
  cases P with
  | zero =>
      change affinePointOverMorphism W Q =
        affinePointOverMorphism W 0 * affinePointOverMorphism W Q
      rw [affinePointOverMorphism_zero_canonical, _root_.one_mul]
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          change affinePointOverMorphism W (.some x₁ y₁ h₁) =
            affinePointOverMorphism W (.some x₁ y₁ h₁) *
              affinePointOverMorphism W 0
          rw [affinePointOverMorphism_zero_canonical, _root_.mul_one]
      | some x₂ y₂ h₂ =>
          by_cases hx : x₁ = x₂
          · by_cases hneg : y₁ ≠ W.toAffine.negY x₂ y₂
            · exact affinePointOverMorphism_add_of_X_eq_of_Y_ne
                W x₁ y₁ x₂ y₂ h₁ h₂ hx hneg
            · exact affinePointOverMorphism_add_of_Y_eq
                W x₁ y₁ x₂ y₂ h₁ h₂ hx (not_ne_iff.mp hneg)
          · exact affinePointOverMorphism_add_of_X_ne
              W x₁ y₁ x₂ y₂ h₁ h₂ hx

/-- The canonical coordinate point map intertwines Mathlib projective
addition with the globally constructed projective group law. -/
theorem projectivePointOverMorphism_add_canonical
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P Q : W.toProjective.Point) :
    projectivePointOverMorphism W (P + Q) =
      projectivePointOverMorphism W P * projectivePointOverMorphism W Q := by
  classical
  change affinePointOverMorphism W (P + Q).toAffineLift =
    affinePointOverMorphism W P.toAffineLift *
      affinePointOverMorphism W Q.toAffineLift
  rw [WeierstrassCurve.Projective.Point.toAffineLift_add]
  exact affinePointOverMorphism_add_canonical W P.toAffineLift Q.toAffineLift

/-- Canonical pointwise addition compatibility for the projective
Weierstrass group object.  Its named downstream consumer is the
order-49 split `Gamma₀` construction. -/
theorem canonicalPointGroupLawCompatibility
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic] :
    CanonicalPointGroupLawCompatibility W where
  map_add := by
    intro _ P Q
    change projectivePointOverMorphism W (P + Q) =
      projectivePointOverMorphism W P * projectivePointOverMorphism W Q
    exact projectivePointOverMorphism_add_canonical W P Q

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
