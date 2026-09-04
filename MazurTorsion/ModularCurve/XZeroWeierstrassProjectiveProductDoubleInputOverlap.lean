/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductRegularCover
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The double input overlap of projective Weierstrass pair charts

The locus where both infinity-chart inputs also enter the standard chart is
the tensor square of the exact cubic overlap.  This file realizes that ring as
an iterated tensor localization, maps its spectrum by open immersions to the
standard-by-standard and infinity-by-infinity pair charts, and identifies the
corresponding basic opens in their affine presentations.

The design boundary is an actual geometric source for the both-standard term
in `projectiveInfinityPairStandardNeighborhoodAndSecantZOpens_cover`.  Its
named downstream consumers `projectivePairDoubleOverlapToStandardPair` and
`projectivePairDoubleOverlapToInfinityPair` let the global addition atlas put
the already-checked standard-pair law on that term.  Equality of their maps
into the full product is proved in the next compatibility layer.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem isLocalizationAway_tensorProduct_right_again
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra K A] [Algebra K B] [Algebra K S]
    (f : A →ₐ[K] B) (r : A)
    (h : letI := f.toAlgebra; IsLocalization.Away r B) :
    letI := (Algebra.TensorProduct.map (AlgHom.id K S) f).toAlgebra
    IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K) (A := S) (B := A) r)
      (TensorProduct K S B) := by
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  letI : IsLocalization.Away r B := h
  letI : Algebra (TensorProduct K S A) (TensorProduct K S B) :=
    (Algebra.TensorProduct.map (AlgHom.id K S) f).toAlgebra
  letI : IsScalarTower S (TensorProduct K S A)
      (TensorProduct K S B) := by
    constructor
    intro a x y
    change (Algebra.TensorProduct.map (AlgHom.id K S) f) (a • x) * y =
      a • ((Algebra.TensorProduct.map (AlgHom.id K S) f) x * y)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
        change ((a * b) ⊗ₜ[K] f c) * y =
          a • ((b ⊗ₜ[K] f c) * y)
        rw [← smul_mul_assoc, TensorProduct.smul_tmul']
        rfl
    | add x z hx hz =>
        simp [smul_add, map_add, add_mul, hx, hz]
  change IsLocalization
    (Submonoid.powers
      (Algebra.TensorProduct.includeRight
        (R := K) (A := S) (B := A) r))
    (TensorProduct K S B)
  rw [← Submonoid.map_powers]
  refine IsLocalization.tensorProduct_tensorProduct_right K S
    (Submonoid.powers r) B ?_
  apply RingHom.ext
  intro x
  change (Algebra.TensorProduct.map (AlgHom.id K S) f)
      (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight (f x)
  have hx := congrArg (fun g ↦ g x)
    (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id K S) f)
  exact hx

/-! ## Coordinate rings and transition maps -/

/-- Tensor square of the exact standard/infinity cubic overlap. -/
abbrev projectivePairDoubleChartOverlapCoordinateRing
    (W : WeierstrassCurve K) :=
  TensorProduct K (coveringChartOverlapCoordinateRing W)
    (coveringChartOverlapCoordinateRing W)

/-- After restricting the first infinity input, restrict the second one too. -/
noncomputable def firstInfinityOverlapToDoubleOverlapAlgHom
    (W : WeierstrassCurve K) :
    projectivePairFirstChartOverlapCoordinateRing W false →ₐ[K]
      projectivePairDoubleChartOverlapCoordinateRing W :=
  Algebra.TensorProduct.map
    (AlgHom.id K (coveringChartOverlapCoordinateRing W))
    (infinityChartToCoveringChartOverlapAlgHom W)

/-- Restrict both inputs of the infinity-by-infinity pair chart to the exact
double overlap. -/
noncomputable def infinityPairToDoubleOverlapAlgHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W →ₐ[K]
      projectivePairDoubleChartOverlapCoordinateRing W :=
  (firstInfinityOverlapToDoubleOverlapAlgHom W).comp
    (infinityPairToFirstChartOverlapAlgHom W false)

/-- After restricting the first standard input, restrict the second one too. -/
noncomputable def firstStandardOverlapToDoubleOverlapAlgHom
    (W : WeierstrassCurve K) :
    projectivePairFirstChartOverlapCoordinateRing W true →ₐ[K]
      projectivePairDoubleChartOverlapCoordinateRing W :=
  Algebra.TensorProduct.map
    (AlgHom.id K (coveringChartOverlapCoordinateRing W))
    (standardChartToCoveringChartOverlapAlgHom W)

/-- Restrict both inputs of the standard-by-standard pair chart to the exact
double overlap. -/
noncomputable def standardPairToDoubleOverlapAlgHom
    (W : WeierstrassCurve K) :
    projectivePairChartCoordinateRing W (true, true) →ₐ[K]
      projectivePairDoubleChartOverlapCoordinateRing W :=
  (firstStandardOverlapToDoubleOverlapAlgHom W).comp
    (standardPairToFirstChartOverlapAlgHom W true)

/-! ## Localization on the infinity side -/

private theorem doubleOverlap_isLocalization_secondInfinityOverlap
    (W : WeierstrassCurve K) :
    letI := (firstInfinityOverlapToDoubleOverlapAlgHom W).toAlgebra
    IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairDoubleChartOverlapCoordinateRing W) := by
  exact isLocalizationAway_tensorProduct_right_again
    (f := infinityChartToCoveringChartOverlapAlgHom W)
    (r := Ideal.Quotient.mk (coveringChartIdeal W false)
      (coordinateChartRatio (K := K) 1 2))
    (coveringChartOverlap_isLocalization_infinityChart W)

/-- The double overlap is the infinity-pair ring localized where the product
of its two `Z / Y` input coordinates is invertible. -/
theorem projectivePairDoubleOverlap_isLocalization_infinityPair
    (W : WeierstrassCurve K) :
    letI := (infinityPairToDoubleOverlapAlgHom W).toAlgebra
    IsLocalization.Away
      (projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W)
      (projectivePairDoubleChartOverlapCoordinateRing W) := by
  let I := projectivePairFirstChartOverlapCoordinateRing W false
  let D := projectivePairDoubleChartOverlapCoordinateRing W
  let R := projectiveInfinityPairCoordinateRing W
  letI : Algebra I D :=
    (firstInfinityOverlapToDoubleOverlapAlgHom W).toAlgebra
  haveI hSecond : IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2))) D :=
    doubleOverlap_isLocalization_secondInfinityOverlap W
  haveI hFirst : IsLocalization.Away
      (projectiveInfinityPairZ₁ W) I := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W false)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2))) I
    exact projectivePairFirstOverlap_isLocalization_infinityPair W false
  letI : Algebra R D := (infinityPairToDoubleOverlapAlgHom W).toAlgebra
  letI : IsScalarTower R I D :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hZ₂ :
      algebraMap R I (projectiveInfinityPairZ₂ W) =
        Algebra.TensorProduct.includeRight
          (R := K)
          (A := coveringChartOverlapCoordinateRing W)
          (B := coveringChartCoordinateRing W false)
          (Ideal.Quotient.mk (coveringChartIdeal W false)
            (coordinateChartRatio (K := K) 1 2)) := by
    change infinityPairToFirstChartOverlapAlgHom W false
        (projectiveInfinityPairZ₂ W) = _
    rw [infinityPairToFirstChartOverlapAlgHom_secondUniversalPoint]
    rfl
  haveI hSecond' : IsLocalization.Away
      (algebraMap R I (projectiveInfinityPairZ₂ W)) D := by
    rw [hZ₂]
    exact hSecond
  exact IsLocalization.Away.mul'
    I D (projectiveInfinityPairZ₁ W) (projectiveInfinityPairZ₂ W)

/-! ## Localization on the standard side -/

/-- The second standard factor can be localized after the first factor has
already entered the exact chart overlap.  The downstream global-addition
consumer uses this boundary to view the double overlap as an open subscheme
of either mixed pair chart. -/
theorem doubleOverlap_isLocalization_secondStandardOverlap
    (W : WeierstrassCurve K) :
    letI := (firstStandardOverlapToDoubleOverlapAlgHom W).toAlgebra
    IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1)))
      (projectivePairDoubleChartOverlapCoordinateRing W) := by
  exact isLocalizationAway_tensorProduct_right_again
    (f := standardChartToCoveringChartOverlapAlgHom W)
    (r := Ideal.Quotient.mk (coveringChartIdeal W true)
      (coordinateChartRatio (K := K) 2 1))
    (coveringChartOverlap_isLocalization_standardChart W)

/-- The double overlap is the standard-pair ring localized where the product
of its two `Y / Z` input coordinates is invertible. -/
theorem projectivePairDoubleOverlap_isLocalization_standardPair
    (W : WeierstrassCurve K) :
    letI := (standardPairToDoubleOverlapAlgHom W).toAlgebra
    IsLocalization.Away
      (projectivePairChartFirstUniversalPoint W (true, true) (1 : Fin 3) *
        projectivePairChartSecondUniversalPoint W (true, true) (1 : Fin 3))
      (projectivePairDoubleChartOverlapCoordinateRing W) := by
  let I := projectivePairFirstChartOverlapCoordinateRing W true
  let D := projectivePairDoubleChartOverlapCoordinateRing W
  let R := projectivePairChartCoordinateRing W (true, true)
  letI : Algebra I D :=
    (firstStandardOverlapToDoubleOverlapAlgHom W).toAlgebra
  haveI hSecond : IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1))) D :=
    doubleOverlap_isLocalization_secondStandardOverlap W
  haveI hFirst : IsLocalization.Away
      (projectivePairChartFirstUniversalPoint W (true, true)
        (1 : Fin 3)) I := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (K := K) 2 1))) I
    exact projectivePairFirstOverlap_isLocalization_standardPair W true
  letI : Algebra R D := (standardPairToDoubleOverlapAlgHom W).toAlgebra
  letI : IsScalarTower R I D :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hY₂ : algebraMap R I
      (projectivePairChartSecondUniversalPoint W (true, true)
        (1 : Fin 3)) =
        Algebra.TensorProduct.includeRight
          (R := K)
          (A := coveringChartOverlapCoordinateRing W)
          (B := coveringChartCoordinateRing W true)
          (Ideal.Quotient.mk (coveringChartIdeal W true)
            (coordinateChartRatio (K := K) 2 1)) := by
    change standardPairToFirstChartOverlapAlgHom W true
        (projectivePairChartSecondUniversalPoint W (true, true)
          (1 : Fin 3)) = _
    rw [standardPairToFirstChartOverlapAlgHom_secondUniversalPoint]
    rfl
  haveI hSecond' : IsLocalization.Away
      (algebraMap R I
        (projectivePairChartSecondUniversalPoint W (true, true)
          (1 : Fin 3))) D := by
    rw [hY₂]
    exact hSecond
  exact IsLocalization.Away.mul' I D
    (projectivePairChartFirstUniversalPoint W (true, true) (1 : Fin 3))
    (projectivePairChartSecondUniversalPoint W (true, true) (1 : Fin 3))

/-! ## Actual double-overlap schemes -/

/-- Spectrum of the exact double input overlap. -/
abbrev projectivePairDoubleChartOverlapScheme
    (W : WeierstrassCurve K) : Scheme.{u} :=
  Spec (.of (projectivePairDoubleChartOverlapCoordinateRing W))

/-- Map the double overlap into the standard-by-standard pair chart. -/
noncomputable def projectivePairDoubleOverlapToStandardPair
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairChartScheme W (true, true) :=
  Spec.map (CommRingCat.ofHom
      (standardPairToDoubleOverlapAlgHom W).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (true, true)).inv

instance projectivePairDoubleOverlapToStandardPair_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectivePairDoubleOverlapToStandardPair W) := by
  letI := (standardPairToDoubleOverlapAlgHom W).toAlgebra
  haveI := projectivePairDoubleOverlap_isLocalization_standardPair W
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (standardPairToDoubleOverlapAlgHom W).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (projectivePairChartFirstUniversalPoint W (true, true) (1 : Fin 3) *
        projectivePairChartSecondUniversalPoint W (true, true) (1 : Fin 3))
  dsimp only [projectivePairDoubleOverlapToStandardPair]
  infer_instance

/-- Map the double overlap into the infinity-by-infinity pair chart. -/
noncomputable def projectivePairDoubleOverlapToInfinityPair
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairChartScheme W (false, false) :=
  Spec.map (CommRingCat.ofHom
      (infinityPairToDoubleOverlapAlgHom W).toRingHom) ≫
    (projectivePairChartIsoSpecTensor W (false, false)).inv

instance projectivePairDoubleOverlapToInfinityPair_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectivePairDoubleOverlapToInfinityPair W) := by
  letI := (infinityPairToDoubleOverlapAlgHom W).toAlgebra
  haveI := projectivePairDoubleOverlap_isLocalization_infinityPair W
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (infinityPairToDoubleOverlapAlgHom W).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W)
  dsimp only [projectivePairDoubleOverlapToInfinityPair]
  infer_instance

@[reassoc]
theorem projectivePairDoubleOverlapToStandardPair_comp_iso_hom
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToStandardPair W ≫
        (projectivePairChartIsoSpecTensor W (true, true)).hom =
      Spec.map (CommRingCat.ofHom
        (standardPairToDoubleOverlapAlgHom W).toRingHom) := by
  simp [projectivePairDoubleOverlapToStandardPair]

@[reassoc]
theorem projectivePairDoubleOverlapToInfinityPair_comp_iso_hom
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToInfinityPair W ≫
        (projectivePairChartIsoSpecTensor W (false, false)).hom =
      Spec.map (CommRingCat.ofHom
        (infinityPairToDoubleOverlapAlgHom W).toRingHom) := by
  simp [projectivePairDoubleOverlapToInfinityPair]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
