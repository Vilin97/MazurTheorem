/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductDoubleInputOverlap

/-!
# Compatibility of the double projective-pair input overlap

The tensor square of the exact cubic chart overlap has two intrinsic
projections back to that cubic overlap.  This file checks both projections
against the standard-by-standard and infinity-by-infinity pair-chart maps.
Pullback extensionality then proves that the two chart descriptions of the
double overlap have the same composite into the full projective product.

The design boundary is the actual both-standard member of the regular
infinity-pair cover.  The named downstream consumer
`projectivePairDoubleOverlap_maps_eq` makes its source embedding independent
of which adjacent pair chart is used, so a later addition atlas can transport
the checked standard-pair law onto this open without an abstract-intersection
choice.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The two intrinsic overlap projections -/

/-- First projection from the double input overlap to the cubic chart
overlap. -/
noncomputable def projectivePairDoubleOverlapFst
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      coveringChartOverlapScheme W :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom
      (R := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartOverlapCoordinateRing W)))

/-- Second projection from the double input overlap to the cubic chart
overlap. -/
noncomputable def projectivePairDoubleOverlapSnd
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      coveringChartOverlapScheme W :=
  Spec.map (CommRingCat.ofHom
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartOverlapCoordinateRing W))))

private theorem projectivePairChartIsoSpecTensor_inv_fst_again
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).inv ≫
        pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom
          (R := K)
          (A := coveringChartCoordinateRing W ij.1)
          (B := coveringChartCoordinateRing W ij.2))) := by
  rw [← projectivePairChartIsoSpecTensor_hom_fst W ij]
  simp

private theorem projectivePairChartIsoSpecTensor_inv_snd_again
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).inv ≫
        pullback.snd
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) =
      Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := K)
            (A := coveringChartCoordinateRing W ij.1)
            (B := coveringChartCoordinateRing W ij.2)))) := by
  rw [← projectivePairChartIsoSpecTensor_hom_snd W ij]
  simp

/-! ## Coordinate-ring projection formulas -/

@[simp]
theorem standardPairToDoubleOverlapAlgHom_includeLeft
    (W : WeierstrassCurve K)
    (x : coveringChartCoordinateRing W true) :
    standardPairToDoubleOverlapAlgHom W
        (Algebra.TensorProduct.includeLeft
          (R := K) (S := K)
          (A := coveringChartCoordinateRing W true)
          (B := coveringChartCoordinateRing W true) x) =
      Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartOverlapCoordinateRing W)
        (standardChartToCoveringChartOverlapRing W x) := by
  simp [standardPairToDoubleOverlapAlgHom,
    firstStandardOverlapToDoubleOverlapAlgHom,
    standardPairToFirstChartOverlapAlgHom]
  rfl

@[simp]
theorem standardPairToDoubleOverlapAlgHom_includeRight
    (W : WeierstrassCurve K)
    (x : coveringChartCoordinateRing W true) :
    standardPairToDoubleOverlapAlgHom W
        (Algebra.TensorProduct.includeRight
          (R := K)
          (A := coveringChartCoordinateRing W true)
          (B := coveringChartCoordinateRing W true) x) =
      Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartOverlapCoordinateRing W)
        (standardChartToCoveringChartOverlapRing W x) := by
  simp [standardPairToDoubleOverlapAlgHom,
    firstStandardOverlapToDoubleOverlapAlgHom,
    standardPairToFirstChartOverlapAlgHom]
  rfl

@[simp]
theorem infinityPairToDoubleOverlapAlgHom_includeLeft
    (W : WeierstrassCurve K)
    (x : coveringChartCoordinateRing W false) :
    infinityPairToDoubleOverlapAlgHom W
        (Algebra.TensorProduct.includeLeft
          (R := K) (S := K)
          (A := coveringChartCoordinateRing W false)
          (B := coveringChartCoordinateRing W false) x) =
      Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartOverlapCoordinateRing W)
        (infinityChartToCoveringChartOverlapRing W x) := by
  simp [infinityPairToDoubleOverlapAlgHom,
    firstInfinityOverlapToDoubleOverlapAlgHom,
    infinityPairToFirstChartOverlapAlgHom]
  rfl

@[simp]
theorem infinityPairToDoubleOverlapAlgHom_includeRight
    (W : WeierstrassCurve K)
    (x : coveringChartCoordinateRing W false) :
    infinityPairToDoubleOverlapAlgHom W
        (Algebra.TensorProduct.includeRight
          (R := K)
          (A := coveringChartCoordinateRing W false)
          (B := coveringChartCoordinateRing W false) x) =
      Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartOverlapCoordinateRing W)
        (B := coveringChartOverlapCoordinateRing W)
        (infinityChartToCoveringChartOverlapRing W x) := by
  simp [infinityPairToDoubleOverlapAlgHom,
    firstInfinityOverlapToDoubleOverlapAlgHom,
    infinityPairToFirstChartOverlapAlgHom]
  rfl

/-! ## Projection compatibility in the two pair charts -/

@[reassoc]
theorem projectivePairDoubleOverlapToStandardPair_comp_fst
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToStandardPair W ≫
        pullback.fst
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) =
      projectivePairDoubleOverlapFst W ≫
        coveringChartOverlapToStandardChart W := by
  rw [projectivePairDoubleOverlapToStandardPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_fst_again,
    projectivePairDoubleOverlapFst,
    coveringChartOverlapToStandardChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact standardPairToDoubleOverlapAlgHom_includeLeft W x

@[reassoc]
theorem projectivePairDoubleOverlapToInfinityPair_comp_fst
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToInfinityPair W ≫
        pullback.fst
          (coveringChartMap W false ≫ structureMap W)
          (coveringChartMap W false ≫ structureMap W) =
      projectivePairDoubleOverlapFst W ≫
        coveringChartOverlapToInfinityChart W := by
  rw [projectivePairDoubleOverlapToInfinityPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_fst_again,
    projectivePairDoubleOverlapFst,
    coveringChartOverlapToInfinityChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact infinityPairToDoubleOverlapAlgHom_includeLeft W x

@[reassoc]
theorem projectivePairDoubleOverlapToStandardPair_comp_snd
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToStandardPair W ≫
        pullback.snd
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) =
      projectivePairDoubleOverlapSnd W ≫
        coveringChartOverlapToStandardChart W := by
  rw [projectivePairDoubleOverlapToStandardPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_snd_again,
    projectivePairDoubleOverlapSnd,
    coveringChartOverlapToStandardChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact standardPairToDoubleOverlapAlgHom_includeRight W x

@[reassoc]
theorem projectivePairDoubleOverlapToInfinityPair_comp_snd
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToInfinityPair W ≫
        pullback.snd
          (coveringChartMap W false ≫ structureMap W)
          (coveringChartMap W false ≫ structureMap W) =
      projectivePairDoubleOverlapSnd W ≫
        coveringChartOverlapToInfinityChart W := by
  rw [projectivePairDoubleOverlapToInfinityPair, Category.assoc,
    projectivePairChartIsoSpecTensor_inv_snd_again,
    projectivePairDoubleOverlapSnd,
    coveringChartOverlapToInfinityChart,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact infinityPairToDoubleOverlapAlgHom_includeRight W x

/-! ## Equality inside the full projective product -/

/-- The standard and infinity descriptions of the exact double overlap are
the same open subscheme of the full projective product. -/
theorem projectivePairDoubleOverlap_maps_eq
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToStandardPair W ≫
        projectivePairChartMap W (true, true) =
      projectivePairDoubleOverlapToInfinityPair W ≫
        projectivePairChartMap W (false, false) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, projectivePairChartMap_comp_fst]
    rw [← Category.assoc,
      projectivePairDoubleOverlapToStandardPair_comp_fst,
      ← Category.assoc,
      projectivePairDoubleOverlapToInfinityPair_comp_fst,
      Category.assoc, Category.assoc,
      coveringChartOverlap_maps_eq]
  · simp only [Category.assoc, projectivePairChartMap_comp_snd]
    rw [← Category.assoc,
      projectivePairDoubleOverlapToStandardPair_comp_snd,
      ← Category.assoc,
      projectivePairDoubleOverlapToInfinityPair_comp_snd,
      Category.assoc, Category.assoc,
      coveringChartOverlap_maps_eq]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
