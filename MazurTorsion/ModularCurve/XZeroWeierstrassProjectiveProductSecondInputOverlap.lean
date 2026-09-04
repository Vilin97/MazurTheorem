/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductFirstInputOverlap

/-!
# The second input overlap of projective Weierstrass pair charts

This file tensors the exact standard/infinity cubic overlap on the second
factor with an unchanged first chart.  The two second normalized universal
inputs differ by the transition scalar `Y/Z`, while the first inputs agree.

The design boundary is the resulting homogeneity law for the raw addition
triple.  Its named downstream consumer,
`projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition`,
supplies the symmetric source-overlap edge needed to construct actual
projective-pair overlap maps and glue normalized local addition morphisms.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Tensor an unchanged first chart with the cubic overlap. -/
abbrev projectivePairSecondChartOverlapCoordinateRing
    (W : WeierstrassCurve K) (i : Bool) :=
  TensorProduct K (coveringChartCoordinateRing W i)
    (coveringChartOverlapCoordinateRing W)

/-- Restrict the `i`-by-standard pair chart to the second-factor overlap. -/
noncomputable def standardPairToSecondChartOverlapAlgHom
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairChartCoordinateRing W (i, true) →ₐ[K]
      projectivePairSecondChartOverlapCoordinateRing W i :=
  Algebra.TensorProduct.map
    (AlgHom.id K (coveringChartCoordinateRing W i))
    (standardChartToCoveringChartOverlapAlgHom W)

/-- Restrict the `i`-by-infinity pair chart to the second-factor overlap. -/
noncomputable def infinityPairToSecondChartOverlapAlgHom
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairChartCoordinateRing W (i, false) →ₐ[K]
      projectivePairSecondChartOverlapCoordinateRing W i :=
  Algebra.TensorProduct.map
    (AlgHom.id K (coveringChartCoordinateRing W i))
    (infinityChartToCoveringChartOverlapAlgHom W)

/-- The second-factor transition scalar in the pair-overlap ring. -/
noncomputable def projectivePairSecondChartOverlapScale
    (W : WeierstrassCurve K) (i : Bool) :
    projectivePairSecondChartOverlapCoordinateRing W i :=
  Algebra.TensorProduct.includeRight
    (R := K)
    (A := coveringChartCoordinateRing W i)
    (B := coveringChartOverlapCoordinateRing W)
    (coveringChartOverlapScale W)

@[simp]
theorem standardPairToSecondChartOverlapAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (i : Bool) (k : Fin 3) :
    standardPairToSecondChartOverlapAlgHom W i
        (projectivePairChartFirstUniversalPoint W (i, true) k) =
      Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartOverlapCoordinateRing W)
        (coveringChartUniversalPoint W i k) := by
  change ((Algebra.TensorProduct.map
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (standardChartToCoveringChartOverlapAlgHom W)).comp
        Algebra.TensorProduct.includeLeft)
      (coveringChartUniversalPoint W i k) = _
  rw [Algebra.TensorProduct.map_comp_includeLeft]
  rfl

@[simp]
theorem infinityPairToSecondChartOverlapAlgHom_firstUniversalPoint
    (W : WeierstrassCurve K) (i : Bool) (k : Fin 3) :
    infinityPairToSecondChartOverlapAlgHom W i
        (projectivePairChartFirstUniversalPoint W (i, false) k) =
      Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartOverlapCoordinateRing W)
        (coveringChartUniversalPoint W i k) := by
  change ((Algebra.TensorProduct.map
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (infinityChartToCoveringChartOverlapAlgHom W)).comp
        Algebra.TensorProduct.includeLeft)
      (coveringChartUniversalPoint W i k) = _
  rw [Algebra.TensorProduct.map_comp_includeLeft]
  rfl

@[simp]
theorem standardPairToSecondChartOverlapAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (i : Bool) (k : Fin 3) :
    standardPairToSecondChartOverlapAlgHom W i
        (projectivePairChartSecondUniversalPoint W (i, true) k) =
      Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartOverlapCoordinateRing W)
        (standardChartToCoveringChartOverlapRing W
          (coveringChartUniversalPoint W true k)) := by
  change ((Algebra.TensorProduct.map
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (standardChartToCoveringChartOverlapAlgHom W)).comp
        Algebra.TensorProduct.includeRight)
      (coveringChartUniversalPoint W true k) = _
  rw [Algebra.TensorProduct.map_comp_includeRight]
  rfl

@[simp]
theorem infinityPairToSecondChartOverlapAlgHom_secondUniversalPoint
    (W : WeierstrassCurve K) (i : Bool) (k : Fin 3) :
    infinityPairToSecondChartOverlapAlgHom W i
        (projectivePairChartSecondUniversalPoint W (i, false) k) =
      Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W i)
        (B := coveringChartOverlapCoordinateRing W)
        (infinityChartToCoveringChartOverlapRing W
          (coveringChartUniversalPoint W false k)) := by
  change ((Algebra.TensorProduct.map
      (AlgHom.id K (coveringChartCoordinateRing W i))
      (infinityChartToCoveringChartOverlapAlgHom W)).comp
        Algebra.TensorProduct.includeRight)
      (coveringChartUniversalPoint W false k) = _
  rw [Algebra.TensorProduct.map_comp_includeRight]
  rfl

/-- The unchanged first universal input restricts identically from the two
adjacent pair charts. -/
theorem projectivePairSecondChartOverlap_standardFirstPoint_eq_infinityFirstPoint
    (W : WeierstrassCurve K) (i : Bool) :
    standardPairToSecondChartOverlapAlgHom W i ∘
        projectivePairChartFirstUniversalPoint W (i, true) =
      infinityPairToSecondChartOverlapAlgHom W i ∘
        projectivePairChartFirstUniversalPoint W (i, false) := by
  funext k
  exact
    (standardPairToSecondChartOverlapAlgHom_firstUniversalPoint W i k).trans
      (infinityPairToSecondChartOverlapAlgHom_firstUniversalPoint W i k).symm

/-- The second universal pair input obeys the expected projective transition
law on the common second-factor overlap. -/
theorem projectivePairSecondChartOverlap_standardSecondPoint_eq_smul_infinitySecondPoint
    (W : WeierstrassCurve K) (i : Bool) :
    standardPairToSecondChartOverlapAlgHom W i ∘
        projectivePairChartSecondUniversalPoint W (i, true) =
      projectivePairSecondChartOverlapScale W i •
        (infinityPairToSecondChartOverlapAlgHom W i ∘
          projectivePairChartSecondUniversalPoint W (i, false)) := by
  funext k
  change standardPairToSecondChartOverlapAlgHom W i
      (projectivePairChartSecondUniversalPoint W (i, true) k) =
    projectivePairSecondChartOverlapScale W i *
      infinityPairToSecondChartOverlapAlgHom W i
        (projectivePairChartSecondUniversalPoint W (i, false) k)
  rw [standardPairToSecondChartOverlapAlgHom_secondUniversalPoint,
    infinityPairToSecondChartOverlapAlgHom_secondUniversalPoint,
    projectivePairSecondChartOverlapScale]
  rw [← map_mul]
  exact congrArg
    (Algebra.TensorProduct.includeRight
      (R := K)
      (A := coveringChartCoordinateRing W i)
      (B := coveringChartOverlapCoordinateRing W))
    (congrFun
      (coveringChartOverlap_standardPoint_eq_smul_infinityPoint W) k)

private theorem projectivePairChartAdditionCoordinates_second_map
    {A : Type u} [CommRing A] [Algebra K A]
    (W : WeierstrassCurve K) (ij : Bool × Bool)
    (f : projectivePairChartCoordinateRing W ij →ₐ[K] A) :
    f ∘ projectivePairChartAdditionCoordinates W ij =
      (W.map (algebraMap K A)).toProjective.addXYZ
        (f ∘ projectivePairChartFirstUniversalPoint W ij)
        (f ∘ projectivePairChartSecondUniversalPoint W ij) := by
  have h := WeierstrassCurve.Projective.map_addXYZ
    (W' := projectivePairChartMappedCurve W ij)
    (f := f.toRingHom)
    (P := projectivePairChartFirstUniversalPoint W ij)
    (Q := projectivePairChartSecondUniversalPoint W ij)
  have hf : f.toRingHom.comp
      (algebraMap K (projectivePairChartCoordinateRing W ij)) =
        algebraMap K A := by
    ext a
    exact f.commutes a
  change ((W.map
      (algebraMap K (projectivePairChartCoordinateRing W ij))).map
        f.toRingHom).toProjective.addXYZ _ _ = _ at h
  rw [WeierstrassCurve.map_map, hf] at h
  exact h.symm

/-- The raw secant triple is compatible with the second input-chart
transition: changing the second normalized representative multiplies all
three output coordinates by the square of the transition scalar. -/
theorem projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition
    (W : WeierstrassCurve K) (i : Bool) :
    standardPairToSecondChartOverlapAlgHom W i ∘
        projectivePairChartAdditionCoordinates W (i, true) =
      projectivePairSecondChartOverlapScale W i ^ 2 •
        (infinityPairToSecondChartOverlapAlgHom W i ∘
          projectivePairChartAdditionCoordinates W (i, false)) := by
  rw [projectivePairChartAdditionCoordinates_second_map,
    projectivePairChartAdditionCoordinates_second_map,
    projectivePairSecondChartOverlap_standardFirstPoint_eq_infinityFirstPoint,
    projectivePairSecondChartOverlap_standardSecondPoint_eq_smul_infinitySecondPoint]
  have h := (W.map (algebraMap K
      (projectivePairSecondChartOverlapCoordinateRing W i))).toProjective.addXYZ_smul
    (infinityPairToSecondChartOverlapAlgHom W i ∘
      projectivePairChartFirstUniversalPoint W (i, false))
    (infinityPairToSecondChartOverlapAlgHom W i ∘
      projectivePairChartSecondUniversalPoint W (i, false))
    1 (projectivePairSecondChartOverlapScale W i)
  simpa only [one_smul, one_mul] using h

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
