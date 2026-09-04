/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductChartRings

/-!
# Universal points on the projective Weierstrass product charts

The two affine charts of the projective cubic carry canonical normalized
homogeneous coordinates.  This file constructs those coordinates in the
quotient chart rings, proves that they satisfy the mapped homogeneous
Weierstrass equation, and then embeds the two universal input points into each
tensor-product chart ring of the projective pair.

These universal points are the algebraic inputs for the missing local addition
formulas.  Their normalization records which homogeneous coordinate is one,
while their equation theorems let later polynomial identities reduce modulo
the two defining cubic equations without introducing point-valued shadows.
-/

noncomputable section

open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The normalized homogeneous point with values in one cubic chart's
coordinate ring. -/
noncomputable def coveringChartUniversalPoint
    (W : WeierstrassCurve K) (b : Bool) :
    Fin 3 → coveringChartCoordinateRing W b :=
  fun j ↦ Ideal.Quotient.mk (coveringChartIdeal W b)
    (coordinateChartRatio (coveringCoordinate b) j)

/-- The distinguished coordinate of the normalized universal chart point is
one. -/
@[simp]
theorem coveringChartUniversalPoint_normalized
    (W : WeierstrassCurve K) (b : Bool) :
    coveringChartUniversalPoint W b (coveringCoordinate b) = 1 := by
  simp [coveringChartUniversalPoint]

/-- The universal normalized chart point satisfies the homogeneous cubic
equation after mapping coefficients into the chart ring. -/
theorem coveringChartUniversalPoint_equation
    (W : WeierstrassCurve K) (b : Bool) :
    (W.map (coveringChartStructureRingHom W b)).toProjective.Equation
      (coveringChartUniversalPoint W b) := by
  rw [WeierstrassCurve.Projective.Equation,
    WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom
      (coveringChartStructureRingHom W b)
      (coveringChartUniversalPoint W b)
      W.toProjective.polynomial = 0
  rw [coveringChartStructureRingHom]
  change MvPolynomial.eval₂Hom
      ((Ideal.Quotient.mk (coveringChartIdeal W b)).comp
        (coordinateChartConstantHom (coveringCoordinate b)))
      (fun j ↦ Ideal.Quotient.mk (coveringChartIdeal W b)
        (coordinateChartRatio (coveringCoordinate b) j))
      W.toProjective.polynomial = 0
  rw [← MvPolynomial.map_eval₂Hom]
  rw [← coordinateChartAwayMk_eq_eval₂Hom
    (coveringCoordinate b) W.toProjective.polynomial
    (polynomial_mem_degree_three W)]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  cases b <;> exact Ideal.subset_span (Set.mem_singleton _)

/-- The first universal input point on a projective-pair chart. -/
noncomputable def projectivePairChartFirstUniversalPoint
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Fin 3 → projectivePairChartCoordinateRing W ij :=
  fun j ↦ Algebra.TensorProduct.includeLeft
    (R := K) (S := K)
    (A := coveringChartCoordinateRing W ij.1)
    (B := coveringChartCoordinateRing W ij.2)
    (coveringChartUniversalPoint W ij.1 j)

/-- The second universal input point on a projective-pair chart. -/
noncomputable def projectivePairChartSecondUniversalPoint
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Fin 3 → projectivePairChartCoordinateRing W ij :=
  fun j ↦ Algebra.TensorProduct.includeRight
    (R := K)
    (A := coveringChartCoordinateRing W ij.1)
    (B := coveringChartCoordinateRing W ij.2)
    (coveringChartUniversalPoint W ij.2 j)

/-- The first universal input retains the normalization of its source chart. -/
@[simp]
theorem projectivePairChartFirstUniversalPoint_normalized
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartFirstUniversalPoint W ij (coveringCoordinate ij.1) = 1 := by
  rw [projectivePairChartFirstUniversalPoint,
    coveringChartUniversalPoint_normalized]
  rfl

/-- The second universal input retains the normalization of its source chart. -/
@[simp]
theorem projectivePairChartSecondUniversalPoint_normalized
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartSecondUniversalPoint W ij (coveringCoordinate ij.2) = 1 := by
  rw [projectivePairChartSecondUniversalPoint,
    coveringChartUniversalPoint_normalized]
  rfl

/-- The first universal input satisfies the cubic equation over the common
tensor-product coefficient ring. -/
theorem projectivePairChartFirstUniversalPoint_equation
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (W.map (algebraMap K (projectivePairChartCoordinateRing W ij))).toProjective.Equation
      (projectivePairChartFirstUniversalPoint W ij) := by
  let f := Algebra.TensorProduct.includeLeftRingHom
    (R := K)
    (A := coveringChartCoordinateRing W ij.1)
    (B := coveringChartCoordinateRing W ij.2)
  have h := (coveringChartUniversalPoint_equation W ij.1).map f
  have hf : f.comp (coveringChartStructureRingHom W ij.1) =
      algebraMap K (projectivePairChartCoordinateRing W ij) := by
    rw [← coveringChartCoordinateRing_algebraMap]
    rfl
  change ((W.map (coveringChartStructureRingHom W ij.1)).map f).toProjective.Equation
    (f ∘ coveringChartUniversalPoint W ij.1) at h
  rw [WeierstrassCurve.map_map, hf] at h
  have hp : f ∘ coveringChartUniversalPoint W ij.1 =
      projectivePairChartFirstUniversalPoint W ij := by
    funext j
    rfl
  rw [hp] at h
  exact h

/-- The second universal input satisfies the cubic equation over the common
tensor-product coefficient ring. -/
theorem projectivePairChartSecondUniversalPoint_equation
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (W.map (algebraMap K (projectivePairChartCoordinateRing W ij))).toProjective.Equation
      (projectivePairChartSecondUniversalPoint W ij) := by
  let f := (Algebra.TensorProduct.includeRight
    (R := K)
    (A := coveringChartCoordinateRing W ij.1)
    (B := coveringChartCoordinateRing W ij.2)).toRingHom
  have h := (coveringChartUniversalPoint_equation W ij.2).map f
  have hf : f.comp (coveringChartStructureRingHom W ij.2) =
      algebraMap K (projectivePairChartCoordinateRing W ij) := by
    rw [← coveringChartCoordinateRing_algebraMap]
    exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := K)
      (A := coveringChartCoordinateRing W ij.1)
      (B := coveringChartCoordinateRing W ij.2)).symm
  change ((W.map (coveringChartStructureRingHom W ij.2)).map f).toProjective.Equation
    (f ∘ coveringChartUniversalPoint W ij.2) at h
  rw [WeierstrassCurve.map_map, hf] at h
  have hp : f ∘ coveringChartUniversalPoint W ij.2 =
      projectivePairChartSecondUniversalPoint W ij := by
    funext j
    rfl
  rw [hp] at h
  exact h

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
