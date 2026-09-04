/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductOutputCompatibility
import Mathlib.Tactic.LinearCombination

/-!
# An infinity-pair neighborhood for Weierstrass addition

On the `Y = 1` chart write the two universal points as `(x₁, 1, z₁)`
and `(x₂, 1, z₂)`.  Subtracting their cubic equations gives

`(z₁ - z₂) B∞ = (x₁ - x₂) A∞`.

The factor `B∞` restricts on the diagonal to the projective `Z` partial
derivative.  In particular it takes the value one at the pair of points at
infinity.  After inverting `B∞`, the quotient `A∞ / B∞` is therefore
a regular slope through the two universal points and remains meaningful on
the diagonal near infinity.

This is the source neighborhood for the remaining local addition formula.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Coordinate ring of the infinity-by-infinity member of the projective-pair
cover. -/
abbrev projectiveInfinityPairCoordinateRing (W : WeierstrassCurve K) :=
  projectivePairChartCoordinateRing W (false, false)

/-- First universal `X / Y` coordinate on the infinity pair. -/
abbrev projectiveInfinityPairX₁ (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W :=
  projectivePairChartFirstUniversalPoint W (false, false) (0 : Fin 3)

/-- First universal `Z / Y` coordinate on the infinity pair. -/
abbrev projectiveInfinityPairZ₁ (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W :=
  projectivePairChartFirstUniversalPoint W (false, false) (2 : Fin 3)

/-- Second universal `X / Y` coordinate on the infinity pair. -/
abbrev projectiveInfinityPairX₂ (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W :=
  projectivePairChartSecondUniversalPoint W (false, false) (0 : Fin 3)

/-- Second universal `Z / Y` coordinate on the infinity pair. -/
abbrev projectiveInfinityPairZ₂ (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W :=
  projectivePairChartSecondUniversalPoint W (false, false) (2 : Fin 3)

/-- The denominator in the divided difference of the infinity-chart
equation with respect to `Z / Y`. -/
def projectiveInfinityPairAdditionB12 (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W :=
  let W' := projectivePairChartMappedCurve W (false, false)
  1 + W'.a₁ * projectiveInfinityPairX₁ W +
    W'.a₃ * (projectiveInfinityPairZ₁ W + projectiveInfinityPairZ₂ W) -
    W'.a₂ * projectiveInfinityPairX₁ W ^ 2 -
    W'.a₄ * projectiveInfinityPairX₁ W *
      (projectiveInfinityPairZ₁ W + projectiveInfinityPairZ₂ W) -
    W'.a₆ * (projectiveInfinityPairZ₁ W ^ 2 +
      projectiveInfinityPairZ₁ W * projectiveInfinityPairZ₂ W +
      projectiveInfinityPairZ₂ W ^ 2)

/-- The numerator in the divided difference of the infinity-chart equation
with respect to `X / Y`. -/
def projectiveInfinityPairAdditionA12 (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W :=
  let W' := projectivePairChartMappedCurve W (false, false)
  projectiveInfinityPairX₁ W ^ 2 +
    projectiveInfinityPairX₁ W * projectiveInfinityPairX₂ W +
    projectiveInfinityPairX₂ W ^ 2 +
    W'.a₂ * projectiveInfinityPairZ₂ W *
      (projectiveInfinityPairX₁ W + projectiveInfinityPairX₂ W) +
    W'.a₄ * projectiveInfinityPairZ₂ W ^ 2 -
    W'.a₁ * projectiveInfinityPairZ₂ W

private lemma infinityChart_pair_coordinate_identity
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (x₁ z₁ x₂ z₂ : R)
    (h₁ : W.toProjective.Equation ![x₁, 1, z₁])
    (h₂ : W.toProjective.Equation ![x₂, 1, z₂]) :
    (z₁ - z₂) *
        (1 + W.a₁ * x₁ + W.a₃ * (z₁ + z₂) - W.a₂ * x₁ ^ 2 -
          W.a₄ * x₁ * (z₁ + z₂) -
          W.a₆ * (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2)) =
      (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * z₂ * (x₁ + x₂) +
          W.a₄ * z₂ ^ 2 - W.a₁ * z₂) := by
  rw [WeierstrassCurve.Projective.equation_iff] at h₁ h₂
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, one_pow, one_mul, mul_one] at h₁ h₂
  linear_combination h₁ - h₂

/-- Difference of the two universal infinity-chart equations, factored into
the numerator-denominator identity for the regular slope. -/
theorem projectiveInfinityPair_addition_coordinate_identity
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairZ₁ W - projectiveInfinityPairZ₂ W) *
        projectiveInfinityPairAdditionB12 W =
      (projectiveInfinityPairX₁ W - projectiveInfinityPairX₂ W) *
        projectiveInfinityPairAdditionA12 W := by
  let W' := projectivePairChartMappedCurve W (false, false)
  have hpoint₁ :
      ![projectiveInfinityPairX₁ W, 1, projectiveInfinityPairZ₁ W] =
        projectivePairChartFirstUniversalPoint W (false, false) := by
    funext j
    fin_cases j
    · rfl
    · change (1 : projectiveInfinityPairCoordinateRing W) =
        projectivePairChartFirstUniversalPoint W (false, false)
          (coveringCoordinate false)
      exact
        (projectivePairChartFirstUniversalPoint_normalized W (false, false)).symm
    · rfl
  have hpoint₂ :
      ![projectiveInfinityPairX₂ W, 1, projectiveInfinityPairZ₂ W] =
        projectivePairChartSecondUniversalPoint W (false, false) := by
    funext j
    fin_cases j
    · rfl
    · change (1 : projectiveInfinityPairCoordinateRing W) =
        projectivePairChartSecondUniversalPoint W (false, false)
          (coveringCoordinate false)
      exact
        (projectivePairChartSecondUniversalPoint_normalized W (false, false)).symm
    · rfl
  have h₁ : W'.toProjective.Equation
      ![projectiveInfinityPairX₁ W, 1, projectiveInfinityPairZ₁ W] := by
    rw [hpoint₁]
    exact projectivePairChartFirstUniversalPoint_equation W (false, false)
  have h₂ : W'.toProjective.Equation
      ![projectiveInfinityPairX₂ W, 1, projectiveInfinityPairZ₂ W] := by
    rw [hpoint₂]
    exact projectivePairChartSecondUniversalPoint_equation W (false, false)
  simpa [projectiveInfinityPairAdditionB12,
    projectiveInfinityPairAdditionA12, W'] using
      infinityChart_pair_coordinate_identity W'
        (projectiveInfinityPairX₁ W) (projectiveInfinityPairZ₁ W)
        (projectiveInfinityPairX₂ W) (projectiveInfinityPairZ₂ W) h₁ h₂

/-! ## The diagonal and the point at infinity -/

/-- The diagonal comorphism from the infinity-pair chart to one copy of the
infinity chart. -/
noncomputable def projectiveInfinityPairDiagonalAlgHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W →ₐ[K]
      coveringChartCoordinateRing W false :=
  Algebra.TensorProduct.lift
    (AlgHom.id K (coveringChartCoordinateRing W false))
    (AlgHom.id K (coveringChartCoordinateRing W false))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem projectiveInfinityPairDiagonalAlgHom_X₁
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDiagonalAlgHom W (projectiveInfinityPairX₁ W) =
      coveringChartUniversalPoint W false (0 : Fin 3) := by
  simp [projectiveInfinityPairDiagonalAlgHom, projectiveInfinityPairX₁,
    projectivePairChartFirstUniversalPoint,
    Algebra.TensorProduct.lift_tmul]

@[simp]
theorem projectiveInfinityPairDiagonalAlgHom_Z₁
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDiagonalAlgHom W (projectiveInfinityPairZ₁ W) =
      coveringChartUniversalPoint W false (2 : Fin 3) := by
  simp [projectiveInfinityPairDiagonalAlgHom, projectiveInfinityPairZ₁,
    projectivePairChartFirstUniversalPoint,
    Algebra.TensorProduct.lift_tmul]

@[simp]
theorem projectiveInfinityPairDiagonalAlgHom_X₂
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDiagonalAlgHom W (projectiveInfinityPairX₂ W) =
      coveringChartUniversalPoint W false (0 : Fin 3) := by
  simp [projectiveInfinityPairDiagonalAlgHom, projectiveInfinityPairX₂,
    projectivePairChartSecondUniversalPoint,
    Algebra.TensorProduct.lift_tmul]

@[simp]
theorem projectiveInfinityPairDiagonalAlgHom_Z₂
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDiagonalAlgHom W (projectiveInfinityPairZ₂ W) =
      coveringChartUniversalPoint W false (2 : Fin 3) := by
  simp [projectiveInfinityPairDiagonalAlgHom, projectiveInfinityPairZ₂,
    projectivePairChartSecondUniversalPoint,
    Algebra.TensorProduct.lift_tmul]

/-- On the diagonal, the divided-difference denominator is exactly the
projective `Z` partial derivative at the universal infinity-chart point. -/
theorem projectiveInfinityPairDiagonalAlgHom_B12
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDiagonalAlgHom W
        (projectiveInfinityPairAdditionB12 W) =
      MvPolynomial.eval (coveringChartUniversalPoint W false)
        (W.map (coveringChartStructureRingHom W false)).toProjective.polynomialZ := by
  have hcoefficient (a : K) :
      projectiveInfinityPairDiagonalAlgHom W
          (algebraMap K (projectiveInfinityPairCoordinateRing W) a) =
        coveringChartStructureRingHom W false a := by
    rw [(projectiveInfinityPairDiagonalAlgHom W).commutes,
      ← coveringChartCoordinateRing_algebraMap]
  have hy : coveringChartUniversalPoint W false (1 : Fin 3) = 1 := by
    change coveringChartUniversalPoint W false (coveringCoordinate false) = 1
    exact coveringChartUniversalPoint_normalized W false
  rw [WeierstrassCurve.Projective.eval_polynomialZ]
  simp only [projectiveInfinityPairAdditionB12, map_add, map_sub, map_mul,
    map_pow, map_one, projectiveInfinityPairDiagonalAlgHom_X₁,
    projectiveInfinityPairDiagonalAlgHom_Z₁,
    projectiveInfinityPairDiagonalAlgHom_Z₂,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆]
  simp only [hcoefficient]
  rw [hy]
  ring

/-- Evaluation of the infinity chart at the projective origin `[0 : 1 : 0]`. -/
noncomputable def coveringInfinityChartOriginAlgHom
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W false →ₐ[K] K :=
  coveringChartCoordinateRingAlgHomOfNormalizedPoint W false ![0, 1, 0]
    (by simpa using W.toProjective.equation_zero)
    (by rfl)

@[simp]
theorem coveringInfinityChartOriginAlgHom_universalPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    coveringInfinityChartOriginAlgHom W
        (coveringChartUniversalPoint W false j) = ![0, 1, 0] j := by
  simpa [coveringInfinityChartOriginAlgHom, coveringChartUniversalPoint] using
    coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio
      W false ![0, 1, 0]
        (by simpa using W.toProjective.equation_zero) (by rfl) j

/-- Evaluation of both factors of the infinity-pair chart at the projective
origin. -/
noncomputable def projectiveInfinityPairOriginAlgHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W →ₐ[K] K :=
  (coveringInfinityChartOriginAlgHom W).comp
    (projectiveInfinityPairDiagonalAlgHom W)

/-- The divided-difference denominator takes the value one at `(O, O)`.
Thus the principal neighborhood selected below genuinely contains the
infinity point of the diagonal. -/
@[simp]
theorem projectiveInfinityPairOriginAlgHom_B12
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginAlgHom W
        (projectiveInfinityPairAdditionB12 W) = 1 := by
  rw [projectiveInfinityPairOriginAlgHom, AlgHom.comp_apply,
    projectiveInfinityPairDiagonalAlgHom_B12,
    WeierstrassCurve.Projective.eval_polynomialZ]
  simp

@[simp]
theorem projectiveInfinityPairOriginAlgHom_A12
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginAlgHom W
        (projectiveInfinityPairAdditionA12 W) = 0 := by
  simp [projectiveInfinityPairOriginAlgHom,
    projectiveInfinityPairAdditionA12, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

/-- Coordinate ring of the principal infinity-pair neighborhood selected by
the divided-difference denominator. -/
abbrev projectiveInfinityPairNeighborhoodRing (W : WeierstrassCurve K) :=
  Localization.Away (projectiveInfinityPairAdditionB12 W)

/-- Pullback of the divided-difference numerator to the infinity-pair
neighborhood. -/
def projectiveInfinityPairNeighborhoodA12 (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  algebraMap (projectiveInfinityPairCoordinateRing W)
    (projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairAdditionA12 W)

/-- Pullback of the divided-difference denominator to the infinity-pair
neighborhood. -/
def projectiveInfinityPairNeighborhoodB12 (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  algebraMap (projectiveInfinityPairCoordinateRing W)
    (projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairAdditionB12 W)

/-- The regular infinity-chart secant/tangent slope `A∞ / B∞`. -/
def projectiveInfinityPairNeighborhoodSlope (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  projectiveInfinityPairNeighborhoodA12 W *
    IsLocalization.Away.invSelf (projectiveInfinityPairAdditionB12 W)

/-- Evaluation at `(O, O)` extends across the principal localization because
the inverted denominator has value one there.  This is the point-valued
consumer certifying that the neighborhood contains the diagonal at infinity. -/
noncomputable def projectiveInfinityPairNeighborhoodOriginAlgHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (projectiveInfinityPairAdditionB12 W)
    (f := projectiveInfinityPairOriginAlgHom W) (by
      rw [projectiveInfinityPairOriginAlgHom_B12]
      exact isUnit_one)

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_algebraMap
    (W : WeierstrassCurve K) (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W) a) =
      projectiveInfinityPairOriginAlgHom W a := by
  simp [projectiveInfinityPairNeighborhoodOriginAlgHom,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

/-- The regular slope times the inverted denominator recovers its numerator. -/
theorem projectiveInfinityPairNeighborhoodSlope_mul_B12
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodSlope W *
        projectiveInfinityPairNeighborhoodB12 W =
      projectiveInfinityPairNeighborhoodA12 W := by
  rw [projectiveInfinityPairNeighborhoodSlope,
    projectiveInfinityPairNeighborhoodB12, mul_assoc,
    mul_comm (IsLocalization.Away.invSelf
      (projectiveInfinityPairAdditionB12 W)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The regular slope specializes to zero at `(O, O)`, as required by the
line `Z = 0` tangent to the cubic at infinity. -/
@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_slope
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodSlope W) = 0 := by
  have h := congrArg (projectiveInfinityPairNeighborhoodOriginAlgHom W)
    (projectiveInfinityPairNeighborhoodSlope_mul_B12 W)
  simpa [projectiveInfinityPairNeighborhoodA12,
    projectiveInfinityPairNeighborhoodB12] using h

private theorem projectiveInfinityPairNeighborhood_coordinate_identity
    (W : WeierstrassCurve K) :
    (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairZ₁ W) -
        algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairZ₂ W)) *
        projectiveInfinityPairNeighborhoodB12 W =
      (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairX₁ W) -
        algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairX₂ W)) *
        projectiveInfinityPairNeighborhoodA12 W := by
  simpa [projectiveInfinityPairNeighborhoodA12,
    projectiveInfinityPairNeighborhoodB12] using congrArg
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodRing W))
      (projectiveInfinityPair_addition_coordinate_identity W)

/-- On `D(B∞)`, the regular slope times `x₁ - x₂` is `z₁ - z₂`.
This identity remains valid on the diagonal. -/
theorem projectiveInfinityPairNeighborhoodSlope_mul_sub (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodSlope W *
        (algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectiveInfinityPairNeighborhoodRing W)
            (projectiveInfinityPairX₁ W) -
          algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectiveInfinityPairNeighborhoodRing W)
            (projectiveInfinityPairX₂ W)) =
      algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairZ₁ W) -
        algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairZ₂ W) := by
  have h := projectiveInfinityPairNeighborhood_coordinate_identity W
  calc
    _ = ((algebraMap (projectiveInfinityPairCoordinateRing W)
              (projectiveInfinityPairNeighborhoodRing W)
              (projectiveInfinityPairX₁ W) -
            algebraMap (projectiveInfinityPairCoordinateRing W)
              (projectiveInfinityPairNeighborhoodRing W)
              (projectiveInfinityPairX₂ W)) *
          projectiveInfinityPairNeighborhoodA12 W) *
        IsLocalization.Away.invSelf
          (projectiveInfinityPairAdditionB12 W) := by
      simp only [projectiveInfinityPairNeighborhoodSlope]
      ring
    _ = ((algebraMap (projectiveInfinityPairCoordinateRing W)
              (projectiveInfinityPairNeighborhoodRing W)
              (projectiveInfinityPairZ₁ W) -
            algebraMap (projectiveInfinityPairCoordinateRing W)
              (projectiveInfinityPairNeighborhoodRing W)
              (projectiveInfinityPairZ₂ W)) *
          projectiveInfinityPairNeighborhoodB12 W) *
        IsLocalization.Away.invSelf
          (projectiveInfinityPairAdditionB12 W) := by rw [← h]
    _ = _ := by
      rw [projectiveInfinityPairNeighborhoodB12, mul_assoc,
        IsLocalization.Away.mul_invSelf, mul_one]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
