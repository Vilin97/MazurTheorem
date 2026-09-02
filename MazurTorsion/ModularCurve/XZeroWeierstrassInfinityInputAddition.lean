/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductAtlas
import Mathlib.Tactic.LinearCombination

/-!
# Addition with one input in the infinity chart

The `Y != 0` by `Z != 0` member of the actual projective-product cover has
coordinates

`P = [u : 1 : v]`, `Q = [x : y : 1]`.

This file develops the universal coordinate ring of that genuine product
chart.  It is the first non-affine input chart in the construction of the
global Weierstrass multiplication.  No group object, point equivalence, or
supplied addition law is used.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Coordinate ring of the `Y != 0` by `Z != 0` member of the actual
projective-product cover. -/
abbrev infinityStandardPairRing (W : WeierstrassCurve K) :=
  projectivePairChartTensorRing W (false, true)

/-- The first input's `X / Y` coordinate. -/
def infinityInputU (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W false :=
  Ideal.Quotient.mk (coveringChartIdeal W false)
    (coordinateChartRatio 1 0)

/-- The first input's `Z / Y` coordinate. -/
def infinityInputV (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W false :=
  Ideal.Quotient.mk (coveringChartIdeal W false)
    (coordinateChartRatio 1 2)

/-- The second input's `X / Z` coordinate. -/
def standardInputX (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W true :=
  Ideal.Quotient.mk (coveringChartIdeal W true)
    (coordinateChartRatio 2 0)

/-- The second input's `Y / Z` coordinate. -/
def standardInputY (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W true :=
  Ideal.Quotient.mk (coveringChartIdeal W true)
    (coordinateChartRatio 2 1)

/-- Universal `u = X₁ / Y₁` on the mixed product chart. -/
def infinityStandardU (W : WeierstrassCurve K) :
    infinityStandardPairRing W :=
  Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (B := coveringChartCoordinateRing W true) (infinityInputU W)

/-- Universal `v = Z₁ / Y₁` on the mixed product chart. -/
def infinityStandardV (W : WeierstrassCurve K) :
    infinityStandardPairRing W :=
  Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (B := coveringChartCoordinateRing W true) (infinityInputV W)

/-- Universal `x = X₂ / Z₂` on the mixed product chart. -/
def infinityStandardX (W : WeierstrassCurve K) :
    infinityStandardPairRing W :=
  Algebra.TensorProduct.includeRight (R := K)
    (A := coveringChartCoordinateRing W false)
    (standardInputX W)

/-- Universal `y = Y₂ / Z₂` on the mixed product chart. -/
def infinityStandardY (W : WeierstrassCurve K) :
    infinityStandardPairRing W :=
  Algebra.TensorProduct.includeRight (R := K)
    (A := coveringChartCoordinateRing W false)
    (standardInputY W)

/-- Structural coefficient map on the mixed product chart. -/
def infinityStandardCoefficientHom (W : WeierstrassCurve K) :
    K →+* infinityStandardPairRing W :=
  Algebra.TensorProduct.includeLeftRingHom.comp
    (coveringChartStructureRingHom W false)

/-- The two factor coefficient maps agree in the tensor product. -/
theorem infinityStandardCoefficientHom_eq_right
    (W : WeierstrassCurve K) :
    infinityStandardCoefficientHom W =
      Algebra.TensorProduct.includeRight.toRingHom.comp
        (coveringChartStructureRingHom W true) := by
  rw [infinityStandardCoefficientHom,
    ← coveringChartCoordinateRing_algebraMap W false,
    ← coveringChartCoordinateRing_algebraMap W true]
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

/-- The explicit coefficient map is the canonical algebra map. -/
theorem infinityStandardCoefficientHom_eq_algebraMap
    (W : WeierstrassCurve K) :
    infinityStandardCoefficientHom W =
      algebraMap K (infinityStandardPairRing W) := by
  rw [infinityStandardCoefficientHom,
    ← coveringChartCoordinateRing_algebraMap W false]
  rfl

private theorem infinityInput_equation (W : WeierstrassCurve K) :
    infinityInputV W +
        coveringChartStructureRingHom W false W.a₁ *
          infinityInputU W * infinityInputV W +
        coveringChartStructureRingHom W false W.a₃ *
          infinityInputV W ^ 2 -
      (infinityInputU W ^ 3 +
        coveringChartStructureRingHom W false W.a₂ *
          infinityInputU W ^ 2 * infinityInputV W +
        coveringChartStructureRingHom W false W.a₄ *
          infinityInputU W * infinityInputV W ^ 2 +
        coveringChartStructureRingHom W false W.a₆ *
          infinityInputV W ^ 3) = 0 := by
  have h : Ideal.Quotient.mk (coveringChartIdeal W false)
      (infinityLocalizedEquation W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [infinityLocalizedEquation_explicit] at h
  change infinityInputV W +
      coveringChartStructureRingHom W false W.a₁ * infinityInputU W *
        infinityInputV W +
      coveringChartStructureRingHom W false W.a₃ * infinityInputV W ^ 2 -
    (infinityInputU W ^ 3 +
      coveringChartStructureRingHom W false W.a₂ * infinityInputU W ^ 2 *
        infinityInputV W +
      coveringChartStructureRingHom W false W.a₄ * infinityInputU W *
        infinityInputV W ^ 2 +
      coveringChartStructureRingHom W false W.a₆ * infinityInputV W ^ 3) = 0 at h
  exact h

private theorem standardInput_equation (W : WeierstrassCurve K) :
    standardInputY W ^ 2 +
        coveringChartStructureRingHom W true W.a₁ *
          standardInputX W * standardInputY W +
        coveringChartStructureRingHom W true W.a₃ *
          standardInputY W -
      (standardInputX W ^ 3 +
        coveringChartStructureRingHom W true W.a₂ *
          standardInputX W ^ 2 +
        coveringChartStructureRingHom W true W.a₄ *
          standardInputX W +
        coveringChartStructureRingHom W true W.a₆) = 0 := by
  have h : Ideal.Quotient.mk (coveringChartIdeal W true)
      (standardChartEquation W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [standardChartEquation_eq_affineToStandardChart] at h
  rw [WeierstrassCurve.Affine.polynomial] at h
  simp only [map_sub, map_add, map_mul, map_pow,
    affineToStandardChart_X, affineToStandardChart_C_X,
    affineToStandardChart_C_C] at h
  change standardInputY W ^ 2 +
      (coveringChartStructureRingHom W true W.a₁ * standardInputX W +
        coveringChartStructureRingHom W true W.a₃) * standardInputY W -
    (standardInputX W ^ 3 +
      coveringChartStructureRingHom W true W.a₂ * standardInputX W ^ 2 +
      coveringChartStructureRingHom W true W.a₄ * standardInputX W +
      coveringChartStructureRingHom W true W.a₆) = 0 at h
  linear_combination h

/-- The universal infinity-chart input satisfies its actual Weierstrass
equation inside the tensor presentation of the product chart. -/
theorem infinityStandard_first_equation (W : WeierstrassCurve K) :
    infinityStandardV W + infinityStandardCoefficientHom W W.a₁ *
        infinityStandardU W * infinityStandardV W +
        infinityStandardCoefficientHom W W.a₃ *
          infinityStandardV W ^ 2 -
      (infinityStandardU W ^ 3 +
        infinityStandardCoefficientHom W W.a₂ *
          infinityStandardU W ^ 2 * infinityStandardV W +
        infinityStandardCoefficientHom W W.a₄ *
          infinityStandardU W * infinityStandardV W ^ 2 +
        infinityStandardCoefficientHom W W.a₆ *
          infinityStandardV W ^ 3) = 0 := by
  let L : coveringChartCoordinateRing W false →ₐ[K]
      infinityStandardPairRing W := Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (B := coveringChartCoordinateRing W true)
  have h := congrArg L (infinityInput_equation W)
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
  simpa [L, infinityStandardU, infinityStandardV,
    infinityStandardCoefficientHom] using h

/-- The universal standard-chart input satisfies its actual affine
Weierstrass equation inside the tensor presentation of the product chart. -/
theorem infinityStandard_second_equation (W : WeierstrassCurve K) :
    infinityStandardY W ^ 2 +
        infinityStandardCoefficientHom W W.a₁ *
          infinityStandardX W * infinityStandardY W +
        infinityStandardCoefficientHom W W.a₃ *
          infinityStandardY W -
      (infinityStandardX W ^ 3 +
        infinityStandardCoefficientHom W W.a₂ *
          infinityStandardX W ^ 2 +
        infinityStandardCoefficientHom W W.a₄ *
          infinityStandardX W +
        infinityStandardCoefficientHom W W.a₆) = 0 := by
  let R : coveringChartCoordinateRing W true →ₐ[K]
      infinityStandardPairRing W := Algebra.TensorProduct.includeRight
        (R := K) (A := coveringChartCoordinateRing W false)
  have h := congrArg R (standardInput_equation W)
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
  rw [infinityStandardCoefficientHom_eq_right W]
  simpa [R, infinityStandardX, infinityStandardY] using h

/-- Named cross-module consumer: the tensor presentation is an actual scheme
presentation of the mixed member of the projective-pair cover. -/
noncomputable def infinityStandardPairTensorIso
    (W : WeierstrassCurve K) :
    projectivePairChartTensorScheme W (false, true) ≅
      projectivePairChartScheme W (false, true) :=
  projectivePairChartTensorIso W (false, true)

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
