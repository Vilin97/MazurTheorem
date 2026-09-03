/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import MazurTorsion.Kubert.OrderTwentyFiveSeventyOneDescentValues

/-!
# A canonical complete-intersection carrier for the order-twenty-five quotient

The genus-four curve associated with the order-twenty-five quotient has the
canonical complete-intersection model in `P³`

`y² - xz + yz - xw + zw = 0`,

`xyz + x²w - xyw - xzw + yzw + z²w - zw² = 0`.

This file records those two homogeneous equations and checks the degree-one
projection `[x:y:z:w] ↦ [x:z:w]` to the corresponding singular plane sextic.
The projection is accompanied by an explicit inverse on the chart

`D = xz + w(z-x) ≠ 0`,

where `y = -B/D` and `B = w(x²-xz+z²-wz)`.  The polynomial identity behind
both directions is checked by `ring`.

The five published rational cusp representatives are also checked directly
against both equations and proved pairwise distinct in projective space.
`orderTwentyFiveCanonicalCusps_pairwiseDistinct` is the named downstream
consumer for the cusp-order and Picard interfaces.

This is an explicit algebraic-model boundary only.  It does not assert that
this complete intersection represents the modular quotient constructed from
the Tate or Brunault data, nor does it classify all of its rational points.
-/

namespace MazurTorsion.Kubert

open scoped LinearAlgebra.Projectivization

/-- The canonical quadric in coordinate order `(x,y,z,w)`. -/
def orderTwentyFiveCanonicalQuadric
    {R : Type*} [CommRing R] (x y z w : R) : R :=
  y ^ 2 - x * z + y * z - x * w + z * w

/-- The canonical cubic in coordinate order `(x,y,z,w)`. -/
def orderTwentyFiveCanonicalCubic
    {R : Type*} [CommRing R] (x y z w : R) : R :=
  x * y * z + x ^ 2 * w - x * y * w - x * z * w +
    y * z * w + z ^ 2 * w - z * w ^ 2

/-- Representative-level membership in the canonical complete intersection. -/
def OrderTwentyFiveCanonicalOnCurve
    {R : Type*} [CommRing R] (x y z w : R) : Prop :=
  orderTwentyFiveCanonicalQuadric x y z w = 0 ∧
    orderTwentyFiveCanonicalCubic x y z w = 0

/-- The denominator of the inverse to the plane projection. -/
def orderTwentyFiveCanonicalProjectionDenominator
    {R : Type*} [CommRing R] (x z w : R) : R :=
  x * z + w * (z - x)

/-- The numerator occurring in the inverse to the plane projection. -/
def orderTwentyFiveCanonicalProjectionNumerator
    {R : Type*} [CommRing R] (x z w : R) : R :=
  w * (x ^ 2 - x * z + z ^ 2 - w * z)

/-- The singular degree-six plane model, in projected coordinates `(x,z,w)`. -/
def orderTwentyFiveCanonicalPlanePolynomial
    {R : Type*} [CommRing R] (x z w : R) : R :=
  x ^ 4 * w ^ 2 - x ^ 3 * z ^ 3 - x ^ 3 * w ^ 3 -
    x ^ 2 * z ^ 2 * w ^ 2 + x ^ 2 * z * w ^ 3 -
    x * z ^ 4 * w + 2 * x * z ^ 3 * w ^ 2 -
    2 * x * z ^ 2 * w ^ 3 + z ^ 2 * w ^ 4

/-- The cubic is linear in `y`, with the exact numerator and denominator used
by the inverse plane chart. -/
theorem orderTwentyFiveCanonicalCubic_eq_projectionLinear
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalCubic x y z w =
      orderTwentyFiveCanonicalProjectionDenominator x z w * y +
        orderTwentyFiveCanonicalProjectionNumerator x z w := by
  simp only [orderTwentyFiveCanonicalCubic,
    orderTwentyFiveCanonicalProjectionDenominator,
    orderTwentyFiveCanonicalProjectionNumerator]
  ring

/-- A compact elimination certificate for projection from the canonical
complete intersection to the plane sextic. -/
theorem orderTwentyFiveCanonicalPlanePolynomial_identity
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalPlanePolynomial x z w =
      orderTwentyFiveCanonicalProjectionDenominator x z w ^ 2 *
          orderTwentyFiveCanonicalQuadric x y z w -
        orderTwentyFiveCanonicalCubic x y z w *
          (orderTwentyFiveCanonicalProjectionDenominator x z w * y -
            orderTwentyFiveCanonicalProjectionNumerator x z w +
            z * orderTwentyFiveCanonicalProjectionDenominator x z w) := by
  simp only [orderTwentyFiveCanonicalPlanePolynomial,
    orderTwentyFiveCanonicalProjectionDenominator,
    orderTwentyFiveCanonicalProjectionNumerator,
    orderTwentyFiveCanonicalQuadric, orderTwentyFiveCanonicalCubic]
  ring

/-- Every representative on the canonical complete intersection projects to
the singular plane sextic. -/
theorem orderTwentyFiveCanonical_to_plane
    {R : Type*} [CommRing R] (x y z w : R)
    (h : OrderTwentyFiveCanonicalOnCurve x y z w) :
    orderTwentyFiveCanonicalPlanePolynomial x z w = 0 := by
  rw [orderTwentyFiveCanonicalPlanePolynomial_identity]
  rw [h.1, h.2]
  ring

/-- The ordinate of the inverse plane chart. -/
def orderTwentyFiveCanonicalLiftY
    {K : Type*} [Field K] (x z w : K) : K :=
  -orderTwentyFiveCanonicalProjectionNumerator x z w /
    orderTwentyFiveCanonicalProjectionDenominator x z w

/-- The lifted ordinate makes the canonical cubic vanish wherever the chart
denominator is nonzero. -/
theorem orderTwentyFiveCanonicalLiftY_cubic
    {K : Type*} [Field K] (x z w : K)
    (hD : orderTwentyFiveCanonicalProjectionDenominator x z w ≠ 0) :
    orderTwentyFiveCanonicalCubic x
      (orderTwentyFiveCanonicalLiftY x z w) z w = 0 := by
  rw [orderTwentyFiveCanonicalCubic_eq_projectionLinear]
  simp only [orderTwentyFiveCanonicalLiftY]
  field_simp
  ring

/-- A plane-sextic point with nonzero chart denominator lifts to the canonical
complete intersection. -/
theorem orderTwentyFiveCanonical_from_plane
    {K : Type*} [Field K] (x z w : K)
    (hD : orderTwentyFiveCanonicalProjectionDenominator x z w ≠ 0)
    (hplane : orderTwentyFiveCanonicalPlanePolynomial x z w = 0) :
    OrderTwentyFiveCanonicalOnCurve x
      (orderTwentyFiveCanonicalLiftY x z w) z w := by
  have hcubic := orderTwentyFiveCanonicalLiftY_cubic x z w hD
  constructor
  · have hid := orderTwentyFiveCanonicalPlanePolynomial_identity
      x (orderTwentyFiveCanonicalLiftY x z w) z w
    rw [hplane, hcubic] at hid
    simp only [zero_mul, sub_zero] at hid
    have hDsq :
        orderTwentyFiveCanonicalProjectionDenominator x z w ^ 2 ≠ 0 :=
      pow_ne_zero 2 hD
    exact (mul_eq_zero.mp hid.symm).resolve_left hDsq
  · exact hcubic

/-- On the nonexceptional chart, the inverse formula recovers the original
canonical ordinate. -/
theorem orderTwentyFiveCanonicalLiftY_eq
    {K : Type*} [Field K] (x y z w : K)
    (hD : orderTwentyFiveCanonicalProjectionDenominator x z w ≠ 0)
    (hcubic : orderTwentyFiveCanonicalCubic x y z w = 0) :
    orderTwentyFiveCanonicalLiftY x z w = y := by
  rw [orderTwentyFiveCanonicalCubic_eq_projectionLinear] at hcubic
  simp only [orderTwentyFiveCanonicalLiftY]
  apply (div_eq_iff hD).2
  linear_combination -hcubic

/-- The `x` coordinates of the five canonical cusp candidates. -/
def orderTwentyFiveCanonicalCuspX : Fin 5 → ℚ :=
  ![0, 0, 1, 0, 1]

/-- The `y` coordinates of the five canonical cusp candidates. -/
def orderTwentyFiveCanonicalCuspY : Fin 5 → ℚ :=
  ![0, -1, 1, 0, 0]

/-- The `z` coordinates of the five canonical cusp candidates. -/
def orderTwentyFiveCanonicalCuspZ : Fin 5 → ℚ :=
  ![0, 1, 0, 1, 0]

/-- The `w` coordinates of the five canonical cusp candidates. -/
def orderTwentyFiveCanonicalCuspW : Fin 5 → ℚ :=
  ![1, 0, 1, 0, 0]

/-- The five rational coordinate vectors of the canonical cusp candidates. -/
def orderTwentyFiveCanonicalCuspVector (i : Fin 5) : Fin 4 → ℚ :=
  ![orderTwentyFiveCanonicalCuspX i,
    orderTwentyFiveCanonicalCuspY i,
    orderTwentyFiveCanonicalCuspZ i,
    orderTwentyFiveCanonicalCuspW i]

@[simp] theorem orderTwentyFiveCanonicalCuspVector_zero (i : Fin 5) :
    orderTwentyFiveCanonicalCuspVector i 0 =
      orderTwentyFiveCanonicalCuspX i := rfl

@[simp] theorem orderTwentyFiveCanonicalCuspVector_one (i : Fin 5) :
    orderTwentyFiveCanonicalCuspVector i 1 =
      orderTwentyFiveCanonicalCuspY i := rfl

@[simp] theorem orderTwentyFiveCanonicalCuspVector_two (i : Fin 5) :
    orderTwentyFiveCanonicalCuspVector i 2 =
      orderTwentyFiveCanonicalCuspZ i := rfl

@[simp] theorem orderTwentyFiveCanonicalCuspVector_three (i : Fin 5) :
    orderTwentyFiveCanonicalCuspVector i 3 =
      orderTwentyFiveCanonicalCuspW i := rfl

/-- Every canonical cusp vector is nonzero. -/
theorem orderTwentyFiveCanonicalCuspVector_ne_zero (i : Fin 5) :
    orderTwentyFiveCanonicalCuspVector i ≠ 0 := by
  fin_cases i <;>
    simp [orderTwentyFiveCanonicalCuspVector,
      orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero]

/-- The projective point represented by the `i`th canonical cusp vector. -/
def orderTwentyFiveCanonicalCusp (i : Fin 5) :
    ℙ ℚ (Fin 4 → ℚ) :=
  Projectivization.mk ℚ (orderTwentyFiveCanonicalCuspVector i)
    (orderTwentyFiveCanonicalCuspVector_ne_zero i)

/-- Each of the five displayed rational vectors lies on both canonical
equations. -/
theorem orderTwentyFiveCanonicalCusp_onCurve (i : Fin 5) :
    OrderTwentyFiveCanonicalOnCurve
      (orderTwentyFiveCanonicalCuspVector i 0)
      (orderTwentyFiveCanonicalCuspVector i 1)
      (orderTwentyFiveCanonicalCuspVector i 2)
      (orderTwentyFiveCanonicalCuspVector i 3) := by
  fin_cases i <;>
    norm_num [OrderTwentyFiveCanonicalOnCurve,
      orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      orderTwentyFiveCanonicalQuadric, orderTwentyFiveCanonicalCubic,
      Matrix.cons_val_zero]

/-- The five displayed rational points are pairwise distinct in projective
space. -/
theorem orderTwentyFiveCanonicalCusp_injective :
    Function.Injective orderTwentyFiveCanonicalCusp := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [orderTwentyFiveCanonicalCusp,
      Projectivization.mk_eq_mk_iff'] at hij <;>
    simp_all [orderTwentyFiveCanonicalCuspVector,
      orderTwentyFiveCanonicalCuspX, orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ, orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Named consumer for the local cusp-order interface: the five canonical
projective representatives satisfy its exact pairwise-distinctness input. -/
theorem orderTwentyFiveCanonicalCusps_pairwiseDistinct :
    OrderTwentyFiveCuspsPairwiseDistinct
      (orderTwentyFiveCanonicalCusp 0)
      (orderTwentyFiveCanonicalCusp 1)
      (orderTwentyFiveCanonicalCusp 2)
      (orderTwentyFiveCanonicalCusp 3)
      (orderTwentyFiveCanonicalCusp 4) := by
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  constructor
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)
  · exact orderTwentyFiveCanonicalCusp_injective.ne (by decide)

end MazurTorsion.Kubert
