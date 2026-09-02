/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination

/-!
# Denominator-free affine doubling coordinates

For a Weierstrass curve over `ℚ`, this file records compact homogeneous
numerators for the abscissa and completed ordinate of an affine double.
The formulas are proved directly from the chord-and-tangent law and are
designed for composition with explicit rational maps.
-/
@[expose] public section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling

/-- The completed-square cubic, equal on the curve to
`(2y + a₁x + a₃)²`. -/
def completedCubic (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

/-- The numerator of the affine doubling abscissa over
`completedCubic`. -/
def xNumerator (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈

/-- The numerator of the completed ordinate of the affine double over
the cube of the source completed ordinate. -/
def completedYNumerator (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 +
    10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
    (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x +
    (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- Homogenization of `xNumerator` to degree four. -/
def xNumeratorHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  u ^ 4 - W.b₄ * u ^ 2 * v ^ 2 - 2 * W.b₆ * u * v ^ 3 -
    W.b₈ * v ^ 4

/-- Homogenization of `completedYNumerator` to degree six. -/
def completedYNumeratorHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  2 * u ^ 6 + W.b₂ * u ^ 5 * v + 5 * W.b₄ * u ^ 4 * v ^ 2 +
    10 * W.b₆ * u ^ 3 * v ^ 3 + 10 * W.b₈ * u ^ 2 * v ^ 4 +
    (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u * v ^ 5 +
    (W.b₄ * W.b₈ - W.b₆ ^ 2) * v ^ 6

/-- Homogenization of `completedCubic` to degree three. -/
def completedCubicHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  4 * u ^ 3 + W.b₂ * u ^ 2 * v + 2 * W.b₄ * u * v ^ 2 +
    W.b₆ * v ^ 3

/-- Directional derivative of `completedCubicHomogeneous` at `(u, v)`
in the direction `(du, dv)`. -/
def completedCubicHomogeneousDirectional
    (W : WeierstrassCurve ℚ) (u v du dv : ℚ) : ℚ :=
  (12 * u ^ 2 + 2 * W.b₂ * u * v + 2 * W.b₄ * v ^ 2) * du +
    (W.b₂ * u ^ 2 + 4 * W.b₄ * u * v + 3 * W.b₆ * v ^ 2) * dv

/-- Directional derivative of `xNumeratorHomogeneous` at `(u, v)`
in the direction `(du, dv)`. -/
def xNumeratorHomogeneousDirectional
    (W : WeierstrassCurve ℚ) (u v du dv : ℚ) : ℚ :=
  (4 * u ^ 3 - 2 * W.b₄ * u * v ^ 2 - 2 * W.b₆ * v ^ 3) * du +
    (-2 * W.b₄ * u ^ 2 * v - 6 * W.b₆ * u * v ^ 2 -
      4 * W.b₈ * v ^ 3) * dv

@[simp] theorem xNumeratorHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    xNumeratorHomogeneous W x 1 = xNumerator W x := by
  simp only [xNumeratorHomogeneous, xNumerator]
  ring

@[simp] theorem completedYNumeratorHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    completedYNumeratorHomogeneous W x 1 = completedYNumerator W x := by
  simp only [completedYNumeratorHomogeneous, completedYNumerator]
  ring

@[simp] theorem completedCubicHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    completedCubicHomogeneous W x 1 = completedCubic W x := by
  simp only [completedCubicHomogeneous, completedCubic]
  ring

/-- The directional numerator identity for tangent doubling.  Equivalently,
the derivative of `xNumeratorHomogeneous / (v * completedCubicHomogeneous)`
has numerator `2 * completedYNumeratorHomogeneous`. -/
theorem xNumeratorHomogeneous_directional
    (W : WeierstrassCurve ℚ) (u v du dv : ℚ) :
    xNumeratorHomogeneousDirectional W u v du dv * v *
          completedCubicHomogeneous W u v -
        xNumeratorHomogeneous W u v *
          (dv * completedCubicHomogeneous W u v +
            v * completedCubicHomogeneousDirectional W u v du dv) =
      2 * completedYNumeratorHomogeneous W u v * (du * v - u * dv) := by
  simp only [xNumeratorHomogeneousDirectional,
    completedCubicHomogeneous, xNumeratorHomogeneous,
    completedCubicHomogeneousDirectional,
    completedYNumeratorHomogeneous]
  linear_combination
    -2 * u ^ 2 * v ^ 4 * (du * v - dv * u) * W.b_relation

/-- The completed-square cubic equals the square of the completed
ordinate on the affine curve. -/
theorem completedCubic_eq_completedY_sq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Equation x y) :
    completedCubic W x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y =
    x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at h
  simp only [completedCubic, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4 * h

/-- The tangent-law doubling abscissa times the completed-square cubic is
the denominator-free numerator `xNumerator`. -/
theorem addX_self_mul_completedCubic
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Equation x y)
    (hv : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) *
        completedCubic W x = xNumerator W x := by
  let v : ℚ := 2 * y + W.a₁ * x + W.a₃
  let n : ℚ := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  let m : ℚ := W.toAffine.slope x x y y
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hv
    simp only [WeierstrassCurve.Affine.negY] at hy
    linarith
  have hm : m * v = n := by
    dsimp only [m]
    rw [W.toAffine.slope_of_Y_ne rfl hy]
    convert
      (div_mul_cancel₀
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) hv)
        using 1
    all_goals
      simp only [v, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.toAffine]
      ring
  have hc := h
  rw [WeierstrassCurve.Affine.equation_iff] at hc
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y =
    x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at hc
  rw [completedCubic_eq_completedY_sq W h]
  rw [WeierstrassCurve.Affine.addX]
  simp only [WeierstrassCurve.toAffine]
  change (m ^ 2 + W.a₁ * m - W.a₂ - x - x) * v ^ 2 =
    xNumerator W x
  simp only [xNumerator, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination
    (m * v + n + W.a₁ * v) * hm -
      (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hc

/-- The completed ordinate of an affine double, multiplied by the cube of
the source completed ordinate, is `completedYNumerator`. -/
theorem completedY_add_self
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Equation x y)
    (hv : 2 * y + W.a₁ * x + W.a₃ ≠ 0) :
    (2 * y + W.a₁ * x + W.a₃) ^ 3 *
      (2 * W.toAffine.addY x x y (W.toAffine.slope x x y y) +
        W.a₁ * W.toAffine.addX x x (W.toAffine.slope x x y y) +
        W.a₃) =
      completedYNumerator W x := by
  let v : ℚ := 2 * y + W.a₁ * x + W.a₃
  let n : ℚ := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
  let m : ℚ := W.toAffine.slope x x y y
  let q : ℚ := W.toAffine.addX x x m
  let r : ℚ := W.toAffine.addY x x y m
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hv
    simp only [WeierstrassCurve.Affine.negY] at hy
    linarith
  have hm : m * v = n := by
    dsimp only [m]
    rw [W.toAffine.slope_of_Y_ne rfl hy]
    convert
      (div_mul_cancel₀
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) hv)
        using 1
    all_goals
      simp only [v, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.toAffine]
      ring
  have hc := h
  rw [WeierstrassCurve.Affine.equation_iff] at hc
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y =
    x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ at hc
  have hq : q * v ^ 2 = xNumerator W x := by
    have ht := addX_self_mul_completedCubic W h hv
    rw [completedCubic_eq_completedY_sq W h] at ht
    simpa only [q, m, v] using ht
  have hr : 2 * r + W.a₁ * q + W.a₃ =
      -(2 * m + W.a₁) * (q - x) - v := by
    simp only [r, q, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]
    ring
  change v ^ 3 * (2 * r + W.a₁ * q + W.a₃) =
    completedYNumerator W x
  simp only [completedYNumerator, xNumerator,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hq ⊢
  linear_combination
    v ^ 3 * hr - 2 * v ^ 2 * (q - x) * hm -
      (2 * n + W.a₁ * v) * hq +
      4 *
        (-W.a₁ ^ 2 * x ^ 2 - 3 * W.a₁ * W.a₃ * x -
          4 * W.a₁ * x * y - 2 * W.a₃ ^ 2 - 4 * W.a₃ * y -
          2 * W.a₄ * x - 4 * W.a₆ + 2 * x ^ 3 - 4 * y ^ 2) * hc

end MazurTorsion.Doubling
