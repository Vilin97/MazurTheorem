/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Paired terms in Vélu's formulas

This file isolates the two elementary chord-law identities behind the
paired form of Vélu's formulas.  Pairing a point `R = (r, s)` with `-R`
removes the source ordinate from the abscissa correction.  The corresponding
completed-ordinate sum is the formal derivative of that correction times
the completed ordinate of the input point.

The total coordinate evaluators below assign zero to the point at infinity.
This convention is convenient for finite kernel-orbit sums; the paired
identities themselves only evaluate affine sums guaranteed by `x ≠ r`.
-/
@[expose] public section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Velu

/-- The abscissa of an affine point, extended by zero at infinity. -/
noncomputable def pointXOrZero (W : WeierstrassCurve ℚ) :
    W.toAffine.Point → ℚ
  | 0 => 0
  | .some x _ _ => x

/-- The completed ordinate `2y + a₁x + a₃` of an affine point, extended
by zero at infinity. -/
noncomputable def pointCompletedYOrZero (W : WeierstrassCurve ℚ) :
    W.toAffine.Point → ℚ
  | 0 => 0
  | .some x y _ => 2 * y + W.a₁ * x + W.a₃

@[simp] theorem pointXOrZero_zero (W : WeierstrassCurve ℚ) :
    pointXOrZero W 0 = 0 :=
  rfl

@[simp] theorem pointXOrZero_some
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Nonsingular x y) :
    pointXOrZero W (.some x y h) = x :=
  rfl

@[simp] theorem pointXOrZero_neg
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    pointXOrZero W (-P) = pointXOrZero W P := by
  cases P with
  | zero => rfl
  | some x y h => simp [WeierstrassCurve.Affine.Point.neg_some]

@[simp] theorem pointCompletedYOrZero_zero (W : WeierstrassCurve ℚ) :
    pointCompletedYOrZero W 0 = 0 :=
  rfl

@[simp] theorem pointCompletedYOrZero_some
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (h : W.toAffine.Nonsingular x y) :
    pointCompletedYOrZero W (.some x y h) =
      2 * y + W.a₁ * x + W.a₃ :=
  rfl

@[simp] theorem pointCompletedYOrZero_neg
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    pointCompletedYOrZero W (-P) = -pointCompletedYOrZero W P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.negY]
      ring

/-- The paired abscissa correction contributed by `R = (r, s)` and `-R`. -/
def pairXCorrection (W : WeierstrassCurve ℚ) (x r s : ℚ) : ℚ :=
  (6 * r ^ 2 + W.b₂ * r + W.b₄) / (x - r) +
    (2 * s + W.a₁ * r + W.a₃) ^ 2 / (x - r) ^ 2

/-- The formal derivative in `x` of `pairXCorrection`. -/
def pairDifferentialCorrection
    (W : WeierstrassCurve ℚ) (x r s : ℚ) : ℚ :=
  -(6 * r ^ 2 + W.b₂ * r + W.b₄) / (x - r) ^ 2 -
    2 * (2 * s + W.a₁ * r + W.a₃) ^ 2 / (x - r) ^ 3

/-- Pairing `R` and `-R` in the chord law gives the standard paired
abscissa term in Vélu's formula. -/
theorem pointXOrZero_add_pair
    (W : WeierstrassCurve ℚ) {x y r s : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hR : W.toAffine.Nonsingular r s)
    (hxr : x ≠ r) :
    pointXOrZero W (.some x y hP + .some r s hR) +
        pointXOrZero W (.some x y hP + -(.some r s hR)) - 2 * r =
      pairXCorrection W x r s := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxr,
    WeierstrassCurve.Affine.Point.add_of_X_ne hxr]
  simp only [pointXOrZero, pairXCorrection]
  rw [W.toAffine.slope_of_X_ne hxr, W.toAffine.slope_of_X_ne hxr]
  simp only [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY]
  have hPcurve := hP.1
  have hRcurve := hR.1
  rw [WeierstrassCurve.Affine.equation_iff] at hPcurve hRcurve
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [sub_ne_zero.mpr hxr]
  linear_combination 2 * hPcurve - 2 * hRcurve

/-- The paired completed-ordinate sum is the derivative correction times
the completed ordinate of the input point. -/
theorem pointCompletedYOrZero_add_pair
    (W : WeierstrassCurve ℚ) {x y r s : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hR : W.toAffine.Nonsingular r s)
    (hxr : x ≠ r) :
    pointCompletedYOrZero W (.some x y hP + .some r s hR) +
        pointCompletedYOrZero W (.some x y hP + -(.some r s hR)) =
      pairDifferentialCorrection W x r s *
        (2 * y + W.a₁ * x + W.a₃) := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxr,
    WeierstrassCurve.Affine.Point.add_of_X_ne hxr]
  simp only [pointCompletedYOrZero, pairDifferentialCorrection]
  rw [W.toAffine.slope_of_X_ne hxr, W.toAffine.slope_of_X_ne hxr]
  simp only [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  have hPcurve := hP.1
  have hRcurve := hR.1
  rw [WeierstrassCurve.Affine.equation_iff] at hPcurve hRcurve
  field_simp [sub_ne_zero.mpr hxr]
  linear_combination
    (-2 * (2 * y + W.a₁ * x + W.a₃)) * hPcurve +
      (2 * (2 * y + W.a₁ * x + W.a₃)) * hRcurve

end MazurTorsion.Velu
