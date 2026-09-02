/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenHauptmodul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Denominator-free Tate normalization at an order-seven point

The pointwise Tate-normalization formula is naturally a tower of rational
expressions.  This file exposes compact cleared coordinates for the final
Tate parameter and for the level-seven Hauptmodul.  Polynomial-certificate
consumers can therefore avoid expanding the normalization or carrying a
spurious nonvanishing assumption for the fully cleared denominator.
-/
@[expose] public section
namespace MazurTorsion.Kubert

/-- The numerator of the tangent slope used in pointwise Tate
normalization. -/
def pointTateLambdaNumerator
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2

/-- The numerator of `pointTateAlpha` after clearing
`pointTateBeta ^ 2`. -/
def pointTateAlphaCleared
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  (W.a₂ + 3 * x) * pointTateBeta W x y ^ 2 -
    W.a₁ * pointTateLambdaNumerator W x y * pointTateBeta W x y -
    pointTateLambdaNumerator W x y ^ 2

/-- The last linear factor in `pointTateParameter`, after clearing
`pointTateBeta ^ 3`. -/
def pointTateGammaCleared
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  pointTateBeta W x y ^ 4 -
    pointTateAlphaCleared W x y *
      (W.a₁ * pointTateBeta W x y +
        2 * pointTateLambdaNumerator W x y)

/-- The numerator of the pointwise Tate parameter in fully cleared form. -/
def pointTateParameterClearedNumerator
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  -pointTateAlphaCleared W x y ^ 3

/-- The denominator of the pointwise Tate parameter in fully cleared
form. -/
def pointTateParameterClearedDenominator
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  pointTateGammaCleared W x y * pointTateBeta W x y ^ 4

/-- The pointwise Tate parameter as a quotient of polynomial expressions.

No nonvanishing hypothesis on the cleared denominator is needed: Lean's
division is total, and both sides are zero when the last normalization
factor vanishes. -/
theorem pointTateParameter_eq_cleared
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hbeta : pointTateBeta W x y ≠ 0) :
    pointTateParameter W x y =
      pointTateParameterClearedNumerator W x y /
        pointTateParameterClearedDenominator W x y := by
  simp only [pointTateParameter, pointTateAlpha, pointTateLambda,
    pointTateLambdaNumerator, pointTateAlphaCleared,
    pointTateGammaCleared, pointTateParameterClearedNumerator,
    pointTateParameterClearedDenominator]
  field_simp [hbeta]
  ring

/-- A nonzero pointwise level-seven Hauptmodul forces the vertical tangent
denominator used by Tate normalization to be nonzero. -/
theorem pointTateBeta_ne_zero_of_hauptmodul_ne_zero
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hB : orderSevenHauptmodulAt W x y ≠ 0) :
    pointTateBeta W x y ≠ 0 := by
  have ht : pointTateParameter W x y ≠ 0 := by
    intro ht
    apply hB
    simp [orderSevenHauptmodulAt, ht]
  have hden :
      pointTateBeta W x y *
        (pointTateBeta W x y - pointTateAlpha W x y *
          (W.a₁ + 2 * pointTateLambda W x y)) ≠ 0 := by
    exact (div_ne_zero_iff.mp (by
      simpa only [pointTateParameter] using ht)).2
  exact (mul_ne_zero_iff.mp hden).1

/-- Homogenization of the cubic denominator in the level-seven
Hauptmodul. -/
def orderSevenParameterCubic (A B : ℚ) : ℚ :=
  A ^ 3 - 8 * A ^ 2 * B + 5 * A * B ^ 2 + B ^ 3

/-- Homogenization of the numerator in the level-seven Hauptmodul. -/
def orderSevenParameterHauptmodulNumerator (A B : ℚ) : ℚ :=
  49 * A * (A - B) * B

/-- The pointwise level-seven Hauptmodul as a quotient of its fully
polynomial numerator and denominator. -/
theorem orderSevenHauptmodulAt_eq_cleared
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hbeta : pointTateBeta W x y ≠ 0) :
    orderSevenHauptmodulAt W x y =
      orderSevenParameterHauptmodulNumerator
          (pointTateParameterClearedNumerator W x y)
          (pointTateParameterClearedDenominator W x y) /
        orderSevenParameterCubic
          (pointTateParameterClearedNumerator W x y)
          (pointTateParameterClearedDenominator W x y) := by
  rw [show orderSevenHauptmodulAt W x y =
      49 * pointTateParameter W x y *
          (pointTateParameter W x y - 1) /
        (pointTateParameter W x y ^ 3 -
          8 * pointTateParameter W x y ^ 2 +
          5 * pointTateParameter W x y + 1) by
    rfl]
  rw [pointTateParameter_eq_cleared W hbeta]
  let A := pointTateParameterClearedNumerator W x y
  let B := pointTateParameterClearedDenominator W x y
  change 49 * (A / B) * (A / B - 1) /
      ((A / B) ^ 3 - 8 * (A / B) ^ 2 + 5 * (A / B) + 1) =
    orderSevenParameterHauptmodulNumerator A B /
      orderSevenParameterCubic A B
  by_cases hB : B = 0
  · simp [hB, orderSevenParameterHauptmodulNumerator,
      orderSevenParameterCubic]
  · have hden :
        (A / B) ^ 3 - 8 * (A / B) ^ 2 + 5 * (A / B) + 1 =
          orderSevenParameterCubic A B / B ^ 3 := by
      simp only [orderSevenParameterCubic]
      field_simp [hB]
    rw [hden]
    by_cases hC : orderSevenParameterCubic A B = 0
    · simp [hC]
    · field_simp [hB, hC]
      simp only [orderSevenParameterHauptmodulNumerator]
      ring

end MazurTorsion.Kubert
