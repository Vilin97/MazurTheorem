/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.EllipticCurve.DoublingCoordinates
public import MazurTorsion.Kubert.OrderSevenHauptmodulClearing
public import MazurTorsion.Kubert.OrderSevenIsogeny
import Mathlib.Tactic.Ring

/-!
# Polynomial selection for backtracking through the order-seven isogeny

If Tate normalization of a point on the order-seven quotient produces the
Fricke partner of the source parameter, clearing the two Hauptmodul
expressions gives a polynomial equation.  The raw equation depends on both
affine coordinates.  On the quotient curve, completed-square identities
replace it by a compact polynomial depending only on the abscissa.

The final theorem packages the exact-order-`49` consumer: the explicit
Vélu image of such a point is not a kernel pole, lies on the quotient, and
its abscissa satisfies the selection polynomial whenever the two
Hauptmodul parameters agree.
-/
@[expose] public section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The raw cross-multiplied equation saying that the quotient point's
level-seven Hauptmodul is the Fricke partner of the source parameter. -/
def orderSevenRawSelectionNumerator (d X Y : ℚ) : ℚ :=
  let W := orderSevenQuotient d
  let A := pointTateParameterClearedNumerator W X Y
  let B := pointTateParameterClearedDenominator W X Y
  d * (d - 1) * orderSevenParameterHauptmodulNumerator A B -
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) *
      orderSevenParameterCubic A B

/-- Equality with the Fricke parameter forces the raw cleared selection
equation. -/
theorem orderSevenRawSelectionNumerator_eq_zero_of_hauptmodul_eq_fricke
    {d X Y : ℚ} [(orderSevenFamily d).IsElliptic]
    (h : orderSevenHauptmodulAt (orderSevenQuotient d) X Y =
      orderSevenFrickeParameter d) :
    orderSevenRawSelectionNumerator d X Y = 0 := by
  have hhaupt :
      orderSevenHauptmodulAt (orderSevenQuotient d) X Y ≠ 0 := by
    rw [h]
    exact orderSevenFrickeParameter_ne_zero d
  have hbeta : pointTateBeta (orderSevenQuotient d) X Y ≠ 0 :=
    pointTateBeta_ne_zero_of_hauptmodul_ne_zero _ hhaupt
  rw [orderSevenHauptmodulAt_eq_cleared _ hbeta] at h
  let A := pointTateParameterClearedNumerator (orderSevenQuotient d) X Y
  let B := pointTateParameterClearedDenominator (orderSevenQuotient d) X Y
  let C := orderSevenParameterCubic A B
  let N := orderSevenParameterHauptmodulNumerator A B
  have hfrac : N / C =
      (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) / (d * (d - 1)) := by
    simpa only [A, B, C, N, orderSevenFrickeParameter] using h
  have hC : C ≠ 0 := by
    intro hC
    have : N / C = 0 := by simp [hC]
    rw [this] at hfrac
    exact orderSevenFrickeParameter_ne_zero d hfrac.symm
  obtain ⟨hd0, hd1, -⟩ := orderSevenFamily_parameters_ne d
  have hdd : d * (d - 1) ≠ 0 :=
    mul_ne_zero hd0 (sub_ne_zero.mpr hd1)
  simp only [orderSevenRawSelectionNumerator]
  change d * (d - 1) * N -
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) * C = 0
  apply sub_eq_zero.mpr
  simpa only [mul_comm] using (div_eq_div_iff hC hdd).mp hfrac

/-- Twice the completed tangent numerator at an affine point. -/
def pointTateCompletedTangentNumerator
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  6 * x ^ 2 + W.b₂ * x + W.b₄

/-- An abscissa-only cleared numerator for `pointTateAlpha`, rescaled by
four on the curve. -/
def pointTateAlphaUnivariateCleared
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  (12 * x + W.b₂) * Doubling.completedCubic W x -
    pointTateCompletedTangentNumerator W x ^ 2

/-- An abscissa-only cleared last normalization factor, rescaled by four
on the curve. -/
def pointTateGammaUnivariateCleared
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * Doubling.completedCubic W x ^ 2 -
    pointTateAlphaUnivariateCleared W x *
      pointTateCompletedTangentNumerator W x

/-- The abscissa-only numerator of the cleared Tate parameter. -/
def pointTateParameterUnivariateNumerator
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  -pointTateAlphaUnivariateCleared W x ^ 3

/-- The abscissa-only denominator of the cleared Tate parameter. -/
def pointTateParameterUnivariateDenominator
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  16 * pointTateGammaUnivariateCleared W x *
    Doubling.completedCubic W x ^ 2

private theorem pointTateCompletedTangentNumerator_eq
    (W : WeierstrassCurve ℚ) (x y : ℚ) :
    pointTateCompletedTangentNumerator W x =
      W.a₁ * pointTateBeta W x y +
        2 * pointTateLambdaNumerator W x y := by
  simp only [pointTateCompletedTangentNumerator, pointTateBeta,
    pointTateLambdaNumerator, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

private theorem completedCubic_eq_pointTateBeta_sq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    Doubling.completedCubic W x = pointTateBeta W x y ^ 2 := by
  rw [Doubling.completedCubic_eq_completedY_sq W hcurve]
  simp only [pointTateBeta]
  congr 1
  ring

private theorem pointTateAlphaUnivariateCleared_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    pointTateAlphaUnivariateCleared W x =
      4 * pointTateAlphaCleared W x y := by
  rw [pointTateAlphaUnivariateCleared,
    completedCubic_eq_pointTateBeta_sq W hcurve,
    pointTateCompletedTangentNumerator_eq W x y]
  simp only [pointTateBeta, pointTateAlphaCleared,
    pointTateLambdaNumerator, WeierstrassCurve.b₂]
  ring

private theorem pointTateGammaUnivariateCleared_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    pointTateGammaUnivariateCleared W x =
      4 * pointTateGammaCleared W x y := by
  rw [pointTateGammaUnivariateCleared,
    completedCubic_eq_pointTateBeta_sq W hcurve,
    pointTateAlphaUnivariateCleared_eq W hcurve,
    pointTateCompletedTangentNumerator_eq W x y]
  simp only [pointTateGammaCleared]
  ring

private theorem pointTateParameterUnivariateNumerator_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    pointTateParameterUnivariateNumerator W x =
      64 * pointTateParameterClearedNumerator W x y := by
  rw [pointTateParameterUnivariateNumerator,
    pointTateAlphaUnivariateCleared_eq W hcurve]
  simp only [pointTateParameterClearedNumerator]
  ring

private theorem pointTateParameterUnivariateDenominator_eq
    (W : WeierstrassCurve ℚ) {x y : ℚ}
    (hcurve : W.toAffine.Equation x y) :
    pointTateParameterUnivariateDenominator W x =
      64 * pointTateParameterClearedDenominator W x y := by
  rw [pointTateParameterUnivariateDenominator,
    pointTateGammaUnivariateCleared_eq W hcurve,
    completedCubic_eq_pointTateBeta_sq W hcurve]
  simp only [pointTateParameterClearedDenominator]
  ring

/-- The compact abscissa-only selection polynomial on the order-seven
quotient. -/
def orderSevenSelectionPolynomial (d X : ℚ) : ℚ :=
  let W := orderSevenQuotient d
  let A := pointTateParameterUnivariateNumerator W X
  let B := pointTateParameterUnivariateDenominator W X
  d * (d - 1) * orderSevenParameterHauptmodulNumerator A B -
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) *
      orderSevenParameterCubic A B

/-- On the quotient curve, the abscissa-only selection polynomial is
`64 ^ 3` times the raw cleared equation. -/
theorem orderSevenSelectionPolynomial_eq_raw
    {d X Y : ℚ}
    (hcurve : (orderSevenQuotient d).toAffine.Equation X Y) :
    orderSevenSelectionPolynomial d X =
      64 ^ 3 * orderSevenRawSelectionNumerator d X Y := by
  simp only [orderSevenSelectionPolynomial,
    orderSevenRawSelectionNumerator]
  rw [pointTateParameterUnivariateNumerator_eq _ hcurve,
    pointTateParameterUnivariateDenominator_eq _ hcurve]
  simp only [orderSevenParameterHauptmodulNumerator,
    orderSevenParameterCubic]
  ring

/-- Fricke equality at a quotient point forces the compact selection
polynomial to vanish at its abscissa. -/
theorem orderSevenSelectionPolynomial_eq_zero_of_hauptmodul_eq_fricke
    {d X Y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hcurve : (orderSevenQuotient d).toAffine.Equation X Y)
    (h : orderSevenHauptmodulAt (orderSevenQuotient d) X Y =
      orderSevenFrickeParameter d) :
    orderSevenSelectionPolynomial d X = 0 := by
  rw [orderSevenSelectionPolynomial_eq_raw hcurve,
    orderSevenRawSelectionNumerator_eq_zero_of_hauptmodul_eq_fricke h]
  ring

/-- Exact order `49` keeps a source point away from the order-seven kernel,
so Fricke equality for its explicit Vélu image forces the compact selection
polynomial to vanish. -/
theorem orderSevenSelectionPolynomial_eq_zero_of_residual_eq_fricke
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (h : orderSevenResidualHauptmodul d x y =
      orderSevenFrickeParameter d) :
    orderSevenSelectionPolynomial d (orderSevenVeluX d x) = 0 := by
  have hx : ¬OrderSevenKernelX d x := by
    exact not_orderSevenKernelX_of_order_fortyNine hP hQ
  have hx0 : x ≠ 0 := fun hx0 ↦ hx (Or.inl hx0)
  have hxb : x ≠ orderSevenB d :=
    fun hxb ↦ hx (Or.inr (Or.inl hxb))
  have hxc : x ≠ orderSevenC d :=
    fun hxc ↦ hx (Or.inr (Or.inr hxc))
  apply orderSevenSelectionPolynomial_eq_zero_of_hauptmodul_eq_fricke
    (orderSevenVelu_equation hP.1 hx0 hxb hxc)
  exact h

end MazurTorsion.Kubert
