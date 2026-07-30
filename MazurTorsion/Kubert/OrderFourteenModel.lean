/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFourteenReduction
import MazurTorsion.NumberTheory.XOneFourteenDescent

/-!
# The order-fourteen Tate parameter curve and `X₁(14)`

This file gives the denominator-safe inverse of the usual parametrization of the
order-fourteen Tate equation by

`s² + s t + s = t³ - t`.

Put `d = b - c`, `C = tateSevenAux b c`, and
`D = tateSevenYNumerator b c`.  On the open set supplied by the exact-order
certificate, the inverse is

`t = D / (d C)`,
`s = -c² (D + d C) / (d² C)`.

The integral change of variables

`U = 4(t + 1)`,
`V = 4(2s + t + 1)`

then lands on the model

`V² = U(U² - 11U + 32)`

used in `MazurTorsion.XOneFourteen`.  We also prove that the image has
`U ≠ 0, 4, 8`.  Thus an eventual classification of the rational points of that
model by the point at infinity and the five affine points with those three
abscissae immediately rules out every admissible Tate parameter.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The denominator common to the inverse modular parameters. -/
def orderFourteenModelDenominator (b c : ℚ) : ℚ :=
  (b - c) * tateSevenAux b c

/-- The numerator of `t+1`, and hence of the `U`-coordinate. -/
def orderFourteenModelNumerator (b c : ℚ) : ℚ :=
  tateSevenYNumerator b c + (b - c) * tateSevenAux b c

/-- The `t`-coordinate on `s² + st + s = t³ - t`. -/
def orderFourteenModelT (b c : ℚ) : ℚ :=
  tateSevenYNumerator b c / orderFourteenModelDenominator b c

/-- The `s`-coordinate on `s² + st + s = t³ - t`. -/
def orderFourteenModelS (b c : ℚ) : ℚ :=
  -c ^ 2 * orderFourteenModelNumerator b c /
    ((b - c) ^ 2 * tateSevenAux b c)

/-- The `U`-coordinate on the Weierstrass model of `X₁(14)`. -/
def orderFourteenModelU (b c : ℚ) : ℚ :=
  4 * orderFourteenModelNumerator b c /
    orderFourteenModelDenominator b c

/-- The `V`-coordinate on the Weierstrass model of `X₁(14)`.

This expression is the denominator-minimized form of
`4(b - 2c² - c)(b² - bc - c³) / (b(c² + c - b)²)`. -/
def orderFourteenModelV (b c : ℚ) : ℚ :=
  4 * orderFourteenModelNumerator b c *
      (b - c - 2 * c ^ 2) /
    ((b - c) ^ 2 * tateSevenAux b c)

/-- The normalized equation obtained after writing `b = r c` and cancelling
the nonzero factor `c⁶` from `orderFourteenPolynomial`. -/
private def orderFourteenRatioPolynomial (r c : ℚ) : ℚ :=
  -c ^ 4 * r +
    c ^ 3 * (-r ^ 3 + 4 * r ^ 2 - 3 * r) +
    c ^ 2 * (5 * r ^ 4 - 16 * r ^ 3 + 17 * r ^ 2 - 6 * r) +
    c * (-6 * r ^ 5 + 25 * r ^ 4 - 40 * r ^ 3 +
      30 * r ^ 2 - 10 * r + 1) +
    r ^ 6 - 5 * r ^ 5 + 10 * r ^ 4 - 10 * r ^ 3 + 5 * r ^ 2 - r

/-- The normalized form of `tateSevenYNumerator (r*c) c / c³`. -/
private def orderFourteenRatioSevenY (r c : ℚ) : ℚ :=
  -c ^ 2 + c * (r - 1) + (r - 1) ^ 3

/-- The normalized form of `orderFourteenModelNumerator (r*c) c / c³`. -/
private def orderFourteenRatioNumerator (r c : ℚ) : ℚ :=
  -c ^ 2 - c * r ^ 2 + 2 * c * r - c +
    3 * r ^ 3 - 8 * r ^ 2 + 7 * r - 2

private def orderFourteenRatioSevenYLinear (r c : ℚ) : ℚ :=
  -c * r ^ 2 - c * r + c + 3 * r ^ 3 - 5 * r ^ 2 + 2 * r

private def orderFourteenRatioNumeratorLinear (r c : ℚ) : ℚ :=
  -2 * c * r ^ 2 - c * r + c + 5 * r ^ 3 - 8 * r ^ 2 + 3 * r

private lemma model_denominator_ne_zero
    {b c : ℚ} (hbc : b ≠ c) (hC : tateSevenAux b c ≠ 0) :
    orderFourteenModelDenominator b c ≠ 0 := by
  exact mul_ne_zero (sub_ne_zero.mpr hbc) hC

private lemma ratio_polynomial_eq_zero
    {b c : ℚ} (hc : c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenRatioPolynomial (b / c) c = 0 := by
  have hscale :
      c ^ 6 * orderFourteenRatioPolynomial (b / c) c =
        orderFourteenPolynomial b c := by
    simp only [orderFourteenRatioPolynomial, orderFourteenPolynomial,
      tateSixNumerator, tateSevenAux, tateSevenYNumerator]
    field_simp [hc]
    ring
  apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 6 hc)
  rw [hscale, hpoly]

private lemma ratio_seven_y_ne_zero
    {r c : ℚ} (hr : r ≠ 1)
    (hpoly : orderFourteenRatioPolynomial r c = 0) :
    orderFourteenRatioSevenY r c ≠ 0 := by
  intro hD
  have hdivision :
      orderFourteenRatioPolynomial r c -
          (c ^ 2 * r + c * r ^ 3 - 3 * c * r ^ 2 + 2 * c * r -
            3 * r ^ 4 + 9 * r ^ 3 - 9 * r ^ 2 + 3 * r) *
            orderFourteenRatioSevenY r c =
        (r - 1) ^ 4 * orderFourteenRatioSevenYLinear r c := by
    simp only [orderFourteenRatioPolynomial, orderFourteenRatioSevenY,
      orderFourteenRatioSevenYLinear]
    ring
  rw [hpoly, hD] at hdivision
  norm_num at hdivision
  have hlinear : orderFourteenRatioSevenYLinear r c = 0 :=
    hdivision.resolve_left (sub_ne_zero.mpr hr)
  have hfinal :
      (r ^ 2 + r - 1) ^ 2 * orderFourteenRatioSevenY r c -
          (c * r ^ 2 + c * r - c + 2 * r ^ 3 - 5 * r ^ 2 +
            4 * r - 1) * orderFourteenRatioSevenYLinear r c =
        (r - 1) ^ 7 := by
    simp only [orderFourteenRatioSevenY,
      orderFourteenRatioSevenYLinear]
    ring
  rw [hD, hlinear] at hfinal
  norm_num at hfinal
  exact pow_ne_zero 7 (sub_ne_zero.mpr hr) hfinal.symm

private lemma ratio_numerator_ne_zero
    {r c : ℚ} (hr : r ≠ 1)
    (hpoly : orderFourteenRatioPolynomial r c = 0) :
    orderFourteenRatioNumerator r c ≠ 0 := by
  intro hR
  have hdivision :
      orderFourteenRatioPolynomial r c -
          (c ^ 2 * r - 2 * c * r ^ 2 + 2 * c * r +
            2 * r ^ 3 - 4 * r ^ 2 + 2 * r) *
            orderFourteenRatioNumerator r c =
        -(r - 1) ^ 3 * orderFourteenRatioNumeratorLinear r c := by
    simp only [orderFourteenRatioPolynomial, orderFourteenRatioNumerator,
      orderFourteenRatioNumeratorLinear]
    ring
  rw [hpoly, hR] at hdivision
  norm_num at hdivision
  have hlinear : orderFourteenRatioNumeratorLinear r c = 0 :=
    hdivision.resolve_left (sub_ne_zero.mpr hr)
  have hfinal :
      (r + 1) ^ 2 * (2 * r - 1) ^ 2 *
            orderFourteenRatioNumerator r c -
          (2 * c * r ^ 2 + c * r - c + 2 * r ^ 4 + 2 * r ^ 3 -
            9 * r ^ 2 + 6 * r - 1) *
            orderFourteenRatioNumeratorLinear r c =
        2 * (r - 1) ^ 7 := by
    simp only [orderFourteenRatioNumerator,
      orderFourteenRatioNumeratorLinear]
    ring
  rw [hR, hlinear] at hfinal
  norm_num at hfinal
  exact (sub_ne_zero.mpr hr) hfinal

private lemma ratio_seven_y_scale
    {b c : ℚ} (hc : c ≠ 0) :
    c ^ 3 * orderFourteenRatioSevenY (b / c) c =
      tateSevenYNumerator b c := by
  simp only [orderFourteenRatioSevenY, tateSevenYNumerator]
  field_simp [hc]
  ring

private lemma ratio_numerator_scale
    {b c : ℚ} (hc : c ≠ 0) :
    c ^ 3 * orderFourteenRatioNumerator (b / c) c =
      orderFourteenModelNumerator b c := by
  simp only [orderFourteenRatioNumerator, orderFourteenModelNumerator,
    tateSevenYNumerator, tateSevenAux]
  field_simp [hc]
  ring

private lemma ratio_ne_one
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    b / c ≠ 1 := by
  intro h
  apply hbc
  field_simp [hc] at h
  exact h

/-- On the rational order-fourteen parameter curve, the numerator `D` of
the inverse `t`-coordinate cannot vanish on the locus `c(b-c) ≠ 0`. -/
theorem tateSevenYNumerator_ne_of_orderFourteenPolynomial
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hpoly : orderFourteenPolynomial b c = 0) :
    tateSevenYNumerator b c ≠ 0 := by
  intro hD
  have hscale := ratio_seven_y_scale (b := b) (c := c) hc
  have hratio : orderFourteenRatioSevenY (b / c) c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 3 hc)
    rw [hscale, hD]
  exact
    (ratio_seven_y_ne_zero (ratio_ne_one hc hbc)
      (ratio_polynomial_eq_zero hc hpoly)) hratio

/-- The numerator of `t+1`, equivalently the numerator of `U`, cannot vanish
on the rational order-fourteen parameter curve when `c(b-c) ≠ 0`. -/
theorem orderFourteenModelNumerator_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelNumerator b c ≠ 0 := by
  intro hR
  have hscale := ratio_numerator_scale (b := b) (c := c) hc
  have hratio : orderFourteenRatioNumerator (b / c) c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 3 hc)
    rw [hscale, hR]
  exact
    (ratio_numerator_ne_zero (ratio_ne_one hc hbc)
      (ratio_polynomial_eq_zero hc hpoly)) hratio

private lemma model_bridge_identity (b c : ℚ) :
    b * (c ^ 2 + c - b) ^ 2 *
        (tateSevenYNumerator b c +
          (b - c) * tateSevenAux b c) -
      (b - c) ^ 2 * tateSevenAux b c * tateSixNumerator b c =
        orderFourteenPolynomial b c := by
  simp only [tateSevenYNumerator, tateSevenAux, tateSixNumerator,
    orderFourteenPolynomial]
  ring

private lemma seven_y_sub_aux_identity (b c : ℚ) :
    tateSevenYNumerator b c - (b - c) * tateSevenAux b c =
      (c ^ 2 + c - b) * tateSixNumerator b c := by
  simp only [tateSevenYNumerator, tateSevenAux, tateSixNumerator]
  ring

private def orderFourteenModelCofactor (b c : ℚ) : ℚ :=
  3 * b ^ 3 - b ^ 2 * c ^ 2 - 8 * b ^ 2 * c +
    2 * b * c ^ 3 + 7 * b * c ^ 2 -
    c ^ 5 - c ^ 4 - 2 * c ^ 3

private lemma model_equation_identity
    (b c : ℚ) (hbc : b ≠ c) :
    orderFourteenModelS b c ^ 2 +
          orderFourteenModelS b c * orderFourteenModelT b c +
          orderFourteenModelS b c -
          orderFourteenModelT b c ^ 3 +
          orderFourteenModelT b c =
      (b - c ^ 2 - c) * orderFourteenModelCofactor b c *
          orderFourteenPolynomial b c /
        ((b - c) ^ 4 * tateSevenAux b c ^ 3) := by
  have hd : b - c ≠ 0 := sub_ne_zero.mpr hbc
  simp only [orderFourteenModelS, orderFourteenModelT,
    orderFourteenModelNumerator, orderFourteenModelDenominator,
    orderFourteenModelCofactor,
    orderFourteenPolynomial, tateSixNumerator, tateSevenAux,
    tateSevenYNumerator]
  field_simp [hd]
  ring

/-- The explicit inverse parameters satisfy the standard affine equation for
`X₁(14)`. -/
theorem orderFourteenModel_plane_equation
    {b c : ℚ} (hbc : b ≠ c)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelS b c ^ 2 +
        orderFourteenModelS b c * orderFourteenModelT b c +
        orderFourteenModelS b c =
      orderFourteenModelT b c ^ 3 - orderFourteenModelT b c := by
  have hid := model_equation_identity b c hbc
  rw [hpoly] at hid
  norm_num at hid
  linarith

/-- The displayed `U` is exactly `4(t+1)`. -/
theorem orderFourteenModelU_eq
    {b c : ℚ} (hbc : b ≠ c) (hC : tateSevenAux b c ≠ 0) :
    orderFourteenModelU b c = 4 * (orderFourteenModelT b c + 1) := by
  have hd : b - c ≠ 0 := sub_ne_zero.mpr hbc
  simp only [orderFourteenModelU, orderFourteenModelT,
    orderFourteenModelNumerator, orderFourteenModelDenominator]
  field_simp [hd, hC]

/-- The displayed `V` is exactly `4(2s+t+1)`. -/
theorem orderFourteenModelV_eq
    {b c : ℚ} (hbc : b ≠ c) (hC : tateSevenAux b c ≠ 0) :
    orderFourteenModelV b c =
      4 * (2 * orderFourteenModelS b c +
        orderFourteenModelT b c + 1) := by
  have hd : b - c ≠ 0 := sub_ne_zero.mpr hbc
  simp only [orderFourteenModelV, orderFourteenModelS,
    orderFourteenModelT, orderFourteenModelNumerator,
    orderFourteenModelDenominator]
  field_simp [hd, hC]
  ring

/-- The denominator-minimized `V` agrees, on the parameter curve, with the
formula obtained by directly solving the usual forward parametrization. -/
theorem orderFourteenModelV_eq_tate_formula
    {b c : ℚ} (hb : b ≠ 0) (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelV b c =
      4 * (b - 2 * c ^ 2 - c) * tateSixNumerator b c /
        (b * (c ^ 2 + c - b) ^ 2) := by
  have hd : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hbridge := model_bridge_identity b c
  rw [hpoly] at hbridge
  have hdenLeft :
      (b - c) ^ 2 * tateSevenAux b c ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hd) hC
  have hdenRight :
      b * (c ^ 2 + c - b) ^ 2 ≠ 0 :=
    mul_ne_zero hb (pow_ne_zero 2 hA)
  simp only [orderFourteenModelV, orderFourteenModelNumerator]
  rw [div_eq_div_iff hdenLeft hdenRight]
  linear_combination
    4 * (b - c - 2 * c ^ 2) * hbridge

/-- The inverse rational map lands on the Weierstrass equation used by
`MazurTorsion.XOneFourteen.curve`. -/
theorem orderFourteenModel_curve_equation
    {b c : ℚ} (hbc : b ≠ c) (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelV b c ^ 2 =
      orderFourteenModelU b c *
        (orderFourteenModelU b c ^ 2 -
          11 * orderFourteenModelU b c + 32) := by
  rw [orderFourteenModelU_eq hbc hC, orderFourteenModelV_eq hbc hC]
  have hplane := orderFourteenModel_plane_equation hbc hpoly
  linear_combination 64 * hplane

/-- The image coordinates define an affine point on
`MazurTorsion.XOneFourteen.curve`. -/
theorem orderFourteenModel_nonsingular
    {b c : ℚ} (hbc : b ≠ c) (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    MazurTorsion.XOneFourteen.curve.toAffine.Nonsingular
      (orderFourteenModelU b c) (orderFourteenModelV b c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [MazurTorsion.XOneFourteen.curve]
  linear_combination orderFourteenModel_curve_equation hbc hC hpoly

/-- An admissible rational parameter does not map to the two-torsion
abscissa `U = 0`. -/
theorem orderFourteenModelU_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelU b c ≠ 0 := by
  have hR := orderFourteenModelNumerator_ne_zero hc hbc hpoly
  exact div_ne_zero (mul_ne_zero (by norm_num) hR)
    (model_denominator_ne_zero hbc hC)

/-- An admissible rational parameter does not map to either point with
abscissa `U = 4`. -/
theorem orderFourteenModelU_ne_four
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelU b c ≠ 4 := by
  have hD :=
    tateSevenYNumerator_ne_of_orderFourteenPolynomial hc hbc hpoly
  have hden := model_denominator_ne_zero hbc hC
  intro hU
  simp only [orderFourteenModelU] at hU
  have hcleared := (div_eq_iff hden).mp hU
  have hDzero : tateSevenYNumerator b c = 0 := by
    simp only [orderFourteenModelNumerator,
      orderFourteenModelDenominator] at hcleared
    linarith
  exact hD hDzero

/-- The certificate factors `A` and `B` exclude both points with
abscissa `U = 8`. -/
theorem orderFourteenModelU_ne_eight
    {b c : ℚ} (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0)
    (hB : tateSixNumerator b c ≠ 0)
    (hC : tateSevenAux b c ≠ 0) :
    orderFourteenModelU b c ≠ 8 := by
  have hden := model_denominator_ne_zero hbc hC
  intro hU
  simp only [orderFourteenModelU] at hU
  have hcleared := (div_eq_iff hden).mp hU
  have hsub :
      tateSevenYNumerator b c -
          (b - c) * tateSevenAux b c = 0 := by
    simp only [orderFourteenModelNumerator,
      orderFourteenModelDenominator] at hcleared
    linarith
  have hfactor := seven_y_sub_aux_identity b c
  have hzero :
      (c ^ 2 + c - b) * tateSixNumerator b c = 0 := by
    rw [← hfactor]
    exact hsub
  exact (mul_ne_zero hA hB) hzero

/-- All affine abscissae occurring among the five visible finite rational
points on the chosen `X₁(14)` model are excluded on the admissible Tate
locus. -/
theorem orderFourteenModelU_not_visible
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0)
    (hB : tateSixNumerator b c ≠ 0)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    orderFourteenModelU b c ≠ 0 ∧
      orderFourteenModelU b c ≠ 4 ∧
      orderFourteenModelU b c ≠ 8 := by
  exact ⟨orderFourteenModelU_ne_zero hc hbc hC hpoly,
    orderFourteenModelU_ne_four hc hbc hC hpoly,
    orderFourteenModelU_ne_eight hbc hA hB hC⟩

/-- The complete bridge needed by the order-fourteen argument: admissible
Tate parameters give a nonsingular rational point on the selected
`X₁(14)` model whose abscissa is not `0`, `4`, or `8`. -/
theorem orderFourteenModel_of_admissible
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0)
    (hB : tateSixNumerator b c ≠ 0)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderFourteenPolynomial b c = 0) :
    MazurTorsion.XOneFourteen.curve.toAffine.Nonsingular
        (orderFourteenModelU b c) (orderFourteenModelV b c) ∧
      orderFourteenModelU b c ≠ 0 ∧
      orderFourteenModelU b c ≠ 4 ∧
      orderFourteenModelU b c ≠ 8 := by
  refine ⟨orderFourteenModel_nonsingular hbc hC hpoly, ?_⟩
  exact orderFourteenModelU_not_visible hc hbc hA hB hC hpoly

/-- An exact rational point of order fourteen therefore produces an affine
point outside all three visible abscissae on `X₁(14)`.  This is the
end-to-end interface from the Tate certificate to the modular model. -/
theorem exists_orderFourteenModel_of_exact_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 14) :
    ∃ b c : ℚ,
      MazurTorsion.XOneFourteen.curve.toAffine.Nonsingular
          (orderFourteenModelU b c) (orderFourteenModelV b c) ∧
        orderFourteenModelU b c ≠ 0 ∧
        orderFourteenModelU b c ≠ 4 ∧
        orderFourteenModelU b c ≠ 8 := by
  obtain ⟨b, c, _u, _hu, _hb, hc, hbc, hA, hB, hC, hpoly, _hdisc⟩ :=
    exists_tateOrderFourteen_certificate E Q hQ
  exact ⟨b, c, orderFourteenModel_of_admissible
    hc hbc hA hB hC hpoly⟩

end MazurTorsion.Kubert
