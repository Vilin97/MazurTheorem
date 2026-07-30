/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderEighteenReduction

/-!
# An explicit genus-two model attached to order eighteen

The order-nine Tate-parameter equation admits the rational parameter

`d = c² / (b - c)`.

Away from the nondegenerate loci already supplied by
`exists_tateOrderEighteen_certificate`, it gives

`c = d²(d - 1)` and `b = c(d² - d + 1)`.

Combining this parametrization with the rational root of the Tate
two-division polynomial gives the auxiliary equation

`(2s + 1)(d²(d - 1)s² - (d² - d + 1)) = s²`.

The displayed rational change of variables then produces a point on

`Y² = X⁶ - 4X⁵ + 10X⁴ - 10X³ + 5X² - 2X + 1`.

This file proves only these algebraic reductions.  In particular, it does
not assert the rational-point classification of this genus-two curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The rational parameter on the nondegenerate order-nine Tate curve. -/
def orderNineParameterD (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)

/-- The auxiliary coordinate obtained from a root of the Tate two-division
polynomial. -/
def orderEighteenAuxiliaryS (b c r : ℚ) : ℚ :=
  ((1 - c) * r - b) / (2 * r * c)

/-- The equation in the order-nine parameter and the auxiliary
two-division coordinate. -/
def orderEighteenAuxiliaryPolynomial (d s : ℚ) : ℚ :=
  (2 * s + 1) *
      (d ^ 2 * (d - 1) * s ^ 2 - (d ^ 2 - d + 1)) -
    s ^ 2

/-- The abscissa in the standard genus-two model for `X₁(18)`. -/
def orderEighteenModelX (d s : ℚ) : ℚ :=
  (d - s + 2 * d * s) / (1 + d * s)

/-- The ordinate in the standard genus-two model for `X₁(18)`. -/
def orderEighteenModelY (d s : ℚ) : ℚ :=
  let X := orderEighteenModelX d s
  2 * X * d - (X ^ 3 - 2 * X ^ 2 + 3 * X - 1)

/-- The sextic defining the standard genus-two model for `X₁(18)`. -/
def orderEighteenHyperellipticPolynomial (X : ℚ) : ℚ :=
  X ^ 6 - 4 * X ^ 5 + 10 * X ^ 4 - 10 * X ^ 3 +
    5 * X ^ 2 - 2 * X + 1

lemma orderNinePolynomial_eq_difference_form (b c : ℚ) :
    orderNinePolynomial b c =
      c ^ 5 - (b - c) * c ^ 3 - (b - c) ^ 3 := by
  simp only [orderNinePolynomial]
  ring

lemma orderNineParameterD_ne_zero
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    orderNineParameterD b c ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)

/-- The nondegenerate order-nine Tate equation has the claimed rational
parametrization. -/
theorem orderNine_parameterization
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c)
    (hnine : orderNinePolynomial b c = 0) :
    c =
        orderNineParameterD b c ^ 2 *
          (orderNineParameterD b c - 1) ∧
      b =
        c *
          (orderNineParameterD b c ^ 2 -
            orderNineParameterD b c + 1) := by
  let d := orderNineParameterD b c
  have hnine' :
      c ^ 5 - (b - c) * c ^ 3 - (b - c) ^ 3 = 0 := by
    rw [← orderNinePolynomial_eq_difference_form]
    exact hnine
  have hcparam : c = d ^ 2 * (d - 1) := by
    dsimp [d, orderNineParameterD]
    field_simp [sub_ne_zero.mpr hbc]
    ring_nf at hnine' ⊢
    linear_combination -hnine'
  have hbparam : b = c * (d ^ 2 - d + 1) := by
    dsimp [d, orderNineParameterD]
    field_simp [sub_ne_zero.mpr hbc]
    ring_nf at hnine' ⊢
    linear_combination -hnine'
  exact ⟨hcparam, hbparam⟩

lemma orderNineParameterD_ne_one
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c)
    (hnine : orderNinePolynomial b c = 0) :
    orderNineParameterD b c ≠ 1 := by
  intro hd1
  have hcparam :=
    (orderNine_parameterization b c hc hbc hnine).1
  rw [hd1] at hcparam
  norm_num at hcparam
  exact hc hcparam

lemma root_ne_zero_of_tateTwoDivisionPolynomial
    (b c r : ℚ) (hb : b ≠ 0)
    (htwo : tateTwoDivisionPolynomial b c r = 0) :
    r ≠ 0 := by
  intro hr
  subst r
  simp [tateTwoDivisionPolynomial, hb] at htwo

/-- After the order-nine parametrization, a root of the two-division
polynomial gives the displayed auxiliary equation. -/
theorem orderEighteenAuxiliaryPolynomial_eq_zero
    (b c r d : ℚ) (hc : c ≠ 0) (hr : r ≠ 0)
    (hcparam : c = d ^ 2 * (d - 1))
    (hbparam : b = c * (d ^ 2 - d + 1))
    (htwo : tateTwoDivisionPolynomial b c r = 0) :
    orderEighteenAuxiliaryPolynomial d
        (orderEighteenAuxiliaryS b c r) = 0 := by
  calc
    orderEighteenAuxiliaryPolynomial d
          (orderEighteenAuxiliaryS b c r) =
        -(d ^ 2 - d + 1) *
            tateTwoDivisionPolynomial b c r /
          (4 * r ^ 3 * c) := by
      simp only [orderEighteenAuxiliaryPolynomial,
        orderEighteenAuxiliaryS, tateTwoDivisionPolynomial]
      field_simp [hr, hc]
      rw [hbparam, hcparam]
      ring
    _ = 0 := by rw [htwo]; simp

/-- The denominator in the genus-two change of variables cannot vanish on
the nondegenerate auxiliary curve. -/
lemma one_add_mul_ne_zero_of_orderEighteenAuxiliary
    (d s : ℚ) (hd : d ≠ 0) (hd1 : d ≠ 1)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    1 + d * s ≠ 0 := by
  intro hden
  have hs : s = -1 / d := by
    field_simp [hd]
    linear_combination hden
  have hspecial :
      orderEighteenAuxiliaryPolynomial d (-1 / d) =
        -(d - 1) ^ 4 / d ^ 2 := by
    simp only [orderEighteenAuxiliaryPolynomial]
    field_simp [hd]
    ring
  rw [hs, hspecial] at haux
  have hpow : (d - 1) ^ 4 = 0 := by
    field_simp [hd] at haux
    exact neg_eq_zero.mp (by simpa using haux)
  exact (pow_ne_zero 4 (sub_ne_zero.mpr hd1)) hpow

/-- The rational change of variables sends the auxiliary equation to the
standard sextic model. -/
theorem orderEighteenModel_equation
    (d s : ℚ) (hden : 1 + d * s ≠ 0)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    orderEighteenModelY d s ^ 2 =
      orderEighteenHyperellipticPolynomial
        (orderEighteenModelX d s) := by
  have hidentity :
      orderEighteenModelY d s ^ 2 -
          orderEighteenHyperellipticPolynomial
            (orderEighteenModelX d s) =
        4 * (d - 1) ^ 2 *
            (2 * d * s + d - s) *
            orderEighteenAuxiliaryPolynomial d s /
          (1 + d * s) ^ 4 := by
    simp only [orderEighteenModelY, orderEighteenModelX,
      orderEighteenHyperellipticPolynomial,
      orderEighteenAuxiliaryPolynomial]
    field_simp [hden]
    ring
  apply sub_eq_zero.mp
  calc
    orderEighteenModelY d s ^ 2 -
          orderEighteenHyperellipticPolynomial
            (orderEighteenModelX d s) =
        4 * (d - 1) ^ 2 *
            (2 * d * s + d - s) *
            orderEighteenAuxiliaryPolynomial d s /
          (1 + d * s) ^ 4 := hidentity
    _ = 0 := by rw [haux]; simp

/-- A nondegenerate point of the auxiliary curve does not map to the
affine point with abscissa zero. -/
lemma orderEighteenModelX_ne_zero
    (d s : ℚ) (hd1 : d ≠ 1)
    (hden : 1 + d * s ≠ 0)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    orderEighteenModelX d s ≠ 0 := by
  intro hX
  have hnum : d - s + 2 * d * s = 0 := by
    simp only [orderEighteenModelX] at hX
    field_simp [hden] at hX
    simpa [mul_comm, mul_left_comm, mul_assoc] using hX
  have hcoef : 2 * d - 1 ≠ 0 := by
    intro hcoef
    have hdhalf : d = 1 / 2 := by linarith
    rw [hdhalf] at hnum
    norm_num at hnum
  have hs : s = -d / (2 * d - 1) := by
    apply (eq_div_iff hcoef).2
    linear_combination hnum
  have hspecial :
      orderEighteenAuxiliaryPolynomial d
          (-d / (2 * d - 1)) =
        -(d - 1) ^ 5 / (2 * d - 1) ^ 3 := by
    simp only [orderEighteenAuxiliaryPolynomial]
    field_simp [hcoef]
    ring
  rw [hs, hspecial] at haux
  have hpow : (d - 1) ^ 5 = 0 := by
    rcases (div_eq_zero_iff.mp haux) with hneg | hdenzero
    · exact neg_eq_zero.mp hneg
    · exact (pow_ne_zero 3 hcoef hdenzero).elim
  exact (pow_ne_zero 5 (sub_ne_zero.mpr hd1)) hpow

/-- A nondegenerate point of the auxiliary curve does not map to the
affine point with abscissa one. -/
lemma orderEighteenModelX_ne_one
    (d s : ℚ) (hd : d ≠ 0) (hd1 : d ≠ 1)
    (hden : 1 + d * s ≠ 0)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    orderEighteenModelX d s ≠ 1 := by
  intro hX
  have hnum :
      d - s + 2 * d * s = 1 + d * s := by
    simp only [orderEighteenModelX] at hX
    field_simp [hden] at hX
    simpa [mul_comm, mul_left_comm, mul_assoc] using hX
  have hfac : (d - 1) * (s + 1) = 0 := by
    linear_combination hnum
  have hsadd : s + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with hdsub | hsadd
    · exact (sub_ne_zero.mpr hd1 hdsub).elim
    · exact hsadd
  have hs : s = -1 := by linarith
  have hspecial :
      orderEighteenAuxiliaryPolynomial d (-1) =
        -d * (d - 1) ^ 2 := by
    simp only [orderEighteenAuxiliaryPolynomial]
    ring
  rw [hs, hspecial] at haux
  rcases mul_eq_zero.mp haux with hnegd | hpow
  · exact hd (neg_eq_zero.mp hnegd)
  · exact (pow_ne_zero 2 (sub_ne_zero.mpr hd1)) hpow

/-- A point of exact order eighteen supplies a nondegenerate rational point
on the explicit genus-two model, together with all Tate parameters,
denominator conditions, source equations, and the original discriminant
scale.

This is only a reduction theorem.  It does not classify the rational
points of the genus-two curve. -/
theorem exists_orderEighteen_genusTwo_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 18) :
    ∃ b c u r d s : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧ r ≠ 0 ∧
      d = orderNineParameterD b c ∧ d ≠ 0 ∧ d ≠ 1 ∧
      c = d ^ 2 * (d - 1) ∧
      b = c * (d ^ 2 - d + 1) ∧
      s = orderEighteenAuxiliaryS b c r ∧
      orderNinePolynomial b c = 0 ∧
      tateTwoDivisionPolynomial b c r = 0 ∧
      orderEighteenAuxiliaryPolynomial d s = 0 ∧
      1 + d * s ≠ 0 ∧
      orderEighteenModelX d s ≠ 0 ∧
      orderEighteenModelX d s ≠ 1 ∧
      orderEighteenModelY d s ^ 2 =
        orderEighteenHyperellipticPolynomial
          (orderEighteenModelX d s) ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
  obtain ⟨b, c, u, r, hu, hb, hc, hbc, hnine, htwo, hdisc⟩ :=
    exists_tateOrderEighteen_certificate E Q hQ
  let d := orderNineParameterD b c
  let s := orderEighteenAuxiliaryS b c r
  have hd : d ≠ 0 :=
    orderNineParameterD_ne_zero b c hc hbc
  have hd1 : d ≠ 1 :=
    orderNineParameterD_ne_one b c hc hbc hnine
  obtain ⟨hcparam, hbparam⟩ :=
    orderNine_parameterization b c hc hbc hnine
  have hr : r ≠ 0 :=
    root_ne_zero_of_tateTwoDivisionPolynomial b c r hb htwo
  have haux : orderEighteenAuxiliaryPolynomial d s = 0 :=
    orderEighteenAuxiliaryPolynomial_eq_zero
      b c r d hc hr hcparam hbparam htwo
  have hden : 1 + d * s ≠ 0 :=
    one_add_mul_ne_zero_of_orderEighteenAuxiliary
      d s hd hd1 haux
  have hX0 : orderEighteenModelX d s ≠ 0 :=
    orderEighteenModelX_ne_zero d s hd1 hden haux
  have hX1 : orderEighteenModelX d s ≠ 1 :=
    orderEighteenModelX_ne_one d s hd hd1 hden haux
  have hmodel :
      orderEighteenModelY d s ^ 2 =
        orderEighteenHyperellipticPolynomial
          (orderEighteenModelX d s) :=
    orderEighteenModel_equation d s hden haux
  exact
    ⟨b, c, u, r, d, s, hu, hb, hc, hbc, hr, rfl, hd, hd1,
      hcparam, hbparam, rfl, hnine, htwo, haux, hden, hX0, hX1,
      hmodel, hdisc⟩

end MazurTorsion.Kubert
