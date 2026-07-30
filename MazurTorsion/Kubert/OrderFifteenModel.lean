/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFifteenReduction
import MazurTorsion.NumberTheory.XOneFifteenDescent

open scoped WeierstrassCurve.Affine

/-!
# The order-fifteen Tate curve and `X₁(15)`

This file gives a denominator-safe birational bridge from the compact
Tate-parameter equation in `OrderFifteenReduction` to the standard plane
model

`s² + s t + s = t³ + t²`

and hence to the Weierstrass model

`V² = U(U² - 7U + 16)`.

Put `r = b/c` and `q = c²/(b-c)`.  Then `b = r c` and
`c = q(r-1)`, the usual raw Tate parameters.  Direct expansion gives

`orderFifteenPolynomial b c =
  -c³(b-c)⁵ orderFifteenRawPolynomial r q`.

The raw curve is transformed to the standard plane model by

`t = -(q²r+q²-3qr+r) / ((q-1)(qr-2r+1))`,

`s = -(q²-qr²-qr+3r²-3r+1) / (qr-2r+1)²`.

Every denominator is proved nonzero from the raw equation and the honest
Tate conditions.  The same calculation shows that the resulting
Weierstrass abscissa is neither `0` nor `4`.
-/

namespace MazurTorsion.Kubert

/-- Sutherland's raw affine equation for `X₁(15)`. -/
def orderFifteenRawPolynomial (r q : ℚ) : ℚ :=
  r ^ 3 -
    r ^ 2 * q ^ 5 + 7 * r ^ 2 * q ^ 4 -
    18 * r ^ 2 * q ^ 3 + 19 * r ^ 2 * q ^ 2 -
    10 * r ^ 2 * q - r * q ^ 5 + 4 * r * q ^ 4 -
    5 * r * q ^ 2 + 5 * r * q -
    q ^ 5 + q ^ 4 - q ^ 3 + q ^ 2 - q

/-- The raw Tate parameter `r = b/c`. -/
def orderFifteenRawR (b c : ℚ) : ℚ :=
  b / c

/-- The raw Tate parameter `q = c²/(b-c)`. -/
def orderFifteenRawQ (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)

/-- The standard-plane `t`-coordinate obtained from the raw model. -/
def orderFifteenPlaneTOfRaw (r q : ℚ) : ℚ :=
  -(q ^ 2 * r + q ^ 2 - 3 * q * r + r) /
    ((q - 1) * (q * r - 2 * r + 1))

/-- The standard-plane `s`-coordinate obtained from the raw model. -/
def orderFifteenPlaneSOfRaw (r q : ℚ) : ℚ :=
  -(q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) /
    (q * r - 2 * r + 1) ^ 2

/-- The standard-plane `t`-coordinate attached directly to Tate parameters. -/
def orderFifteenPlaneT (b c : ℚ) : ℚ :=
  orderFifteenPlaneTOfRaw
    (orderFifteenRawR b c) (orderFifteenRawQ b c)

/-- The standard-plane `s`-coordinate attached directly to Tate parameters. -/
def orderFifteenPlaneS (b c : ℚ) : ℚ :=
  orderFifteenPlaneSOfRaw
    (orderFifteenRawR b c) (orderFifteenRawQ b c)

/-- The `U`-coordinate on `XOneFifteen.curve`. -/
def orderFifteenModelU (b c : ℚ) : ℚ :=
  4 * (orderFifteenPlaneT b c + 1)

/-- The `V`-coordinate on `XOneFifteen.curve`. -/
def orderFifteenModelV (b c : ℚ) : ℚ :=
  4 *
    (2 * orderFifteenPlaneS b c +
      orderFifteenPlaneT b c + 1)

/-- The compact Tate polynomial is the raw `X₁(15)` polynomial after the
displayed denominator-safe substitution. -/
theorem orderFifteenRawPolynomial_eq_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenRawPolynomial
      (orderFifteenRawR b c) (orderFifteenRawQ b c) = 0 := by
  have hd : b - c ≠ 0 :=
    sub_ne_zero.mpr hbc
  dsimp [orderFifteenRawR, orderFifteenRawQ,
    orderFifteenRawPolynomial]
  simp only [orderFifteenPolynomial] at hpoly
  field_simp [hc, hd]
  linear_combination -hpoly

private lemma raw_q_ne_one
    {r q : ℚ} (hr1 : r ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q ≠ 1 := by
  intro hq
  subst q
  have hpower : (r - 1) ^ 3 = 0 := by
    simp only [orderFifteenRawPolynomial] at hraw
    linear_combination hraw
  exact (pow_ne_zero 3 (sub_ne_zero.mpr hr1)) hpower

private lemma raw_middle_denominator_ne_zero
    {r q : ℚ} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q * r - 2 * r + 1 ≠ 0 := by
  intro hmiddle
  have hq : q = (2 * r - 1) / r := by
    field_simp [hr0]
    linarith
  have hid :
      orderFifteenRawPolynomial r ((2 * r - 1) / r) =
        (r - 1) ^ 8 / r ^ 5 := by
    simp only [orderFifteenRawPolynomial]
    field_simp [hr0]
    ring
  rw [hq, hid] at hraw
  field_simp [hr0] at hraw
  have hpower : (r - 1) ^ 8 = 0 := by
    simpa using hraw
  exact (pow_ne_zero 8 (sub_ne_zero.mpr hr1)) hpower

private lemma raw_zero_abscissa_factor_ne_zero
    {r q : ℚ} (hq1 : q ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q ^ 2 - q - r + 1 ≠ 0 := by
  intro hfactor
  have hr : r = q ^ 2 - q + 1 := by
    linarith
  have hid :
      orderFifteenRawPolynomial (q ^ 2 - q + 1) q =
        -(q - 1) ^ 9 := by
    simp only [orderFifteenRawPolynomial]
    ring
  rw [hr, hid] at hraw
  have hpower : (q - 1) ^ 9 = 0 :=
    neg_eq_zero.mp hraw
  exact (pow_ne_zero 9 (sub_ne_zero.mpr hq1)) hpower

private lemma raw_four_abscissa_factor_ne_zero
    {r q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q ^ 2 * r + q ^ 2 - 3 * q * r + r ≠ 0 := by
  intro hfactor
  have hcoefficient : q ^ 2 - 3 * q + 1 ≠ 0 := by
    intro hcoefficient
    have hqSq : q ^ 2 = 0 := by
      linear_combination hfactor - r * hcoefficient
    exact (pow_ne_zero 2 hq0) hqSq
  have hr :
      r = -q ^ 2 / (q ^ 2 - 3 * q + 1) := by
    apply (eq_div_iff hcoefficient).2
    linear_combination hfactor
  let m : ℚ := q ^ 2 - 3 * q + 1
  have hm : m = q ^ 2 - 3 * q + 1 :=
    rfl
  have hm0 : m ≠ 0 := by
    simpa [m] using hcoefficient
  have hid :
      orderFifteenRawPolynomial
          (-q ^ 2 / m) q =
        -q * (q - 1) ^ 10 /
          m ^ 3 := by
    simp only [orderFifteenRawPolynomial]
    field_simp [hm0]
    rw [hm]
    ring
  have hrm : r = -q ^ 2 / m := by
    simpa [m] using hr
  rw [hrm, hid] at hraw
  have hdenominator :
      m ^ 3 ≠ 0 :=
    pow_ne_zero 3 hm0
  have hnumerator :
      -q * (q - 1) ^ 10 = 0 :=
    (div_eq_zero_iff.mp hraw).resolve_right hdenominator
  have hnonzero :
      -q * (q - 1) ^ 10 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hq0)
      (pow_ne_zero 10 (sub_ne_zero.mpr hq1))
  exact hnonzero hnumerator

private lemma plane_equation_of_numerator
    {a n d l : ℚ} (ha : a ≠ 0) (hn : n ≠ 0)
    (hnum :
      a ^ 3 * l ^ 2 + a ^ 2 * n * l * d -
        a ^ 3 * n ^ 2 * l + n * d ^ 3 -
        a * n ^ 2 * d ^ 2 = 0) :
    (-l / n ^ 2) ^ 2 +
          (-l / n ^ 2) * (-d / (a * n)) +
          (-l / n ^ 2) =
        (-d / (a * n)) ^ 3 +
          (-d / (a * n)) ^ 2 := by
  field_simp [ha, hn]
  linear_combination hnum

private lemma four_neg_div_add_one
    {a n d k : ℚ} (ha : a ≠ 0) (hn : n ≠ 0)
    (hrelation : a * n - d = -k) :
    4 * ((-d) / (a * n) + 1) =
      -4 * k / (a * n) := by
  field_simp [ha, hn]
  linear_combination hrelation

/-- The raw birational formulas satisfy the standard plane equation whenever
their two denominators are nonzero. -/
theorem orderFifteenPlane_equation_of_raw
    {r q : ℚ} (hq1 : q ≠ 1)
    (hmiddle : q * r - 2 * r + 1 ≠ 0)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    let t := orderFifteenPlaneTOfRaw r q
    let s := orderFifteenPlaneSOfRaw r q
    s ^ 2 + s * t + s = t ^ 3 + t ^ 2 := by
  have hqsub : q - 1 ≠ 0 :=
    sub_ne_zero.mpr hq1
  have hnumerator :
      (q - 1) ^ 3 *
            (q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) ^ 2 +
          (q - 1) ^ 2 * (q * r - 2 * r + 1) *
            (q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) *
            (q ^ 2 * r + q ^ 2 - 3 * q * r + r) -
          (q - 1) ^ 3 * (q * r - 2 * r + 1) ^ 2 *
            (q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) +
          (q * r - 2 * r + 1) *
            (q ^ 2 * r + q ^ 2 - 3 * q * r + r) ^ 3 -
          (q - 1) * (q * r - 2 * r + 1) ^ 2 *
            (q ^ 2 * r + q ^ 2 - 3 * q * r + r) ^ 2 =
        0 := by
    simp only [orderFifteenRawPolynomial] at hraw
    linear_combination
      -(q ^ 2 * r + q ^ 2 - 3 * q * r + r) * hraw
  simpa [orderFifteenPlaneTOfRaw, orderFifteenPlaneSOfRaw] using
    plane_equation_of_numerator hqsub hmiddle hnumerator

private lemma raw_r_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0) :
    orderFifteenRawR b c ≠ 0 := by
  exact div_ne_zero hb hc

private lemma raw_r_ne_one
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    orderFifteenRawR b c ≠ 1 := by
  intro hr
  simp only [orderFifteenRawR] at hr
  have hcleared := (div_eq_iff hc).mp hr
  exact hbc (by simpa using hcleared)

private lemma raw_q_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    orderFifteenRawQ b c ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 hc)
    (sub_ne_zero.mpr hbc)

private lemma raw_q_ne_one_of_admissible
    {b c : ℚ} (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0) :
    orderFifteenRawQ b c ≠ 1 := by
  intro hq
  simp only [orderFifteenRawQ] at hq
  have hcleared :=
    (div_eq_iff (sub_ne_zero.mpr hbc)).mp hq
  apply hA
  linear_combination hcleared

/-- Both denominators in the inverse map from the raw Tate parameter
curve to the standard plane model are nonzero on the admissible locus. -/
theorem orderFifteenPlane_denominators_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    (orderFifteenRawQ b c - 1) *
          (orderFifteenRawQ b c * orderFifteenRawR b c -
            2 * orderFifteenRawR b c + 1) ≠ 0 ∧
      (orderFifteenRawQ b c * orderFifteenRawR b c -
          2 * orderFifteenRawR b c + 1) ^ 2 ≠ 0 := by
  have hr0 := raw_r_ne_zero hb hc
  have hr1 := raw_r_ne_one hc hbc
  have hraw :=
    orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 :=
    raw_q_ne_one_of_admissible hbc hA
  have hmiddle :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  exact ⟨mul_ne_zero (sub_ne_zero.mpr hq1) hmiddle,
    pow_ne_zero 2 hmiddle⟩

/-- The checked inverse formulas carry every admissible Tate parameter
to the standard affine equation `s² + st + s = t³ + t²`. -/
theorem orderFifteenModel_plane_equation
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenPlaneS b c ^ 2 +
          orderFifteenPlaneS b c * orderFifteenPlaneT b c +
          orderFifteenPlaneS b c =
        orderFifteenPlaneT b c ^ 3 +
          orderFifteenPlaneT b c ^ 2 := by
  have hr0 := raw_r_ne_zero hb hc
  have hr1 := raw_r_ne_one hc hbc
  have hraw :=
    orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 :=
    raw_q_ne_one_of_admissible hbc hA
  have hmiddle :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  simpa [orderFifteenPlaneT, orderFifteenPlaneS] using
    orderFifteenPlane_equation_of_raw hq1 hmiddle hraw

/-- The inverse rational map lands on the Weierstrass equation used by
`MazurTorsion.XOneFifteen.curve`. -/
theorem orderFifteenModel_curve_equation
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenModelV b c ^ 2 =
      orderFifteenModelU b c *
        (orderFifteenModelU b c ^ 2 -
          7 * orderFifteenModelU b c + 16) := by
  have hplane :=
    orderFifteenModel_plane_equation hb hc hbc hA hpoly
  simpa [orderFifteenModelU, orderFifteenModelV] using
    MazurTorsion.XOneFifteen.to_curve_equation hplane

/-- The image coordinates define an affine point on
`MazurTorsion.XOneFifteen.curve`. -/
theorem orderFifteenModel_nonsingular
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    MazurTorsion.XOneFifteen.curve.toAffine.Nonsingular
      (orderFifteenModelU b c) (orderFifteenModelV b c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [MazurTorsion.XOneFifteen.curve]
  linear_combination
    orderFifteenModel_curve_equation hb hc hbc hA hpoly

/-- An admissible order-fifteen parameter does not map to the
two-torsion abscissa `U = 0`. -/
theorem orderFifteenModelU_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenModelU b c ≠ 0 := by
  let r := orderFifteenRawR b c
  let q := orderFifteenRawQ b c
  have hr0 : r ≠ 0 := by
    simpa [r] using raw_r_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    simpa [r] using raw_r_ne_one hc hbc
  have hraw : orderFifteenRawPolynomial r q = 0 := by
    simpa [r, q] using
      orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 : q ≠ 1 := by
    simpa [q] using raw_q_ne_one_of_admissible hbc hA
  have hmiddle : q * r - 2 * r + 1 ≠ 0 :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  have hfactor : q ^ 2 - q - r + 1 ≠ 0 :=
    raw_zero_abscissa_factor_ne_zero hq1 hraw
  have hcoordinate :
      orderFifteenModelU b c =
        -4 * (q ^ 2 - q - r + 1) /
          ((q - 1) * (q * r - 2 * r + 1)) := by
    simp only [orderFifteenModelU, orderFifteenPlaneT,
      orderFifteenPlaneTOfRaw]
    change
      4 *
          ((-(q ^ 2 * r + q ^ 2 - 3 * q * r + r)) /
              ((q - 1) * (q * r - 2 * r + 1)) + 1) =
        -4 * (q ^ 2 - q - r + 1) /
          ((q - 1) * (q * r - 2 * r + 1))
    apply four_neg_div_add_one
      (sub_ne_zero.mpr hq1) hmiddle
    ring
  rw [hcoordinate]
  exact div_ne_zero (mul_ne_zero (by norm_num) hfactor)
    (mul_ne_zero (sub_ne_zero.mpr hq1) hmiddle)

/-- An admissible order-fifteen parameter does not map to either
point with abscissa `U = 4`. -/
theorem orderFifteenModelU_ne_four
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenModelU b c ≠ 4 := by
  let r := orderFifteenRawR b c
  let q := orderFifteenRawQ b c
  have hr0 : r ≠ 0 := by
    simpa [r] using raw_r_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    simpa [r] using raw_r_ne_one hc hbc
  have hq0 : q ≠ 0 := by
    simpa [q] using raw_q_ne_zero hc hbc
  have hraw : orderFifteenRawPolynomial r q = 0 := by
    simpa [r, q] using
      orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 : q ≠ 1 := by
    simpa [q] using raw_q_ne_one_of_admissible hbc hA
  have hmiddle : q * r - 2 * r + 1 ≠ 0 :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  have hfactor :
      q ^ 2 * r + q ^ 2 - 3 * q * r + r ≠ 0 :=
    raw_four_abscissa_factor_ne_zero hq0 hq1 hraw
  have hcoordinate :
      orderFifteenModelU b c - 4 =
        -4 * (q ^ 2 * r + q ^ 2 - 3 * q * r + r) /
          ((q - 1) * (q * r - 2 * r + 1)) := by
    simp only [orderFifteenModelU, orderFifteenPlaneT,
      orderFifteenPlaneTOfRaw]
    change
      4 *
            ((-(q ^ 2 * r + q ^ 2 - 3 * q * r + r)) /
              ((q - 1) * (q * r - 2 * r + 1)) + 1) -
          4 =
        -4 * (q ^ 2 * r + q ^ 2 - 3 * q * r + r) /
          ((q - 1) * (q * r - 2 * r + 1))
    ring
  intro hU
  have hzero : orderFifteenModelU b c - 4 = 0 :=
    sub_eq_zero.mpr hU
  rw [hcoordinate] at hzero
  exact
    (div_ne_zero (mul_ne_zero (by norm_num) hfactor)
      (mul_ne_zero (sub_ne_zero.mpr hq1) hmiddle)) hzero

/-- The complete denominator-safe bridge: admissible Tate parameters give
a nonsingular point on the selected `X₁(15)` model outside both visible
finite abscissae. -/
theorem orderFifteenModel_of_admissible
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    MazurTorsion.XOneFifteen.curve.toAffine.Nonsingular
        (orderFifteenModelU b c) (orderFifteenModelV b c) ∧
      orderFifteenModelU b c ≠ 0 ∧
      orderFifteenModelU b c ≠ 4 := by
  exact ⟨orderFifteenModel_nonsingular hb hc hbc hA hpoly,
    orderFifteenModelU_ne_zero hb hc hbc hA hpoly,
    orderFifteenModelU_ne_four hb hc hbc hA hpoly⟩

/-- An exact rational point of order fifteen produces a nonsingular
rational point outside abscissae `0` and `4` on the chosen `X₁(15)`
model.  This is the end-to-end interface from the exact-order hypothesis
to the modular curve. -/
theorem exists_orderFifteenModel_of_exact_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 15) :
    ∃ b c : ℚ,
      MazurTorsion.XOneFifteen.curve.toAffine.Nonsingular
          (orderFifteenModelU b c) (orderFifteenModelV b c) ∧
        orderFifteenModelU b c ≠ 0 ∧
        orderFifteenModelU b c ≠ 4 := by
  obtain ⟨b, c, _u, _hu, hb, hc, hbc, hA, hpoly, _hdisc⟩ :=
    exists_tateOrderFifteen_certificate E Q hQ
  exact ⟨b, c,
    orderFifteenModel_of_admissible hb hc hbc hA hpoly⟩

end MazurTorsion.Kubert
