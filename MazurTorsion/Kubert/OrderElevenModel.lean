/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderElevenReduction

/-!
# The order-eleven Tate curve and `X₁(11)`

This file gives a denominator-safe bridge from the compact Tate parameter
equation in `OrderElevenReduction` to the standard model

`v² + v = u³ - u²`

of `X₁(11)`.

Put

`r = b/c`, `q = c²/(b-c)`.

The compact polynomial is a nonzero scalar multiple of the raw equation

`r² - rq³ + 3rq² - 4rq + q = 0`.

Writing

`N = rq - 2r + 1`, `K = q² - q - r + 1`,

the checked rational map is

`u = K/N`,

`v = (q-r)K/N² - 1`.

For context, this is the composition of the standard raw-to-plane map

`x = (q-r)/N`, `y = N/K`

to `x²y - xy² + y - 1 = 0` with the projective linear change

`u = 1/y`, `v = x/y - 1`.

The raw equation proves `N`, `K`, and `q-r` nonzero on the honest Tate
locus.  Thus an exact order-eleven point maps to an affine point whose
abscissa is neither `0` nor `1`, the abscissae of the four rational
finite cusp points on this model.  No rational-point classification is
asserted.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEleven

/-- The standard elliptic model `v²+v=u³-u²` of `X₁(11)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, -1, 1, 0, 0⟩

private instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

end MazurTorsion.XOneEleven

namespace MazurTorsion.Kubert

/-- The raw affine equation for `X₁(11)`. -/
def orderElevenRawPolynomial (r q : ℚ) : ℚ :=
  r ^ 2 - r * q ^ 3 + 3 * r * q ^ 2 -
    4 * r * q + q

/-- The raw parameter `r=b/c`. -/
def orderElevenRawR (b c : ℚ) : ℚ :=
  b / c

/-- The raw parameter `q=c²/(b-c)`. -/
def orderElevenRawQ (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)

/-- The Weierstrass abscissa obtained from raw parameters. -/
def orderElevenModelUOfRaw (r q : ℚ) : ℚ :=
  (q ^ 2 - q - r + 1) /
    (r * q - 2 * r + 1)

/-- The Weierstrass ordinate obtained from raw parameters. -/
def orderElevenModelVOfRaw (r q : ℚ) : ℚ :=
  (q - r) * (q ^ 2 - q - r + 1) /
      (r * q - 2 * r + 1) ^ 2 - 1

/-- The `u`-coordinate attached directly to Tate parameters. -/
def orderElevenModelU (b c : ℚ) : ℚ :=
  orderElevenModelUOfRaw
    (orderElevenRawR b c) (orderElevenRawQ b c)

/-- The `v`-coordinate attached directly to Tate parameters. -/
def orderElevenModelV (b c : ℚ) : ℚ :=
  orderElevenModelVOfRaw
    (orderElevenRawR b c) (orderElevenRawQ b c)

/-- The compact Tate equation is the raw `X₁(11)` equation after the
displayed denominator-safe substitution. -/
theorem orderElevenRawPolynomial_eq_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hpoly : orderElevenPolynomial b c = 0) :
    orderElevenRawPolynomial
      (orderElevenRawR b c) (orderElevenRawQ b c) = 0 := by
  have hd : b - c ≠ 0 :=
    sub_ne_zero.mpr hbc
  dsimp [orderElevenRawR, orderElevenRawQ,
    orderElevenRawPolynomial]
  simp only [orderElevenPolynomial,
    orderElevenSixNumerator] at hpoly
  field_simp [hc, hd]
  linear_combination hpoly

private lemma orderEleven_raw_middle_ne_zero
    {r q : ℚ} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hraw : orderElevenRawPolynomial r q = 0) :
    r * q - 2 * r + 1 ≠ 0 := by
  intro hmiddle
  have hq : q = (2 * r - 1) / r := by
    field_simp [hr0]
    linarith
  have hid :
      orderElevenRawPolynomial r ((2 * r - 1) / r) =
        (r - 1) ^ 4 / r ^ 2 := by
    simp only [orderElevenRawPolynomial]
    field_simp [hr0]
    ring
  rw [hq, hid] at hraw
  have hden : r ^ 2 ≠ 0 :=
    pow_ne_zero 2 hr0
  have hpower : (r - 1) ^ 4 = 0 :=
    (div_eq_zero_iff.mp hraw).resolve_right hden
  exact
    (pow_ne_zero 4 (sub_ne_zero.mpr hr1)) hpower

private lemma orderEleven_raw_zero_factor_ne_zero
    {r q : ℚ} (hq1 : q ≠ 1)
    (hraw : orderElevenRawPolynomial r q = 0) :
    q ^ 2 - q - r + 1 ≠ 0 := by
  intro hfactor
  have hr : r = q ^ 2 - q + 1 := by
    linarith
  have hid :
      orderElevenRawPolynomial (q ^ 2 - q + 1) q =
        -(q - 1) ^ 5 := by
    simp only [orderElevenRawPolynomial]
    ring
  rw [hr, hid] at hraw
  have hpower : (q - 1) ^ 5 = 0 :=
    neg_eq_zero.mp hraw
  exact
    (pow_ne_zero 5 (sub_ne_zero.mpr hq1)) hpower

private lemma orderEleven_raw_one_factor_ne_zero
    {r q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hraw : orderElevenRawPolynomial r q = 0) :
    q - r ≠ 0 := by
  intro hdifference
  have hr : r = q := by
    linarith
  have hid :
      orderElevenRawPolynomial q q =
        -q * (q - 1) ^ 3 := by
    simp only [orderElevenRawPolynomial]
    ring
  rw [hr, hid] at hraw
  have hnonzero :
      -q * (q - 1) ^ 3 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hq0)
      (pow_ne_zero 3 (sub_ne_zero.mpr hq1))
  exact hnonzero hraw

private lemma orderEleven_raw_r_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0) :
    orderElevenRawR b c ≠ 0 :=
  div_ne_zero hb hc

private lemma orderEleven_raw_r_ne_one
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    orderElevenRawR b c ≠ 1 := by
  intro hr
  simp only [orderElevenRawR] at hr
  have hcleared := (div_eq_iff hc).mp hr
  exact hbc (by simpa using hcleared)

private lemma orderEleven_raw_q_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    orderElevenRawQ b c ≠ 0 :=
  div_ne_zero (pow_ne_zero 2 hc)
    (sub_ne_zero.mpr hbc)

private lemma orderEleven_raw_q_ne_one
    {b c : ℚ} (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0) :
    orderElevenRawQ b c ≠ 1 := by
  intro hq
  simp only [orderElevenRawQ] at hq
  have hcleared :=
    (div_eq_iff (sub_ne_zero.mpr hbc)).mp hq
  apply hA
  linear_combination hcleared

/-- Every denominator and both rational finite-cusp factors of the model
map are nonzero on the admissible Tate locus. -/
theorem orderElevenModel_factors_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    let r := orderElevenRawR b c
    let q := orderElevenRawQ b c
    r * q - 2 * r + 1 ≠ 0 ∧
      q ^ 2 - q - r + 1 ≠ 0 ∧
      q - r ≠ 0 ∧ q ≠ 1 := by
  let r := orderElevenRawR b c
  let q := orderElevenRawQ b c
  have hr0 : r ≠ 0 := by
    simpa [r] using orderEleven_raw_r_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    simpa [r] using orderEleven_raw_r_ne_one hc hbc
  have hq0 : q ≠ 0 := by
    simpa [q] using orderEleven_raw_q_ne_zero hc hbc
  have hq1 : q ≠ 1 := by
    simpa [q] using orderEleven_raw_q_ne_one hbc hA
  have hraw : orderElevenRawPolynomial r q = 0 := by
    simpa [r, q] using
      orderElevenRawPolynomial_eq_zero hc hbc hpoly
  exact
    ⟨orderEleven_raw_middle_ne_zero hr0 hr1 hraw,
      orderEleven_raw_zero_factor_ne_zero hq1 hraw,
      orderEleven_raw_one_factor_ne_zero hq0 hq1 hraw,
      hq1⟩

private lemma orderEleven_curve_equation_of_numerator
    {n k l : ℚ} (hn : n ≠ 0)
    (hnum :
      l ^ 2 * k ^ 2 - l * k * n ^ 2 -
        k ^ 3 * n + k ^ 2 * n ^ 2 = 0) :
    (l * k / n ^ 2 - 1) ^ 2 +
          (l * k / n ^ 2 - 1) =
        (k / n) ^ 3 - (k / n) ^ 2 := by
  field_simp [hn]
  linear_combination hnum

/-- The raw rational formulas satisfy the standard Weierstrass equation
whenever their sole denominator is nonzero. -/
theorem orderElevenModel_curve_equation_of_raw
    {r q : ℚ} (hmiddle : r * q - 2 * r + 1 ≠ 0)
    (hraw : orderElevenRawPolynomial r q = 0) :
    orderElevenModelVOfRaw r q ^ 2 +
          orderElevenModelVOfRaw r q =
        orderElevenModelUOfRaw r q ^ 3 -
          orderElevenModelUOfRaw r q ^ 2 := by
  have hnum :
      (q - r) ^ 2 * (q ^ 2 - q - r + 1) ^ 2 -
            (q - r) * (q ^ 2 - q - r + 1) *
              (r * q - 2 * r + 1) ^ 2 -
          (q ^ 2 - q - r + 1) ^ 3 *
            (r * q - 2 * r + 1) +
        (q ^ 2 - q - r + 1) ^ 2 *
          (r * q - 2 * r + 1) ^ 2 = 0 := by
    simp only [orderElevenRawPolynomial] at hraw
    linear_combination
      (q - 1) * (q - r) *
        (q ^ 2 - q - r + 1) * hraw
  simpa [orderElevenModelUOfRaw,
    orderElevenModelVOfRaw] using
      orderEleven_curve_equation_of_numerator
        hmiddle hnum

/-- The Tate-parameter image lies on `v²+v=u³-u²`. -/
theorem orderElevenModel_curve_equation
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    orderElevenModelV b c ^ 2 +
          orderElevenModelV b c =
        orderElevenModelU b c ^ 3 -
          orderElevenModelU b c ^ 2 := by
  have hfactors :=
    orderElevenModel_factors_ne_zero
      hb hc hbc hA hpoly
  have hraw :=
    orderElevenRawPolynomial_eq_zero hc hbc hpoly
  simpa [orderElevenModelU, orderElevenModelV] using
    orderElevenModel_curve_equation_of_raw
      hfactors.1 hraw

/-- The image coordinates define an affine point on the standard
`X₁(11)` model. -/
theorem orderElevenModel_nonsingular
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    MazurTorsion.XOneEleven.curve.toAffine.Nonsingular
      (orderElevenModelU b c) (orderElevenModelV b c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [MazurTorsion.XOneEleven.curve]
  linear_combination
    orderElevenModel_curve_equation hb hc hbc hA hpoly

/-- The image avoids the rational finite-cusp abscissa `u=0`. -/
theorem orderElevenModelU_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    orderElevenModelU b c ≠ 0 := by
  have hfactors :=
    orderElevenModel_factors_ne_zero
      hb hc hbc hA hpoly
  exact div_ne_zero hfactors.2.1 hfactors.1

/-- The image avoids the rational finite-cusp abscissa `u=1`. -/
theorem orderElevenModelU_ne_one
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    orderElevenModelU b c ≠ 1 := by
  let r := orderElevenRawR b c
  let q := orderElevenRawQ b c
  have hfactors :=
    orderElevenModel_factors_ne_zero
      hb hc hbc hA hpoly
  have hmiddle : r * q - 2 * r + 1 ≠ 0 := by
    simpa only [r, q] using hfactors.1
  have hdifference : q - r ≠ 0 := by
    simpa only [r, q] using hfactors.2.2.1
  have hq1 : q ≠ 1 := by
    simpa only [r, q] using hfactors.2.2.2
  intro hU
  simp only [orderElevenModelU,
    orderElevenModelUOfRaw] at hU
  change
    (q ^ 2 - q - r + 1) /
      (r * q - 2 * r + 1) = 1 at hU
  have hcleared := (div_eq_iff hmiddle).mp hU
  have hzero :
      (q - 1) * (q - r) = 0 := by
    linear_combination hcleared
  exact
    (mul_ne_zero (sub_ne_zero.mpr hq1) hdifference) hzero

/-- The complete bridge: admissible Tate parameters give a nonsingular
point outside both rational finite-cusp abscissae on `X₁(11)`. -/
theorem orderElevenModel_of_admissible
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    MazurTorsion.XOneEleven.curve.toAffine.Nonsingular
        (orderElevenModelU b c) (orderElevenModelV b c) ∧
      orderElevenModelU b c ≠ 0 ∧
      orderElevenModelU b c ≠ 1 := by
  exact
    ⟨orderElevenModel_nonsingular hb hc hbc hA hpoly,
      orderElevenModelU_ne_zero hb hc hbc hA hpoly,
      orderElevenModelU_ne_one hb hc hbc hA hpoly⟩

/-- An exact rational point of order eleven produces an affine point on
the standard `X₁(11)` model outside all rational cusp points: the point
at infinity is avoided by affineness, and the four finite ones have
abscissa `0` or `1`. -/
theorem exists_orderElevenModel_of_exact_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 11) :
    ∃ b c : ℚ,
      MazurTorsion.XOneEleven.curve.toAffine.Nonsingular
          (orderElevenModelU b c) (orderElevenModelV b c) ∧
        orderElevenModelU b c ≠ 0 ∧
        orderElevenModelU b c ≠ 1 := by
  obtain
      ⟨b, c, _u, _hu, hb, hc, hbc, hA, _hB,
        hpoly, _hdisc⟩ :=
    exists_tateOrderEleven_certificate E Q hQ
  exact
    ⟨b, c,
      orderElevenModel_of_admissible
        hb hc hbc hA hpoly⟩

end MazurTorsion.Kubert
