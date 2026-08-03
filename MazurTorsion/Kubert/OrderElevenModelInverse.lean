/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderElevenModel
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The reverse birational bridge from `X₁(11)` to Tate normal form

The forward map in `OrderElevenModel` sends admissible raw Tate parameters
`(r,q)` to the affine model

`v² + v = u³ - u²`.

This file constructs the reverse rational functions away from the four finite
rational cusps (`u = 0` and `u = 1`).  It proves that a noncusp model point
gives parameters `b,c` satisfying every denominator condition and the compact
order-eleven Tate equation.  Conversely, those checked conditions force the
marked Tate point `(0,0)` to have exact order eleven.

The discriminant calculation is closed by a checked resultant certificate:
singularity together with the raw modular equation would force a root of a
monic degree-five polynomial with no rational roots.  Thus the reconstructed
Tate cubic is genuinely elliptic.  No rational-point classification of
`X₁(11)` is used.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Reverse raw parameter `r` on the noncusp affine chart of `X₁(11)`. -/
def orderElevenRawROfModel (u v : ℚ) : ℚ :=
  (u - 1) / (u ^ 2 - v - 1)

/-- Reverse raw parameter `q` on the noncusp affine chart of `X₁(11)`. -/
def orderElevenRawQOfModel (u v : ℚ) : ℚ :=
  (u ^ 2 - u + v + 1) / (v + 1)

/-- Recover `c` from `r = b/c` and `q = c²/(b-c)`. -/
def orderElevenCOfModel (u v : ℚ) : ℚ :=
  orderElevenRawQOfModel u v * (orderElevenRawROfModel u v - 1)

/-- Recover `b = r*c` from a model point. -/
def orderElevenBOfModel (u v : ℚ) : ℚ :=
  orderElevenRawROfModel u v * orderElevenCOfModel u v

private lemma model_equation
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v) :
    v ^ 2 + v = u ^ 3 - u ^ 2 := by
  have h := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at h
  norm_num [MazurTorsion.XOneEleven.curve] at h
  linear_combination h

private lemma model_v_add_one_ne_zero
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    v + 1 ≠ 0 := by
  intro hv
  have hv' : v = -1 := by linarith
  have heq := model_equation hP
  rw [hv'] at heq
  have hzero : u ^ 2 * (u - 1) = 0 := by
    nlinarith
  exact (mul_ne_zero (pow_ne_zero 2 hu0) (sub_ne_zero.mpr hu1)) hzero

private lemma model_u_sq_sub_v_sub_one_ne_zero
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    u ^ 2 - v - 1 ≠ 0 := by
  intro hden
  have hv : v = u ^ 2 - 1 := by linarith
  have heq := model_equation hP
  rw [hv] at heq
  have hzero : u ^ 3 * (u - 1) = 0 := by
    nlinarith
  exact (mul_ne_zero (pow_ne_zero 3 hu0) (sub_ne_zero.mpr hu1)) hzero

private lemma model_q_numerator_ne_zero
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    u ^ 2 - u + v + 1 ≠ 0 := by
  intro hnum
  have hv : v = -u ^ 2 + u - 1 := by linarith
  have heq := model_equation hP
  rw [hv] at heq
  have hzero : u * (u - 1) ^ 3 = 0 := by
    nlinarith
  exact (mul_ne_zero hu0 (pow_ne_zero 3 (sub_ne_zero.mpr hu1))) hzero

private lemma model_v_ne_zero
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    v ≠ 0 := by
  intro hv
  have heq := model_equation hP
  rw [hv] at heq
  have hzero : u ^ 2 * (u - 1) = 0 := by
    nlinarith
  exact (mul_ne_zero (pow_ne_zero 2 hu0) (sub_ne_zero.mpr hu1)) hzero

private lemma orderElevenRawROfModel_ne_zero
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    orderElevenRawROfModel u v ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hu1)
    (model_u_sq_sub_v_sub_one_ne_zero hP hu0 hu1)

private lemma orderElevenRawROfModel_ne_one
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    orderElevenRawROfModel u v ≠ 1 := by
  intro hr
  have hden := model_u_sq_sub_v_sub_one_ne_zero hP hu0 hu1
  simp only [orderElevenRawROfModel] at hr
  have hcleared := (div_eq_one_iff_eq hden).mp hr
  have hv : v = u ^ 2 - u := by linarith
  have heq := model_equation hP
  rw [hv] at heq
  have hzero : u * (u - 1) ^ 3 = 0 := by
    nlinarith
  exact (mul_ne_zero hu0 (pow_ne_zero 3 (sub_ne_zero.mpr hu1))) hzero

private lemma orderElevenRawQOfModel_ne_zero
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    orderElevenRawQOfModel u v ≠ 0 :=
  div_ne_zero (model_q_numerator_ne_zero hP hu0 hu1)
    (model_v_add_one_ne_zero hP hu0 hu1)

private lemma orderElevenRawQOfModel_ne_one
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    orderElevenRawQOfModel u v ≠ 1 := by
  intro hq
  have hv1 := model_v_add_one_ne_zero hP hu0 hu1
  simp only [orderElevenRawQOfModel] at hq
  have hcleared := (div_eq_one_iff_eq hv1).mp hq
  have hzero : u * (u - 1) = 0 := by
    nlinarith
  exact (mul_ne_zero hu0 (sub_ne_zero.mpr hu1)) hzero

/-- The remaining factor of the Tate discriminant after the visibly nonzero
raw factors have been removed. -/
def orderElevenSingularFactor (r q : ℚ) : ℚ :=
  q ^ 3 * r ^ 2 - 2 * q ^ 3 * r + q ^ 3 -
    8 * q ^ 2 * r ^ 2 + 5 * q ^ 2 * r + 3 * q ^ 2 +
    16 * q * r ^ 2 - 20 * q * r + 3 * q + 1

/-- The degree-five eliminant obtained from the raw order-eleven equation and
the singular-discriminant factor. -/
def orderElevenSingularEliminant (q : ℚ) : ℚ :=
  q ^ 5 - 4 * q ^ 4 - 9 * q ^ 3 + 27 * q ^ 2 - 13 * q - 1

private noncomputable def orderElevenSingularEliminantPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 5 - Polynomial.C 4 * Polynomial.X ^ 4 -
    Polynomial.C 9 * Polynomial.X ^ 3 +
    Polynomial.C 27 * Polynomial.X ^ 2 -
    Polynomial.C 13 * Polynomial.X - Polynomial.C 1

private lemma orderElevenSingularEliminantPolynomial_monic :
    orderElevenSingularEliminantPolynomial.Monic := by
  unfold orderElevenSingularEliminantPolynomial
  monicity!

/-- The eliminant has no rational root.  Since it is monic with constant
coefficient `-1`, the integral-root theorem leaves only `q = ±1`, and direct
evaluation excludes both. -/
theorem orderElevenSingularEliminant_ne_zero (q : ℚ) :
    orderElevenSingularEliminant q ≠ 0 := by
  intro hq
  have hroot :
      Polynomial.aeval q orderElevenSingularEliminantPolynomial = 0 := by
    simpa [Polynomial.aeval_def, orderElevenSingularEliminantPolynomial,
      orderElevenSingularEliminant] using hq
  obtain ⟨z, hz, hdiv⟩ :=
    exists_integer_of_is_root_of_monic
      orderElevenSingularEliminantPolynomial_monic hroot
  have hconstant : orderElevenSingularEliminantPolynomial.coeff 0 = -1 := by
    norm_num [orderElevenSingularEliminantPolynomial]
  rw [hconstant] at hdiv
  have hzunit : IsUnit z :=
    isUnit_iff_dvd_one.mpr (dvd_neg.mp hdiv)
  rcases Int.isUnit_iff.mp hzunit with rfl | rfl
  · norm_num at hz
    norm_num [orderElevenSingularEliminant, hz] at hq
  · norm_num at hz
    norm_num [orderElevenSingularEliminant, hz] at hq

private def orderElevenResultantRawCoefficient (r q : ℚ) : ℚ :=
  q * (q ^ 8 * r - 2 * q ^ 8 - 19 * q ^ 7 * r + 27 * q ^ 7 +
    148 * q ^ 6 * r - 162 * q ^ 6 - 610 * q ^ 5 * r + 587 * q ^ 5 +
    1429 * q ^ 4 * r - 1327 * q ^ 4 - 1884 * q ^ 3 * r + 1774 * q ^ 3 +
    1264 * q ^ 2 * r - 1249 * q ^ 2 - 320 * q * r + 360 * q - 16)

private def orderElevenResultantSingularCoefficient (r q : ℚ) : ℚ :=
  q ^ 9 - 14 * q ^ 8 + 81 * q ^ 7 - q ^ 6 * r - 258 * q ^ 6 +
    11 * q ^ 5 * r + 491 * q ^ 5 - 44 * q ^ 4 * r - 556 * q ^ 4 +
    82 * q ^ 3 * r + 345 * q ^ 3 - 69 * q ^ 2 * r - 93 * q ^ 2 +
    20 * q * r + 3 * q + 1

/-- Checked Bézout certificate for eliminating `r` between the raw modular
equation and the singular-discriminant factor. -/
theorem orderEleven_raw_singular_resultant_identity (r q : ℚ) :
    orderElevenResultantRawCoefficient r q * orderElevenRawPolynomial r q +
        orderElevenResultantSingularCoefficient r q *
          orderElevenSingularFactor r q =
      (q - 1) ^ 7 * orderElevenSingularEliminant q := by
  simp only [orderElevenResultantRawCoefficient,
    orderElevenResultantSingularCoefficient, orderElevenRawPolynomial,
    orderElevenSingularFactor, orderElevenSingularEliminant]
  ring

/-- A raw order-eleven parameter satisfying `q ≠ 1` cannot reconstruct a
singular Tate cubic. -/
theorem orderElevenSingularFactor_ne_zero_of_raw
    {r q : ℚ} (hq1 : q ≠ 1)
    (hraw : orderElevenRawPolynomial r q = 0) :
    orderElevenSingularFactor r q ≠ 0 := by
  intro hsing
  have hzero : (q - 1) ^ 7 * orderElevenSingularEliminant q = 0 := by
    rw [← orderEleven_raw_singular_resultant_identity r q, hraw, hsing]
    ring
  exact (mul_ne_zero (pow_ne_zero 7 (sub_ne_zero.mpr hq1))
    (orderElevenSingularEliminant_ne_zero q)) hzero

/-- Factored discriminant identity for Tate parameters recovered from raw
coordinates. -/
theorem tateNormalDiscriminant_of_raw (r q : ℚ) :
    tateNormalDiscriminant (r * (q * (r - 1))) (q * (r - 1)) =
      (r * (q * (r - 1))) ^ 3 * q * (r - 1) ^ 2 *
        orderElevenSingularFactor r q := by
  simp only [tateNormalDiscriminant, orderElevenSingularFactor]
  ring

private def rawInverseMultiplier (u v : ℚ) : ℚ :=
  u ^ 6 - 3 * u ^ 5 - u ^ 4 * v + 2 * u ^ 4 +
    2 * u ^ 3 * v + u ^ 3 - u ^ 2 * v ^ 2 -
    3 * u ^ 2 * v - 2 * u ^ 2 + u * v ^ 2 +
    2 * u * v + u + v ^ 3 + 2 * v ^ 2 + v

/-- The reverse rational functions satisfy the raw `X₁(11)` equation. -/
theorem orderElevenRawPolynomial_of_model
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    orderElevenRawPolynomial
      (orderElevenRawROfModel u v) (orderElevenRawQOfModel u v) = 0 := by
  have hv1 := model_v_add_one_ne_zero hP hu0 hu1
  have hden := model_u_sq_sub_v_sub_one_ne_zero hP hu0 hu1
  have hcurve : u ^ 3 - u ^ 2 - v ^ 2 - v = 0 := by
    linarith [model_equation hP]
  have hid :
      orderElevenRawPolynomial
          (orderElevenRawROfModel u v) (orderElevenRawQOfModel u v) =
        -(u ^ 3 - u ^ 2 - v ^ 2 - v) * rawInverseMultiplier u v /
          ((v + 1) ^ 3 * (u ^ 2 - v - 1) ^ 2) := by
    simp only [orderElevenRawPolynomial, orderElevenRawROfModel,
      orderElevenRawQOfModel, rawInverseMultiplier]
    field_simp [hv1, hden]
    ring
  rw [hid, hcurve]
  norm_num

/-- The reverse raw functions are a genuine inverse to the forward model map
on the noncusp locus. -/
theorem orderElevenModelOfRaw_inverse
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    orderElevenModelUOfRaw
          (orderElevenRawROfModel u v) (orderElevenRawQOfModel u v) = u ∧
      orderElevenModelVOfRaw
          (orderElevenRawROfModel u v) (orderElevenRawQOfModel u v) = v := by
  let r := orderElevenRawROfModel u v
  let q := orderElevenRawQOfModel u v
  let n := r * q - 2 * r + 1
  let k := q ^ 2 - q - r + 1
  have hv1 := model_v_add_one_ne_zero hP hu0 hu1
  have hv0 := model_v_ne_zero hP hu0 hu1
  have hden := model_u_sq_sub_v_sub_one_ne_zero hP hu0 hu1
  have hcurve : u ^ 3 - u ^ 2 - v ^ 2 - v = 0 := by
    linarith [model_equation hP]
  have hnIdentity :
      n = u * v * (u - 1) / ((v + 1) * (u ^ 2 - v - 1)) := by
    dsimp only [n, r, q, orderElevenRawROfModel, orderElevenRawQOfModel]
    field_simp [hv1, hden]
    linear_combination hcurve
  have hn : n ≠ 0 := by
    rw [hnIdentity]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hu0 hv0) (sub_ne_zero.mpr hu1))
      (mul_ne_zero hv1 hden)
  have hk : k = u * n := by
    have hid : k - u * n =
        (u - 1) * (u ^ 3 - u ^ 2 - v ^ 2 - v) / (v + 1) ^ 2 := by
      dsimp only [k, n, r, q, orderElevenRawROfModel, orderElevenRawQOfModel]
      field_simp [hv1, hden]
      ring
    rw [hcurve] at hid
    norm_num at hid
    linarith
  have hqr : (q - r) * u = (v + 1) * n := by
    have hid : (q - r) * u - (v + 1) * n =
        (u ^ 3 - u ^ 2 - v ^ 2 - v) / (v + 1) := by
      dsimp only [n, r, q, orderElevenRawROfModel, orderElevenRawQOfModel]
      field_simp [hv1, hden]
      ring
    rw [hcurve] at hid
    norm_num at hid
    linarith
  constructor
  · change k / n = u
    exact (div_eq_iff hn).2 hk
  · change (q - r) * k / n ^ 2 - 1 = v
    have hquot : (q - r) * u / n = v + 1 :=
      (div_eq_iff hn).2 hqr
    calc
      (q - r) * k / n ^ 2 - 1 = (q - r) * u / n - 1 := by
        rw [hk]
        field_simp [hn]
      _ = v := by rw [hquot]; ring

/-- A noncusp rational point on the selected `X₁(11)` model yields honest
Tate parameters satisfying every denominator condition and the compact
order-eleven equation. -/
theorem exists_admissible_orderEleven_tateParameters_of_model
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ b c : ℚ,
      b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      orderElevenPolynomial b c = 0 ∧
      tateNormalDiscriminant b c ≠ 0 := by
  let r := orderElevenRawROfModel u v
  let q := orderElevenRawQOfModel u v
  let c := orderElevenCOfModel u v
  let b := orderElevenBOfModel u v
  have hc_eq : c = q * (r - 1) := rfl
  have hb_eq : b = r * c := rfl
  have hr0 : r ≠ 0 := by
    simpa only [r] using orderElevenRawROfModel_ne_zero hP hu0 hu1
  have hr1 : r ≠ 1 := by
    simpa only [r] using orderElevenRawROfModel_ne_one hP hu0 hu1
  have hq0 : q ≠ 0 := by
    simpa only [q] using orderElevenRawQOfModel_ne_zero hP hu0 hu1
  have hq1 : q ≠ 1 := by
    simpa only [q] using orderElevenRawQOfModel_ne_one hP hu0 hu1
  have hraw : orderElevenRawPolynomial r q = 0 := by
    simpa only [r, q] using orderElevenRawPolynomial_of_model hP hu0 hu1
  have hsing : orderElevenSingularFactor r q ≠ 0 :=
    orderElevenSingularFactor_ne_zero_of_raw hq1 hraw
  have hc : c ≠ 0 := by
    rw [hc_eq]
    exact mul_ne_zero hq0 (sub_ne_zero.mpr hr1)
  have hb : b ≠ 0 := by
    rw [hb_eq]
    exact mul_ne_zero hr0 hc
  have hbc : b ≠ c := by
    intro h
    have hzero : c * (r - 1) = 0 := by
      rw [hb_eq] at h
      linear_combination h
    exact (mul_ne_zero hc (sub_ne_zero.mpr hr1)) hzero
  have hAeq : c ^ 2 + c - b = q * (q - 1) * (r - 1) ^ 2 := by
    rw [hb_eq, hc_eq]
    ring
  have hA : c ^ 2 + c - b ≠ 0 := by
    rw [hAeq]
    exact mul_ne_zero (mul_ne_zero hq0 (sub_ne_zero.mpr hq1))
      (pow_ne_zero 2 (sub_ne_zero.mpr hr1))
  have hpolyIdentity :
      orderElevenPolynomial b c =
        q ^ 5 * (r - 1) ^ 8 * orderElevenRawPolynomial r q := by
    simp only [orderElevenPolynomial, orderElevenSixNumerator,
      orderElevenRawPolynomial]
    rw [hb_eq, hc_eq]
    ring
  have hpoly : orderElevenPolynomial b c = 0 := by
    rw [hpolyIdentity, hraw, mul_zero]
  have hdisc : tateNormalDiscriminant b c ≠ 0 := by
    have hid := tateNormalDiscriminant_of_raw r q
    change tateNormalDiscriminant b c =
      b ^ 3 * q * (r - 1) ^ 2 * orderElevenSingularFactor r q at hid
    rw [hid]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hb) hq0)
        (pow_ne_zero 2 (sub_ne_zero.mpr hr1))) hsing
  exact ⟨b, c, hb, hc, hbc, hA, hpoly, hdisc⟩

/-- The compact Tate equation is sufficient: under the exact denominator
conditions used by the checked fifth- and sixth-multiple formulas, the marked
origin has exact additive order eleven. -/
theorem addOrderOf_marked_eq_eleven_of_admissible
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    let h00 := tateNormalCurve_nonsingular_origin b c hb
    addOrderOf
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 11 := by
  let h00 := tateNormalCurve_nonsingular_origin b c hb
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hx : tateSixX b c = tateFiveX b c := by
    rw [tateSixX_eq_orderEleven_reduced b c hb hc hbc hA]
    change
      (b - c) * orderElevenSixNumerator b c / (c ^ 2 + c - b) ^ 2 =
        b * c * (c ^ 2 + c - b) / (b - c) ^ 2
    apply (div_eq_div_iff
      (pow_ne_zero 2 hA)
      (pow_ne_zero 2 (sub_ne_zero.mpr hbc))).2
    simp only [orderElevenPolynomial] at hpoly
    linear_combination hpoly
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hA h00
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff (W := (tateNormalCurve b c).toAffine)).mp hx with
    hsame | hopposite
  · have h65 : (6 : ℕ) • P = (5 : ℕ) • P := by
      exact hsix.trans (hsame.trans hfive.symm)
    have hPzero : P = 0 := by
      apply add_left_cancel (a := (5 : ℕ) • P)
      simpa only [add_zero] using (show (5 : ℕ) • P + P = (5 : ℕ) • P from by
        rw [← show (6 : ℕ) • P = (5 : ℕ) • P + P by abel]
        exact h65)
    exact (WeierstrassCurve.Affine.Point.some_ne_zero h00 hPzero).elim
  · have h65 : (6 : ℕ) • P = -((5 : ℕ) • P) := by
      exact hsix.trans (hopposite.trans (congrArg Neg.neg hfive.symm))
    have heleven : (11 : ℕ) • P = 0 := by
      rw [show (11 : ℕ) • P = (6 : ℕ) • P + (5 : ℕ) • P by abel,
        h65, neg_add_cancel]
    letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    exact addOrderOf_eq_prime heleven
      (WeierstrassCurve.Affine.Point.some_ne_zero h00)

/-- Algebraic intermediate: a noncusp model point produces a Tate normal form
whose marked nonsingular point has exact order eleven. -/
theorem exists_tate_marked_order_eleven_of_model
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ (b c : ℚ)
      (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0),
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11 := by
  obtain ⟨b, c, hb, hc, hbc, hA, hpoly, -⟩ :=
    exists_admissible_orderEleven_tateParameters_of_model hP hu0 hu1
  let h00 := tateNormalCurve_nonsingular_origin b c hb
  exact ⟨b, c, h00,
    addOrderOf_marked_eq_eleven_of_admissible hb hc hbc hA hpoly⟩

/-- End-to-end reverse modular bridge: every noncusp point on the selected
`X₁(11)` model reconstructs an elliptic Tate curve over `ℚ` with a rational
point of exact order eleven. -/
theorem exists_elliptic_tate_marked_order_eleven_of_model
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ (b c : ℚ)
      (_ : (tateNormalCurve b c).IsElliptic)
      (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0),
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11 := by
  obtain ⟨b, c, hb, hc, hbc, hA, hpoly, hdisc⟩ :=
    exists_admissible_orderEleven_tateParameters_of_model hP hu0 hu1
  have hElliptic : (tateNormalCurve b c).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
      tateNormalCurve_discriminant]
    exact hdisc
  let h00 := tateNormalCurve_nonsingular_origin b c hb
  exact ⟨b, c, hElliptic, h00,
    addOrderOf_marked_eq_eleven_of_admissible hb hc hbc hA hpoly⟩

/-- Real downstream consumer for the reverse bridge.  Any uniform theorem
excluding rational points of exact order eleven on elliptic curves forces
every rational point of the affine `X₁(11)` model onto the two finite cusp
abscissae. -/
theorem model_abscissa_eq_zero_or_one_of_no_order_eleven
    (hno : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
      (P : E.toAffine.Point), addOrderOf P ≠ 11)
    {u v : ℚ}
    (hP : MazurTorsion.XOneEleven.curve.toAffine.Nonsingular u v) :
    u = 0 ∨ u = 1 := by
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  by_cases hu1 : u = 1
  · exact Or.inr hu1
  obtain ⟨b, c, hElliptic, h00, horder⟩ :=
    exists_elliptic_tate_marked_order_eleven_of_model hP hu0 hu1
  letI : (tateNormalCurve b c).IsElliptic := hElliptic
  exact (hno (tateNormalCurve b c)
    (WeierstrassCurve.Affine.Point.some 0 0 h00) horder).elim

end MazurTorsion.Kubert
