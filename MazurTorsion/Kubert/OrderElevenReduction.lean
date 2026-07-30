/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFifteenReduction

/-!
# Reduction of a point of order eleven

Let `P = (0, 0)` on the Tate normal form

`y² + (1-c)xy - by = x³ - bx²`.

The checked addition recurrence gives explicit coordinates for `5P` and
`6P`.  If `P` has exact order eleven, then `6P = -5P`, so their
`X`-coordinates agree.  Put

* `A = c² + c - b`,
* `B = b² - bc - c³`, and
* `d = b-c`.

Clearing only the already proved nonzero denominators gives the compact
parameter equation

`d³ B - bc A³ = 0`.

This file proves the exact-order reduction and retains all factors needed
by the birational model map.  It does not classify the rational points of
the parameter curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The numerator in the denominator-safe formula for `x(6P)`. -/
def orderElevenSixNumerator (b c : ℚ) : ℚ :=
  b ^ 2 - b * c - c ^ 3

/-- The compact Tate-parameter equation for exact order eleven. -/
def orderElevenPolynomial (b c : ℚ) : ℚ :=
  let A := c ^ 2 + c - b
  let B := orderElevenSixNumerator b c
  let d := b - c
  d ^ 3 * B - b * c * A ^ 3

private lemma orderEleven_tateFiveRatio_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) :
    tateFiveY b c / tateFiveX b c =
      c * orderElevenSixNumerator b c /
        ((b - c) * (c ^ 2 + c - b)) := by
  simp only [tateFiveX, tateFiveY, orderElevenSixNumerator]
  field_simp [hb, hc, sub_ne_zero.mpr hbc]

/-- Denominator-safe reduced formula for the abscissa of `6P`. -/
lemma tateSixX_eq_orderEleven_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0) :
    tateSixX b c =
      (b - c) * orderElevenSixNumerator b c /
        (c ^ 2 + c - b) ^ 2 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := orderElevenSixNumerator b c
  let d : ℚ := b - c
  have hA' : A ≠ 0 := by
    simpa only [A] using hA
  have hd : d ≠ 0 := by
    simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateFiveY b c / tateFiveX b c =
        c * B / (d * A) := by
    simpa only [A, B, d] using
      orderEleven_tateFiveRatio_eq b c hb hc hbc
  have hxfive :
      tateFiveX b c = b * c * A / d ^ 2 := by
    simp only [tateFiveX, A, d]
  change
    tateNextX b c (tateFiveX b c) (tateFiveY b c) =
      d * B / A ^ 2
  simp only [tateNextX]
  rw [hratio, hxfive]
  field_simp [hA', hd]
  dsimp only [A, B, d, orderElevenSixNumerator]
  ring

private lemma cross_multiply_orderEleven_abscissae
    {A B d R : ℚ} (hA : A ≠ 0) (hd : d ≠ 0)
    (h :
      d * B / A ^ 2 = R * A / d ^ 2) :
    d ^ 3 * B - R * A ^ 3 = 0 := by
  field_simp [hA, hd] at h
  linear_combination h

private theorem nsmul_ne_zero_of_marked_order_eleven
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 11) (n : ℕ)
    (hndvd : ¬11 ∣ n) :
    n • P ≠ 0 := by
  intro hn
  apply hndvd
  rw [← horder]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn

private lemma c_ne_zero_of_marked_order_eleven
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11) :
    c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_eleven P horder 4
      (by norm_num)
  intro hc
  subst c
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates b 0 hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some 0 (b - 0) h₃ =
        -P := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp)
      (by
        simp [W, tateNormalCurve,
          WeierstrassCurve.Affine.negY])
  apply hfourNe
  rw [show (4 : ℕ) • P = (3 : ℕ) • P + P by abel]
  rw [hthree, hneg, neg_add_cancel]

private lemma parameters_ne_of_marked_order_eleven
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11) :
    b ≠ c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_eleven P horder 5
      (by norm_num)
  intro hbc
  subst c
  obtain ⟨h₂, htwo⟩ :=
    two_nsmul_origin_coordinates b b hb h00
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates b b hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some b (b * b) h₂ =
        -WeierstrassCurve.Affine.Point.some b (b - b) h₃ := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp)
      (by
        simp [tateNormalCurve,
          WeierstrassCurve.Affine.negY]
        ring)
  apply hfiveNe
  rw [show (5 : ℕ) • P =
      (2 : ℕ) • P + (3 : ℕ) • P by abel]
  rw [htwo, hthree, hneg, neg_add_cancel]

private lemma five_numerator_ne_of_marked_order_eleven
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11) :
    c ^ 2 + c - b ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_eleven P horder 4
      (by norm_num)
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_eleven P horder 6
      (by norm_num)
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  intro hA
  have hxfive : tateFiveX b c = 0 := by
    simp [tateFiveX, hA]
  rcases
      (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxfive with
    heq | hneg
  · apply hfourNe
    have hfiveEq : (5 : ℕ) • P = P :=
      hfive.trans heq
    have hcancel : (4 : ℕ) • P + P = 0 + P := by
      rw [← show (5 : ℕ) • P = (4 : ℕ) • P + P by
        abel]
      exact hfiveEq.trans (zero_add P).symm
    exact add_right_cancel hcancel
  · apply hsixNe
    rw [show (6 : ℕ) • P = (5 : ℕ) • P + P by abel]
    rw [hfive, hneg, neg_add_cancel]

/-- Exact order eleven of the marked Tate point forces the compact
parameter polynomial to vanish. -/
theorem orderElevenPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11) :
    orderElevenPolynomial b c = 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc :=
    c_ne_zero_of_marked_order_eleven b c hb h00 horder
  have hbc :=
    parameters_ne_of_marked_order_eleven b c hb h00 horder
  have hA :=
    five_numerator_ne_of_marked_order_eleven
      b c hb hc hbc h00 horder
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hA h00
  have heleven : (11 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hsum :
      (6 : ℕ) • P + (5 : ℕ) • P = 0 := by
    rw [show (6 : ℕ) • P + (5 : ℕ) • P =
      (11 : ℕ) • P by abel]
    exact heleven
  have hopposite :
      WeierstrassCurve.Affine.Point.some
          (tateSixX b c) (tateSixY b c) h₆ =
        -WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) h₅ := by
    rw [← hsix, ← hfive]
    exact eq_neg_of_add_eq_zero_left hsum
  rw [WeierstrassCurve.Affine.Point.neg_some] at hopposite
  have hx : tateSixX b c = tateFiveX b c :=
    (WeierstrassCurve.Affine.Point.some.injEq
      (tateSixX b c) (tateSixY b c) h₆
      (tateFiveX b c)
      ((tateNormalCurve b c).toAffine.negY
        (tateFiveX b c) (tateFiveY b c)) _).mp
      hopposite |>.1
  rw [tateSixX_eq_orderEleven_reduced
      b c hb hc hbc hA, tateFiveX] at hx
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := orderElevenSixNumerator b c
  let d : ℚ := b - c
  have hA' : A ≠ 0 := by
    simpa only [A] using hA
  have hd : d ≠ 0 := by
    simpa only [d] using sub_ne_zero.mpr hbc
  have hx' :
      d * B / A ^ 2 = b * c * A / d ^ 2 := by
    simpa only [A, B, d] using hx
  have hcross :=
    cross_multiply_orderEleven_abscissae
      hA' hd hx'
  simpa only [orderElevenPolynomial, A, B, d] using hcross

/-- On an admissible solution of the compact equation, the numerator of
`x(6P)` is also nonzero. -/
theorem orderElevenSixNumerator_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderElevenPolynomial b c = 0) :
    orderElevenSixNumerator b c ≠ 0 := by
  intro hB
  have hnonzero :
      b * c * (c ^ 2 + c - b) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hb hc) (pow_ne_zero 3 hA)
  apply hnonzero
  simp only [orderElevenPolynomial, hB, mul_zero] at hpoly
  linear_combination -hpoly

/-- A rational point of exact order eleven produces an admissible point
on the explicit Tate-parameter curve, with the discriminant scale
retained. -/
theorem exists_tateOrderEleven_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 11) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      orderElevenSixNumerator b c ≠ 0 ∧
      orderElevenPolynomial b c = 0 ∧
      u ^ 12 * E.Δ = tateNormalDiscriminant b c := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs
      (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  have hQ3 : Q + Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • Q = Q + Q + Q by abel]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 11 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc :=
    c_ne_zero_of_marked_order_eleven b c hb h00 hmarked
  have hbc :=
    parameters_ne_of_marked_order_eleven b c hb h00 hmarked
  have hA :=
    five_numerator_ne_of_marked_order_eleven
      b c hb hc hbc h00 hmarked
  have hpoly :=
    orderElevenPolynomial_eq_zero_of_marked_order
      b c hb h00 hmarked
  have hB :=
    orderElevenSixNumerator_ne_zero hb hc hA hpoly
  refine
    ⟨b, c, u, hu, hb, hc, hbc, hA, hB, hpoly, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rw [← hbase, hdisc, tateNormalCurve_discriminant]

end MazurTorsion.Kubert
