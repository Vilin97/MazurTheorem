/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.ThreeTorsion
import MazurTorsion.Kubert.TateNormalFormMultiples

/-!
# Reduction of a point of order fifteen

An exact rational point of order `15` can be put in Tate normal form. Its fifth multiple then
has exact order `3`, so the `X`-coordinate of that multiple is a root of the third division
polynomial. Clearing the two honest Tate denominators produces the polynomial
`orderFifteenPolynomial` below.

This file proves only the forward modular reduction. In particular, it makes no assertion about
the rational points of the resulting affine parameter curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- A compact polynomial equation for the Tate-parameter image of `X₁(15)`.

Writing `A = c² + c - b` and `d = b - c`, this is the third division polynomial
at `x(5P) = bcA/d²`, after multiplication by `d⁸` and removal of the nonzero factor `b³`. -/
def orderFifteenPolynomial (b c : ℚ) : ℚ :=
  let A := c ^ 2 + c - b
  let d := b - c
  3 * b * (c * A) ^ 4 +
    ((1 - c) ^ 2 - 4 * b) * (c * A) ^ 3 * d ^ 2 +
    3 * (c - 1) * (c * A) ^ 2 * d ^ 4 +
    3 * (c * A) * d ^ 6 -
    d ^ 8

/-- The discriminant of the two-parameter Tate normal form, in a factored presentation useful
for retaining the twelfth-power scale supplied by Tate normalization. -/
def tateNormalDiscriminant (b c : ℚ) : ℚ :=
  b ^ 3 *
    (16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b +
      c ^ 4 - 3 * c ^ 3 + 3 * c ^ 2 - c)

lemma tateNormalCurve_discriminant (b c : ℚ) :
    (tateNormalCurve b c).Δ = tateNormalDiscriminant b c := by
  simp only [tateNormalCurve, tateNormalDiscriminant, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma c_ne_zero_of_marked_order_fifteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15) :
    c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    have hdvd : addOrderOf P ∣ 4 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hfour
    rw [horder] at hdvd
    norm_num at hdvd
  intro hc
  subst c
  obtain ⟨h₃, hthree⟩ := three_nsmul_origin_coordinates b 0 hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some 0 (b - 0) h₃ = -P := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp) (by simp [W, tateNormalCurve, WeierstrassCurve.Affine.negY])
  apply hfourNe
  rw [show (4 : ℕ) • P = (3 : ℕ) • P + P by abel]
  rw [hthree, hneg, neg_add_cancel]

private lemma parameters_ne_of_marked_order_fifteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15) :
    b ≠ c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 := by
    intro hfive
    have hdvd : addOrderOf P ∣ 5 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hfive
    rw [horder] at hdvd
    norm_num at hdvd
  intro hbc
  subst c
  obtain ⟨h₂, htwo⟩ := two_nsmul_origin_coordinates b b hb h00
  obtain ⟨h₃, hthree⟩ := three_nsmul_origin_coordinates b b hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some b (b * b) h₂ =
        -WeierstrassCurve.Affine.Point.some b (b - b) h₃ := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp) (by simp [tateNormalCurve, WeierstrassCurve.Affine.negY]; ring)
  apply hfiveNe
  rw [show (5 : ℕ) • P = (2 : ℕ) • P + (3 : ℕ) • P by abel]
  rw [htwo, hthree, hneg, neg_add_cancel]

private lemma orderFifteenPolynomial_eq_zero_of_three_division
    (b c : ℚ) (hb : b ≠ 0) (hbc : b ≠ c)
    (hψ :
      Polynomial.eval (tateFiveX b c)
        (tateNormalCurve b c).toAffine.Ψ₃ = 0) :
    orderFifteenPolynomial b c = 0 := by
  simp only [tateFiveX, tateNormalCurve, WeierstrassCurve.Ψ₃,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at hψ
  field_simp [sub_ne_zero.mpr hbc] at hψ
  have hscaled :
      b ^ 3 * orderFifteenPolynomial b c = 0 := by
    simp only [orderFifteenPolynomial]
    ring_nf at hψ ⊢
    exact hψ
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hb)

/-- Exact order `15` of the marked Tate point forces the compact parameter polynomial to vanish.
The proof records the fifth multiple explicitly and uses its exact order `3`. -/
theorem orderFifteenPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15) :
    orderFifteenPolynomial b c = 0 := by
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc := c_ne_zero_of_marked_order_fifteen b c hb h00 horder
  have hbc := parameters_ne_of_marked_order_fifteen b c hb h00 horder
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hfiveOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) h₅) = 3 := by
    rw [← hfive]
    change addOrderOf ((5 : ℕ) • P) = 3
    rw [addOrderOf_nsmul' P (by norm_num), horder]
    norm_num
  have hthree :
      (3 : ℕ) •
          WeierstrassCurve.Affine.Point.some
            (tateFiveX b c) (tateFiveY b c) h₅ = 0 := by
    rw [← hfiveOrder]
    exact addOrderOf_nsmul_eq_zero _
  exact orderFifteenPolynomial_eq_zero_of_three_division b c hb hbc <|
    (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
      (tateNormalCurve b c).toAffine h₅).mp hthree

/-- A rational point of exact order `15` produces a point on the explicit Tate-parameter
curve, with every denominator condition and the original discriminant scale retained.

The additional condition `c²+c-b ≠ 0` follows from the displayed polynomial and `b-c ≠ 0`;
it is useful when continuing the checked multiple recurrence from `5P` to `6P`. -/
theorem exists_tateOrderFifteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 15) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      orderFifteenPolynomial b c = 0 ∧
      u ^ 12 * E.Δ = tateNormalDiscriminant b c := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
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
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc := c_ne_zero_of_marked_order_fifteen b c hb h00 hmarked
  have hbc := parameters_ne_of_marked_order_fifteen b c hb h00 hmarked
  have hpoly :=
    orderFifteenPolynomial_eq_zero_of_marked_order b c hb h00 hmarked
  have hnumerator : c ^ 2 + c - b ≠ 0 := by
    intro hzero
    have hd : b - c ≠ 0 := sub_ne_zero.mpr hbc
    have hpow : -(b - c) ^ 8 = 0 := by
      simpa [orderFifteenPolynomial, hzero] using hpoly
    exact pow_ne_zero 8 hd (neg_eq_zero.mp hpow)
  refine ⟨b, c, u, hu, hb, hc, hbc, hnumerator, hpoly, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rw [← hbase, hdisc, tateNormalCurve_discriminant]

end MazurTorsion.Kubert
