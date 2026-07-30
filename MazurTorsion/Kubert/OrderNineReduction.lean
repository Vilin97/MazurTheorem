/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalFormMultiples

/-!
# Reduction of a point of order nine

If the marked point `P = (0, 0)` on Tate normal form has exact order nine,
then `5P = -4P`.  Comparing the already checked fourth- and fifth-multiple
abscissas and clearing only the proved-nonzero denominators gives

`c⁵ + c⁴ + (1-b)c³ - 3bc² + 3b²c - b³ = 0`.

This is the common Tate-parameter certificate used by the order-eighteen
and order-twenty-seven branches.  No rational-point classification of the
resulting parameter curve is asserted here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The Tate-parameter equation forced by exact order nine of the marked
point. -/
def orderNinePolynomial (b c : ℚ) : ℚ :=
  c ^ 5 + c ^ 4 + (1 - b) * c ^ 3 -
    3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3

lemma c_ne_zero_of_marked_order_nine
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9) :
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
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates b 0 hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some 0 (b - 0) h₃ = -P := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp)
      (by
        simp [W, tateNormalCurve,
          WeierstrassCurve.Affine.negY])
  apply hfourNe
  rw [show (4 : ℕ) • P = (3 : ℕ) • P + P by abel]
  rw [hthree, hneg, neg_add_cancel]

lemma parameters_ne_of_marked_order_nine
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9) :
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
  rw [show (5 : ℕ) • P = (2 : ℕ) • P + (3 : ℕ) • P by abel]
  rw [htwo, hthree, hneg, neg_add_cancel]

/-- Exact order nine of the marked Tate point forces
`orderNinePolynomial b c = 0`. -/
theorem orderNinePolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9) :
    orderNinePolynomial b c = 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc :=
    c_ne_zero_of_marked_order_nine b c hb h00 horder
  have hbc :=
    parameters_ne_of_marked_order_nine b c hb h00 horder
  obtain ⟨h₄, hfour⟩ :=
    four_mul_origin_coordinates b c hb hc h00
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hfour' :
      (4 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2)
          (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [show (4 : ℕ) • P = P + P + P + P by abel]
    exact hfour
  have hsum : (5 : ℕ) • P = -((4 : ℕ) • P) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← add_nsmul]
    norm_num
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  rw [hfive, hfour',
    WeierstrassCurve.Affine.Point.neg_some] at hsum
  have hx :
      tateFiveX b c = b * (b - c) / c ^ 2 := by
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hsum
    exact hsum.1
  simp only [tateFiveX] at hx
  field_simp [hc, sub_ne_zero.mpr hbc] at hx
  simp only [orderNinePolynomial]
  linear_combination hx

/-- A rational point of exact order nine produces a denominator-safe point
on the explicit Tate-parameter curve, retaining the twelfth-power
discriminant scale of the original curve. -/
theorem exists_tateOrderNine_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 9) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      orderNinePolynomial b c = 0 ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
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
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc :=
    c_ne_zero_of_marked_order_nine b c hb h00 hmarked
  have hbc :=
    parameters_ne_of_marked_order_nine b c hb h00 hmarked
  have hpoly :=
    orderNinePolynomial_eq_zero_of_marked_order
      b c hb h00 hmarked
  refine ⟨b, c, u, hu, hb, hc, hbc, hpoly, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rwa [← hbase]

end MazurTorsion.Kubert
