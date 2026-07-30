/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.NaiveHeightDescent
import MazurTorsion.Kubert.OrderNineReduction

/-!
# Reduction of a point of order eighteen

If `Q` has exact order eighteen, then `2Q` has exact order nine and `9Q`
has exact order two.  Normalize the order-nine point to the marked point on
Tate normal form.  The first fact gives `orderNinePolynomial b c = 0`;
the transported order-two point supplies a rational root of the explicit
two-division cubic.

This is the denominator-safe common entry to the usual genus-two model for
`X₁(18)`.  The elimination and rational-point classification are kept as a
separate boundary.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The duplication denominator on Tate normal form. Its rational roots are
the abscissas of the nonzero rational points killed by two. -/
def tateTwoDivisionPolynomial (b c r : ℚ) : ℚ :=
  4 * r ^ 3 + ((1 - c) ^ 2 - 4 * b) * r ^ 2 +
    2 * b * (c - 1) * r + b ^ 2

private lemma tateTwoDivisionPolynomial_eq_zero_of_order_two
    (b c r s : ℚ)
    (hrs : (tateNormalCurve b c).toAffine.Nonsingular r s)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some r s hrs :
          (tateNormalCurve b c).toAffine.Point) = 2) :
    tateTwoDivisionPolynomial b c r = 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some r s hrs
  have hdouble : P + P = 0 := by
    rw [← two_nsmul, ← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hvertical : s = W.toAffine.negY r s := by
    by_contra hne
    have hnonzero : P + P ≠ 0 := by
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    exact hnonzero hdouble
  have hden :=
    (WeierstrassCurve.Affine.den_duplication_eq_zero_iff hrs.1).mpr
      hvertical
  simp only [tateNormalCurve, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hden
  simp only [tateTwoDivisionPolynomial]
  linear_combination hden

/-- A rational point of exact order eighteen produces simultaneous
order-nine and rational-two-torsion equations on one Tate normal form,
with the original discriminant scale retained. -/
theorem exists_tateOrderEighteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 18) :
    ∃ b c u r : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      orderNinePolynomial b c = 0 ∧
      tateTwoDivisionPolynomial b c r = 0 ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  let R : (E⁄ℚ).Point := (2 : ℕ) • Q
  let T : (E⁄ℚ).Point := (9 : ℕ) • Q
  have hRorder : addOrderOf R = 9 := by
    dsimp [R]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hTorder : addOrderOf T = 2 := by
    dsimp [T]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hR2 : R + R ≠ 0 := by
    intro h
    have hdvd : addOrderOf R ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hRorder] at hdvd
    norm_num at hdvd
  have hR3 : R + R + R ≠ 0 := by
    intro h
    have hdvd : addOrderOf R ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • R = R + R + R by abel]
        exact h)
    rw [hRorder] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heR, hdisc⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) R hR2 hR3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9 := by
    rw [← heR, AddEquiv.addOrderOf_eq]
    exact hRorder
  have hc :=
    c_ne_zero_of_marked_order_nine b c hb h00 hmarked
  have hbc :=
    parameters_ne_of_marked_order_nine b c hb h00 hmarked
  have hnine :=
    orderNinePolynomial_eq_zero_of_marked_order
      b c hb h00 hmarked
  have hTmarked : addOrderOf (e T) = 2 := by
    rw [AddEquiv.addOrderOf_eq]
    exact hTorder
  cases hTcase : e T with
  | zero =>
      rw [hTcase] at hTmarked
      change
        addOrderOf
          (0 : (tateNormalCurve b c).toAffine.Point) = 2
        at hTmarked
      rw [addOrderOf_zero] at hTmarked
      omega
  | some r s hrs =>
      have htwo :
          tateTwoDivisionPolynomial b c r = 0 :=
        tateTwoDivisionPolynomial_eq_zero_of_order_two
          b c r s hrs (by simpa [hTcase] using hTmarked)
      refine ⟨b, c, u, r, hu, hb, hc, hbc, hnine, htwo, ?_⟩
      have hbase : (E⁄ℚ).Δ = E.Δ := by
        simp [WeierstrassCurve.baseChange]
      rwa [← hbase]

end MazurTorsion.Kubert
