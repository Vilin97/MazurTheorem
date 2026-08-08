/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalFormMultiples

/-!
# Rational points of order twenty-five

An exact order-25 point is put in Tate normal form.  The checked rational
recurrence computes `12P` and `13P`, with every nonzero secant denominator
deduced from exact order.  Since `13P = -12P`, their abscissas agree.  This
gives an explicit rational-function equation on `X₁(25)` while preserving the
discriminant scaling from the original elliptic curve.

This is a forward reduction, not yet the Diophantine exclusion of all
noncuspidal rational points on the resulting curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The rational-function equation obtained by comparing `12P` and `13P` in
the denominator-checked Tate recurrence. -/
def orderTwentyFiveRecurrenceEquation (b c : ℚ) : ℚ :=
  tateSuccessiveX b c 11 - tateSuccessiveX b c 10

private theorem nsmul_ne_zero_of_marked_order_twentyFive
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 25) (n : ℕ) (hn : 0 < n) (hn25 : n < 25) :
    n • P ≠ 0 := by
  intro hnsmul
  have hdvd : 25 ∣ n := by
    rw [← horder]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hnsmul
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- Exact order 25 makes every abscissa used to compute through `13P`
nonzero.  These are precisely the secant denominators of the recurrence. -/
theorem tateSuccessiveX_ne_zero_of_marked_order_twentyFive
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    ∀ n ≤ 10, tateSuccessiveX b c n ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      have hprevious : ∀ k < n, tateSuccessiveX b c k ≠ 0 := by
        intro k hk
        exact ih k hk (by omega)
      obtain ⟨hpoint, hcoord⟩ :=
        nsmul_origin_eq_successiveCoordinates b c hb h00 n hprevious
      intro hx
      rcases (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := W.toAffine) (y₁ := tateSuccessiveY b c n) (y₂ := 0)
        (h₁ := hpoint) (h₂ := h00)).mp hx with heq | hneg
      · have hsmall : (n + 1) • P ≠ 0 :=
          nsmul_ne_zero_of_marked_order_twentyFive P horder (n + 1)
            (by omega) (by omega)
        apply hsmall
        have hcancel : (n + 1) • P + P = 0 + P := by
          calc
            (n + 1) • P + P = (n + 2) • P := by
              rw [show n + 2 = (n + 1) + 1 by omega]
              simpa only [one_nsmul] using
                (add_nsmul P (n + 1) 1).symm
            _ = WeierstrassCurve.Affine.Point.some
                (tateSuccessiveX b c n) (tateSuccessiveY b c n) hpoint :=
              hcoord
            _ = P := by simpa [P] using heq
            _ = 0 + P := (zero_add P).symm
        exact add_right_cancel hcancel
      · have hsmall : (n + 3) • P ≠ 0 :=
          nsmul_ne_zero_of_marked_order_twentyFive P horder (n + 3)
            (by omega) (by omega)
        apply hsmall
        rw [show (n + 3) • P = (n + 2) • P + P by
          rw [show n + 3 = (n + 2) + 1 by omega, add_nsmul, one_nsmul]]
        rw [hcoord, hneg, neg_add_cancel]

/-- Exact order 25 of the marked Tate point forces the checked `12P/13P`
rational-function equation. -/
theorem orderTwentyFiveRecurrenceEquation_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveRecurrenceEquation b c = 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hx :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive
      b c hb h00 horder
  obtain ⟨h₁₂, htwelve⟩ :=
    nsmul_origin_eq_successiveCoordinates b c hb h00 10
      (fun k hk => hx k (by omega))
  obtain ⟨h₁₃, hthirteen⟩ :=
    nsmul_origin_eq_successiveCoordinates b c hb h00 11
      (fun k hk => hx k (by omega))
  have htwentyFive : (25 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hopposite : (13 : ℕ) • P = -((12 : ℕ) • P) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← htwentyFive]
    abel
  rw [hthirteen, htwelve,
    WeierstrassCurve.Affine.Point.neg_some] at hopposite
  have hxEqual :
      tateSuccessiveX b c 11 = tateSuccessiveX b c 10 :=
    (WeierstrassCurve.Affine.Point.some.injEq
      (tateSuccessiveX b c 11) (tateSuccessiveY b c 11) h₁₃
      (tateSuccessiveX b c 10)
      (W.toAffine.negY
        (tateSuccessiveX b c 10) (tateSuccessiveY b c 10)) _).mp
      hopposite |>.1
  simp only [orderTwentyFiveRecurrenceEquation]
  exact sub_eq_zero.mpr hxEqual

/-- A rational point of exact order 25 supplies a denominator-checked point
on the explicit Tate recurrence locus, retaining the twelfth-power
discriminant scale of the original curve. -/
theorem exists_tateOrderTwentyFive_recurrence_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 25) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧
      (∀ n ≤ 10, tateSuccessiveX b c n ≠ 0) ∧
      orderTwentyFiveRecurrenceEquation b c = 0 ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hP2 : P + P ≠ 0 := by
    intro h
    have hdvd : addOrderOf P ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hP] at hdvd
    norm_num at hdvd
  have hP3 : P + P + P ≠ 0 := by
    intro h
    have hdvd : addOrderOf P ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • P = P + P + P by abel]
        exact h)
    rw [hP] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heP, hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) P hP2 hP3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact hP
  have hequation :=
    orderTwentyFiveRecurrenceEquation_eq_zero_of_marked_order
      b c hb h00 hmarked
  have hdenominators :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive
      b c hb h00 hmarked
  refine ⟨b, c, u, hu, hb, hdenominators, hequation, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rwa [← hbase]

end MazurTorsion.Kubert
