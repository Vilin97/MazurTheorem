/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFourteenReduction

/-!
# Reduction of a point of order thirteen

Let `P = (0, 0)` be the marked point on the Tate normal form

`y² + (1-c)xy - by = x³ - bx²`.

If `P` has exact order `13`, then `7P = -6P`; in particular, the two points have the
same `X`-coordinate.  The checked formulas for `6P` and `7P` turn this equality into

`(b-c) B³ + bc A³ C = 0`,

where

* `A = c² + c - b`,
* `B = b² - bc - c³`, and
* `C = 2b² - bc² - 3bc + c²`.

All factors used as denominators are proved nonzero from exact order, rather than
discarded during simplification.

The substitutions

`r = b/c`, `s = c²/(b-c)`

then give the affine plane model

`r³ + (-s⁴ + 5s³ - 9s² + 4s - 2)r²
    + (-s³ + 6s² - 3s + 1)r - s³ = 0`.

This file proves the forward reduction only.  It does not classify the rational
points of this genus-two modular curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The denominator-safe Tate-parameter polynomial forced by exact order `13`.

It is obtained by equating the checked `X`-coordinates of `6P` and `7P`. -/
def orderThirteenPolynomial (b c : ℚ) : ℚ :=
  let A := c ^ 2 + c - b
  let B := tateSixNumerator b c
  let C := tateSevenAux b c
  (b - c) * B ^ 3 + b * c * A ^ 3 * C

/-- The reduced affine `X₁(13)` polynomial in the coordinates
`r = b/c` and `s = c²/(b-c)`. -/
def orderThirteenReducedPolynomial (r s : ℚ) : ℚ :=
  r ^ 3 +
    (-s ^ 4 + 5 * s ^ 3 - 9 * s ^ 2 + 4 * s - 2) * r ^ 2 +
    (-s ^ 3 + 6 * s ^ 2 - 3 * s + 1) * r -
    s ^ 3

private theorem nsmul_ne_zero_of_marked_order_thirteen
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 13) (n : ℕ) (hndvd : ¬13 ∣ n) :
    n • P ≠ 0 := by
  intro hn
  apply hndvd
  rw [← horder]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn

private lemma c_ne_zero_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 4 (by norm_num)
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

private lemma parameters_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    b ≠ c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 5 (by norm_num)
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

private lemma five_numerator_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    c ^ 2 + c - b ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 4 (by norm_num)
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 6 (by norm_num)
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  intro hA
  have hxfive : tateFiveX b c = 0 := by
    simp [tateFiveX, hA]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxfive with heq | hneg
  · apply hfourNe
    have hfiveEq : (5 : ℕ) • P = P :=
      hfive.trans heq
    have hcancel : (4 : ℕ) • P + P = 0 + P := by
      rw [← show (5 : ℕ) • P = (4 : ℕ) • P + P by abel]
      exact hfiveEq.trans (zero_add P).symm
    exact add_right_cancel hcancel
  · apply hsixNe
    rw [show (6 : ℕ) • P = (5 : ℕ) • P + P by abel]
    rw [hfive, hneg, neg_add_cancel]

private lemma six_numerator_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    tateSixNumerator b c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 5 (by norm_num)
  have hsevenNe : (7 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 7 (by norm_num)
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hfiveNumerator h00
  intro hB
  have hxsix : tateSixX b c = 0 := by
    rw [tateSixX_eq_reduced b c hb hc hbc hfiveNumerator]
    simp [hB]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxsix with heq | hneg
  · apply hfiveNe
    have hsixEq : (6 : ℕ) • P = P :=
      hsix.trans heq
    have hcancel : (5 : ℕ) • P + P = 0 + P := by
      rw [← show (6 : ℕ) • P = (5 : ℕ) • P + P by abel]
      exact hsixEq.trans (zero_add P).symm
    exact add_right_cancel hcancel
  · apply hsevenNe
    rw [show (7 : ℕ) • P = (6 : ℕ) • P + P by abel]
    rw [hsix, hneg, neg_add_cancel]

private lemma seven_aux_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    tateSevenAux b c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 6 (by norm_num)
  have heightNe : (8 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 8 (by norm_num)
  obtain ⟨h₇, hseven⟩ :=
    seven_nsmul_origin_coordinates b c hb hc hbc
      hfiveNumerator hsixNumerator h00
  have hxseven : tateSevenX b c ≠ 0 := by
    intro hx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hx with heq | hneg
    · apply hsixNe
      have hsevenEq : (7 : ℕ) • P = P :=
        hseven.trans heq
      have hcancel : (6 : ℕ) • P + P = 0 + P := by
        rw [← show (7 : ℕ) • P = (6 : ℕ) • P + P by abel]
        exact hsevenEq.trans (zero_add P).symm
      exact add_right_cancel hcancel
    · apply heightNe
      rw [show (8 : ℕ) • P = (7 : ℕ) • P + P by abel]
      rw [hseven, hneg, neg_add_cancel]
  intro hC
  apply hxseven
  rw [tateSevenX_eq_reduced b c hb hc hbc
    hfiveNumerator hsixNumerator]
  simp [hC]

private lemma orderThirteenPolynomial_eq_zero_of_opposite_multiples
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h₆ : (tateNormalCurve b c).toAffine.Nonsingular
      (tateSixX b c) (tateSixY b c))
    (h₇ : (tateNormalCurve b c).toAffine.Nonsingular
      (tateSevenX b c) (tateSevenY b c))
    (hopposite :
      WeierstrassCurve.Affine.Point.some
          (tateSevenX b c) (tateSevenY b c) h₇ =
        -WeierstrassCurve.Affine.Point.some
          (tateSixX b c) (tateSixY b c) h₆) :
    orderThirteenPolynomial b c = 0 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hB : B ≠ 0 := by simpa only [B] using hsixNumerator
  rw [WeierstrassCurve.Affine.Point.neg_some] at hopposite
  have hx :
      tateSevenX b c = tateSixX b c :=
    (WeierstrassCurve.Affine.Point.some.injEq
      (tateSevenX b c) (tateSevenY b c) h₇
      (tateSixX b c)
      ((tateNormalCurve b c).toAffine.negY
        (tateSixX b c) (tateSixY b c)) _).mp hopposite |>.1
  rw [tateSevenX_eq_reduced b c hb hc hbc
      hfiveNumerator hsixNumerator,
    tateSixX_eq_reduced b c hb hc hbc hfiveNumerator] at hx
  change -b * c * A * C / B ^ 2 = (b - c) * B / A ^ 2 at hx
  have hscaled :
      (b - c) * B ^ 3 + b * c * A ^ 3 * C = 0 := by
    field_simp [hA, hB] at hx
    linear_combination -hx
  simpa only [orderThirteenPolynomial, A, B, C] using hscaled

/-- Exact order `13` of the marked Tate point forces the denominator-safe
`X₁(13)` parameter polynomial to vanish. -/
theorem orderThirteenPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    orderThirteenPolynomial b c = 0 := by
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc := c_ne_zero_of_marked_order_thirteen b c hb h00 horder
  have hbc := parameters_ne_of_marked_order_thirteen b c hb h00 horder
  have hA :=
    five_numerator_ne_of_marked_order_thirteen b c hb hc hbc h00 horder
  have hB :=
    six_numerator_ne_of_marked_order_thirteen b c hb hc hbc hA h00 horder
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hA h00
  obtain ⟨h₇, hseven⟩ :=
    seven_nsmul_origin_coordinates b c hb hc hbc hA hB h00
  have hthirteen : (13 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hsum : (7 : ℕ) • P + (6 : ℕ) • P = 0 := by
    rw [← hthirteen]
    abel
  have hopposite : (7 : ℕ) • P = -((6 : ℕ) • P) :=
    eq_neg_of_add_eq_zero_left hsum
  rw [hsix, hseven] at hopposite
  exact orderThirteenPolynomial_eq_zero_of_opposite_multiples
    b c hb hc hbc hA hB h₆ h₇ hopposite

/-- Substituting `b = rs(r-1)` and `c = s(r-1)` factors the Tate polynomial as
`s⁷(r-1)¹¹` times the reduced polynomial. -/
lemma orderThirteenPolynomial_substitution (r s : ℚ) :
    orderThirteenPolynomial (r * s * (r - 1)) (s * (r - 1)) =
      s ^ 7 * (r - 1) ^ 11 * orderThirteenReducedPolynomial r s := by
  simp only [orderThirteenPolynomial, orderThirteenReducedPolynomial,
    tateSixNumerator, tateSevenAux]
  ring

/-- The forward rational change of variables from the Tate certificate to the
reduced affine model, including the inverse identities needed to justify the
substitution and the inherited noncuspidal conditions. -/
theorem exists_orderThirteen_reduced_certificate
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0)
    (hB : tateSixNumerator b c ≠ 0)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderThirteenPolynomial b c = 0) :
    ∃ r s : ℚ,
      r = b / c ∧ s = c ^ 2 / (b - c) ∧
      r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ s ∧
      r * s - 2 * r + 1 ≠ 0 ∧
      b = r * s * (r - 1) ∧ c = s * (r - 1) ∧
      orderThirteenReducedPolynomial r s = 0 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hrzero : r ≠ 0 := div_ne_zero hb hc
  have hrone : r ≠ 1 := by
    intro hr
    have : b = c := by
      dsimp only [r] at hr
      field_simp [hc] at hr
      exact hr
    exact hbc this
  have hszero : s ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hc) hbc'
  have hcsub : c = s * (r - 1) := by
    dsimp only [r, s]
    field_simp [hc, hbc']
  have hbsub : b = r * s * (r - 1) := by
    dsimp only [r, s]
    field_simp [hc, hbc']
  have hAidentity :
      c ^ 2 + c - b = s * (r - 1) ^ 2 * (s - 1) := by
    rw [hbsub, hcsub]
    ring
  have hBone :
      tateSixNumerator b c =
        s ^ 2 * (r - 1) ^ 3 * (r - s) := by
    rw [hbsub, hcsub]
    simp only [tateSixNumerator]
    ring
  have hCone :
      tateSevenAux b c =
        -s ^ 2 * (r - 1) ^ 3 * (r * s - 2 * r + 1) := by
    rw [hbsub, hcsub]
    simp only [tateSevenAux]
    ring
  have hsone : s ≠ 1 := by
    intro hs
    apply hA
    rw [hAidentity, hs]
    ring
  have hrs : r ≠ s := by
    intro hrs
    apply hB
    rw [hBone, hrs]
    ring
  have hCfactor : r * s - 2 * r + 1 ≠ 0 := by
    intro hfactor
    apply hC
    rw [hCone, hfactor]
    ring
  have hsubpoly :
      orderThirteenPolynomial (r * s * (r - 1)) (s * (r - 1)) = 0 := by
    rwa [← hbsub, ← hcsub]
  rw [orderThirteenPolynomial_substitution] at hsubpoly
  have hprefactor : s ^ 7 * (r - 1) ^ 11 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 7 hszero)
      (pow_ne_zero 11 (sub_ne_zero.mpr hrone))
  have hreduced : orderThirteenReducedPolynomial r s = 0 :=
    (mul_eq_zero.mp hsubpoly).resolve_left hprefactor
  exact ⟨r, s, rfl, rfl, hrzero, hrone, hszero, hsone, hrs,
    hCfactor, hbsub, hcsub, hreduced⟩

/-- An exact rational point of order `13` produces both the denominator-safe Tate
certificate and a noncuspidal rational point on the reduced affine `X₁(13)` model. -/
theorem exists_tateOrderThirteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 13) :
    ∃ b c u r s : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      tateSixNumerator b c ≠ 0 ∧
      tateSevenAux b c ≠ 0 ∧
      orderThirteenPolynomial b c = 0 ∧
      u ^ 12 * E.Δ = tateNormalDiscriminant b c ∧
      r = b / c ∧ s = c ^ 2 / (b - c) ∧
      r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ s ∧
      r * s - 2 * r + 1 ≠ 0 ∧
      b = r * s * (r - 1) ∧ c = s * (r - 1) ∧
      orderThirteenReducedPolynomial r s = 0 := by
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
          (tateNormalCurve b c).toAffine.Point) = 13 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc := c_ne_zero_of_marked_order_thirteen b c hb h00 hmarked
  have hbc := parameters_ne_of_marked_order_thirteen b c hb h00 hmarked
  have hA :=
    five_numerator_ne_of_marked_order_thirteen b c hb hc hbc h00 hmarked
  have hB :=
    six_numerator_ne_of_marked_order_thirteen b c hb hc hbc hA h00 hmarked
  have hC :=
    seven_aux_ne_of_marked_order_thirteen b c hb hc hbc hA hB h00 hmarked
  have hpoly :=
    orderThirteenPolynomial_eq_zero_of_marked_order b c hb h00 hmarked
  obtain ⟨r, s, hr, hs, hrzero, hrone, hszero, hsone, hrs,
      hCfactor, hbsub, hcsub, hreduced⟩ :=
    exists_orderThirteen_reduced_certificate
      b c hb hc hbc hA hB hC hpoly
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  have hdisc' : u ^ 12 * E.Δ = tateNormalDiscriminant b c := by
    rw [← hbase, hdisc, tateNormalCurve_discriminant]
  exact ⟨b, c, u, r, s, hu, hb, hc, hbc, hA, hB, hC, hpoly,
    hdisc', hr, hs, hrzero, hrone, hszero, hsone, hrs, hCfactor,
    hbsub, hcsub, hreduced⟩

end MazurTorsion.Kubert
