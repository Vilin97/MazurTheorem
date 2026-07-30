/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFifteenReduction

/-!
# Reduction of a point of order fourteen

An exact rational point of order `14` can be put in Tate normal form.  The checked
addition recurrence computes its sixth and seventh multiples.  Since the seventh
multiple has order `2`, its coordinates satisfy

`2 * y(7P) + (1-c) * x(7P) - b = 0`.

Clearing precisely the denominators introduced by the recurrence gives
`orderFourteenPolynomial`.  This file proves only this forward reduction, retaining
all denominator conditions and the discriminant scale.  It makes no assertion about
the rational points of the resulting genus-one parameter curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The numerator appearing in the denominator-safe formula for `x(6P)`. -/
def tateSixNumerator (b c : ℚ) : ℚ :=
  b ^ 2 - b * c - c ^ 3

/-- An auxiliary numerator in the coordinates of `7P`. -/
def tateSevenAux (b c : ℚ) : ℚ :=
  2 * b ^ 2 - b * c ^ 2 - 3 * b * c + c ^ 2

/-- The numerator in the denominator-safe formula for `y(7P)`. -/
def tateSevenYNumerator (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c + b * c ^ 3 + 3 * b * c ^ 2 -
    c ^ 5 - c ^ 4 - c ^ 3

/-- The recurrence-defined `X`-coordinate of `7P`. -/
def tateSevenX (b c : ℚ) : ℚ :=
  tateNextX b c (tateSixX b c) (tateSixY b c)

/-- The recurrence-defined `Y`-coordinate of `7P`. -/
def tateSevenY (b c : ℚ) : ℚ :=
  tateNextY b c (tateSixX b c) (tateSixY b c)

/-- The affine Tate-parameter equation forced by exact order `14`.

Writing

* `A = c² + c - b`,
* `B = b² - bc - c³`,
* `C = 2b² - bc² - 3bc + c²`, and
* `D = b³ - 3b²c + bc³ + 3bc² - c⁵ - c⁴ - c³`,

the equation is `2bA²D - (1-c)cACB - B³ = 0`.  It is the numerator of
`2y(7P) + (1-c)x(7P) - b` after multiplication by `B³ / b`. -/
def orderFourteenPolynomial (b c : ℚ) : ℚ :=
  let A := c ^ 2 + c - b
  let B := tateSixNumerator b c
  let C := tateSevenAux b c
  let D := tateSevenYNumerator b c
  2 * b * A ^ 2 * D - (1 - c) * c * A * C * B - B ^ 3

private lemma tateFiveRatio_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) :
    tateFiveY b c / tateFiveX b c =
      c * tateSixNumerator b c /
        ((b - c) * (c ^ 2 + c - b)) := by
  simp only [tateFiveX, tateFiveY, tateSixNumerator]
  field_simp [hb, hc, sub_ne_zero.mpr hbc]

lemma tateSixX_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0) :
    tateSixX b c =
      (b - c) * tateSixNumerator b c / (c ^ 2 + c - b) ^ 2 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateFiveY b c / tateFiveX b c = c * B / (d * A) := by
    simpa only [A, B, d] using tateFiveRatio_eq b c hb hc hbc
  have hxfive : tateFiveX b c = b * c * A / d ^ 2 := by
    simp only [tateFiveX, A, d]
  change tateNextX b c (tateFiveX b c) (tateFiveY b c) =
    d * B / A ^ 2
  simp only [tateNextX]
  rw [hratio, hxfive]
  field_simp [hA, hd]
  dsimp only [A, B, d, tateSixNumerator]
  ring

lemma tateSixY_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0) :
    tateSixY b c =
      -c * (b - c) ^ 2 * tateSevenAux b c /
        (c ^ 2 + c - b) ^ 3 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateFiveY b c / tateFiveX b c = c * B / (d * A) := by
    simpa only [A, B, d] using tateFiveRatio_eq b c hb hc hbc
  have hxfive : tateFiveX b c = b * c * A / d ^ 2 := by
    simp only [tateFiveX, A, d]
  have hyfive : tateFiveY b c = b * c ^ 2 * B / d ^ 3 := by
    simp only [tateFiveY, B, d, tateSixNumerator]
  have hxsix : tateSixX b c = d * B / A ^ 2 := by
    simpa only [A, B, d] using
      tateSixX_eq_reduced b c hb hc hbc hfiveNumerator
  change
    -((tateFiveY b c / tateFiveX b c) *
          (tateSixX b c - tateFiveX b c) + tateFiveY b c) -
        (1 - c) * tateSixX b c + b =
      -c * d ^ 2 * C / A ^ 3
  rw [hratio, hxfive, hyfive, hxsix]
  field_simp [hA, hd]
  dsimp only [A, B, C, d, tateSixNumerator, tateSevenAux]
  ring

private lemma tateSixRatio_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0) :
    tateSixY b c / tateSixX b c =
      -c * (b - c) * tateSevenAux b c /
        ((c ^ 2 + c - b) * tateSixNumerator b c) := by
  rw [tateSixX_eq_reduced b c hb hc hbc hfiveNumerator,
    tateSixY_eq_reduced b c hb hc hbc hfiveNumerator]
  field_simp [hc, sub_ne_zero.mpr hbc, hfiveNumerator,
    hsixNumerator]

lemma tateSevenX_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0) :
    tateSevenX b c =
      -b * c * (c ^ 2 + c - b) * tateSevenAux b c /
        tateSixNumerator b c ^ 2 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hB : B ≠ 0 := by simpa only [B] using hsixNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateSixY b c / tateSixX b c = -c * d * C / (A * B) := by
    simpa only [A, B, C, d] using
      tateSixRatio_eq b c hb hc hbc hfiveNumerator hsixNumerator
  have hxsix : tateSixX b c = d * B / A ^ 2 := by
    simpa only [A, B, d] using
      tateSixX_eq_reduced b c hb hc hbc hfiveNumerator
  change tateNextX b c (tateSixX b c) (tateSixY b c) =
    -b * c * A * C / B ^ 2
  simp only [tateNextX]
  rw [hratio, hxsix]
  field_simp [hA, hB, hd]
  dsimp only [A, B, C, d, tateSixNumerator, tateSevenAux]
  ring

lemma tateSevenY_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0) :
    tateSevenY b c =
      b ^ 2 * (c ^ 2 + c - b) ^ 2 * tateSevenYNumerator b c /
        tateSixNumerator b c ^ 3 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  let D : ℚ := tateSevenYNumerator b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hB : B ≠ 0 := by simpa only [B] using hsixNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateSixY b c / tateSixX b c = -c * d * C / (A * B) := by
    simpa only [A, B, C, d] using
      tateSixRatio_eq b c hb hc hbc hfiveNumerator hsixNumerator
  have hxsix : tateSixX b c = d * B / A ^ 2 := by
    simpa only [A, B, d] using
      tateSixX_eq_reduced b c hb hc hbc hfiveNumerator
  have hysix : tateSixY b c = -c * d ^ 2 * C / A ^ 3 := by
    simpa only [A, C, d] using
      tateSixY_eq_reduced b c hb hc hbc hfiveNumerator
  have hxseven : tateSevenX b c = -b * c * A * C / B ^ 2 := by
    simpa only [A, B, C] using
      tateSevenX_eq_reduced b c hb hc hbc hfiveNumerator hsixNumerator
  change
    -((tateSixY b c / tateSixX b c) *
          (tateSevenX b c - tateSixX b c) + tateSixY b c) -
        (1 - c) * tateSevenX b c + b =
      b ^ 2 * A ^ 2 * D / B ^ 3
  rw [hratio, hxsix, hysix, hxseven]
  field_simp [hA, hB, hd]
  dsimp only [A, B, C, D, d, tateSixNumerator, tateSevenAux,
    tateSevenYNumerator]
  ring

/-- Checked recurrence from `6P` to `7P`, with every denominator recorded. -/
theorem seven_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₇ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSevenX b c) (tateSevenY b c),
      (7 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateSevenX b c) (tateSevenY b c) h₇ := by
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hfiveNumerator h00
  have hxsix : tateSixX b c ≠ 0 := by
    rw [tateSixX_eq_reduced b c hb hc hbc hfiveNumerator]
    exact div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hbc) hsixNumerator)
      (pow_ne_zero 2 hfiveNumerator)
  obtain ⟨h₇, hseven⟩ :=
    add_origin_coordinates b c (tateSixX b c) (tateSixY b c)
      hxsix h₆ h00
  refine ⟨h₇, ?_⟩
  rw [show (7 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hsix, hseven]
  rfl

private theorem nsmul_ne_zero_of_marked_order_fourteen
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 14) (n : ℕ) (hndvd : ¬14 ∣ n) :
    n • P ≠ 0 := by
  intro hn
  apply hndvd
  rw [← horder]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn

private lemma c_ne_zero_of_marked_order_fourteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14) :
    c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 4 (by norm_num)
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

private lemma parameters_ne_of_marked_order_fourteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14) :
    b ≠ c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 5 (by norm_num)
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

private lemma five_numerator_ne_of_marked_order_fourteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14) :
    c ^ 2 + c - b ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 4 (by norm_num)
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 6 (by norm_num)
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

private lemma six_numerator_ne_of_marked_order_fourteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14) :
    tateSixNumerator b c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 5 (by norm_num)
  have hsevenNe : (7 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 7 (by norm_num)
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

private lemma seven_aux_ne_of_marked_order_fourteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14) :
    tateSevenAux b c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 6 (by norm_num)
  have heightNe : (8 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_fourteen P horder 8 (by norm_num)
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

private lemma orderFourteenPolynomial_eq_zero_of_two_torsion
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h₇ : (tateNormalCurve b c).toAffine.Nonsingular
      (tateSevenX b c) (tateSevenY b c))
    (htwo :
      (2 : ℕ) •
          WeierstrassCurve.Affine.Point.some
            (tateSevenX b c) (tateSevenY b c) h₇ = 0) :
    orderFourteenPolynomial b c = 0 := by
  let W := tateNormalCurve b c
  let R : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some
      (tateSevenX b c) (tateSevenY b c) h₇
  have hselfneg : R = -R := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [two_nsmul] using htwo
  have hyneg :
      tateSevenY b c =
        W.toAffine.negY (tateSevenX b c) (tateSevenY b c) := by
    rw [WeierstrassCurve.Affine.Point.neg_some] at hselfneg
    exact
      (WeierstrassCurve.Affine.Point.some.injEq
        (tateSevenX b c) (tateSevenY b c) h₇
        (tateSevenX b c)
        (W.toAffine.negY (tateSevenX b c) (tateSevenY b c))
        _).mp hselfneg |>.2
  have hlinear :
      2 * tateSevenY b c + (1 - c) * tateSevenX b c - b = 0 := by
    simp only [W, tateNormalCurve, WeierstrassCurve.Affine.negY] at hyneg
    linarith
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  let D : ℚ := tateSevenYNumerator b c
  have hB : B ≠ 0 := by simpa only [B] using hsixNumerator
  have hxseven : tateSevenX b c = -b * c * A * C / B ^ 2 := by
    simpa only [A, B, C] using
      tateSevenX_eq_reduced b c hb hc hbc hfiveNumerator hsixNumerator
  have hyseven : tateSevenY b c = b ^ 2 * A ^ 2 * D / B ^ 3 := by
    simpa only [A, B, D] using
      tateSevenY_eq_reduced b c hb hc hbc hfiveNumerator hsixNumerator
  rw [hxseven, hyseven] at hlinear
  have hscaled :
      b * (2 * b * A ^ 2 * D - (1 - c) * c * A * C * B - B ^ 3) = 0 := by
    field_simp [hB] at hlinear
    linear_combination hlinear
  have hpoly :
      2 * b * A ^ 2 * D - (1 - c) * c * A * C * B - B ^ 3 = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hb
  simpa only [orderFourteenPolynomial, A, B, C, D] using hpoly

/-- Exact order `14` of the marked Tate point forces the denominator-safe
`X₁(14)` parameter polynomial to vanish. -/
theorem orderFourteenPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14) :
    orderFourteenPolynomial b c = 0 := by
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc := c_ne_zero_of_marked_order_fourteen b c hb h00 horder
  have hbc := parameters_ne_of_marked_order_fourteen b c hb h00 horder
  have hA :=
    five_numerator_ne_of_marked_order_fourteen b c hb hc hbc h00 horder
  have hB :=
    six_numerator_ne_of_marked_order_fourteen b c hb hc hbc hA h00 horder
  obtain ⟨h₇, hseven⟩ :=
    seven_nsmul_origin_coordinates b c hb hc hbc hA hB h00
  have hsevenOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some
          (tateSevenX b c) (tateSevenY b c) h₇) = 2 := by
    rw [← hseven]
    change addOrderOf ((7 : ℕ) • P) = 2
    rw [addOrderOf_nsmul' P (by norm_num), horder]
    norm_num
  have htwo :
      (2 : ℕ) •
          WeierstrassCurve.Affine.Point.some
            (tateSevenX b c) (tateSevenY b c) h₇ = 0 := by
    rw [← hsevenOrder]
    exact addOrderOf_nsmul_eq_zero _
  exact orderFourteenPolynomial_eq_zero_of_two_torsion
    b c hb hc hbc hA hB h₇ htwo

/-- An exact rational point of order `14` produces a point on the explicit
Tate-parameter model of `X₁(14)`.  The four recurrence denominators, the
next noncuspidal numerator, and the original discriminant scale are retained.

No classification of rational points on `orderFourteenPolynomial b c = 0`
is asserted here. -/
theorem exists_tateOrderFourteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 14) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      tateSixNumerator b c ≠ 0 ∧
      tateSevenAux b c ≠ 0 ∧
      orderFourteenPolynomial b c = 0 ∧
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
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 14 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc := c_ne_zero_of_marked_order_fourteen b c hb h00 hmarked
  have hbc := parameters_ne_of_marked_order_fourteen b c hb h00 hmarked
  have hA :=
    five_numerator_ne_of_marked_order_fourteen b c hb hc hbc h00 hmarked
  have hB :=
    six_numerator_ne_of_marked_order_fourteen b c hb hc hbc hA h00 hmarked
  have hC :=
    seven_aux_ne_of_marked_order_fourteen b c hb hc hbc hA hB h00 hmarked
  have hpoly :=
    orderFourteenPolynomial_eq_zero_of_marked_order b c hb h00 hmarked
  refine ⟨b, c, u, hu, hb, hc, hbc, hA, hB, hC, hpoly, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rw [← hbase, hdisc, tateNormalCurve_discriminant]

end MazurTorsion.Kubert
