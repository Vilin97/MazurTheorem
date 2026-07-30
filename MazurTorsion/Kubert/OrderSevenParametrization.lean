/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalFormMultiples

/-!
# The order-seven Tate parametrization

On Tate normal form the marked origin has order seven exactly when

`b² - bc - c³ = 0`,

and then `d = b/c` parametrizes `X₁(7)`:

`b = d³ - d²`, `c = d² - d`, with `d ∉ {0,1}`.

The discriminant of the parametrized family is
`d⁷(d-1)⁷(d³-8d²+5d+1)`, and the `X₀(7)` hauptmodul value

`t₇ = 49d(d-1)/(d³-8d²+5d+1)`

satisfies the cleared `j`-identity used by the composite-level
hauptmodul certificates.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- On Tate normal form, an origin killed by seven and not by lower
multiples satisfies `b² - bc - c³ = 0` with `c ≠ 0`. -/
theorem orderSeven_tate_relation
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (hP0 : (WeierstrassCurve.Affine.Point.some 0 0 h00 :
      (tateNormalCurve b c).toAffine.Point) ≠ 0)
    (h7 : (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
      (tateNormalCurve b c).toAffine.Point) = 0) :
    c ≠ 0 ∧ b ^ 2 - b * c - c ^ 3 = 0 := by
  set P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00 with hPdef
  obtain ⟨h₃, htriple⟩ := three_nsmul_origin_coordinates b c hb h00
  have hc : c ≠ 0 := by
    intro hc0
    subst hc0
    have h3eq : (3 : ℕ) • P = -P := by
      rw [htriple, hPdef, WeierstrassCurve.Affine.Point.neg_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some _ rfl
        (by norm_num [WeierstrassCurve.Affine.negY, tateNormalCurve])
    have h4 : (4 : ℕ) • P = 0 := by
      have h4split : (4 : ℕ) • P = (3 : ℕ) • P + P := by abel
      rw [h4split, h3eq]
      abel
    apply hP0
    calc
      P = (2 : ℕ) • ((4 : ℕ) • P) - (7 : ℕ) • P := by abel
      _ = 0 := by rw [h4, h7]; simp
  refine ⟨hc, ?_⟩
  obtain ⟨h₄, hquad⟩ := four_mul_origin_coordinates b c hb hc h00
  have hfour : (4 : ℕ) • P = WeierstrassCurve.Affine.Point.some
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [hPdef, show (4 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
    exact hquad
  have hthree : (3 : ℕ) • P = WeierstrassCurve.Affine.Point.some
      c (b - c) h₃ := by
    rw [hPdef]
    exact (three_nsmul_origin_coordinates b c hb h00).choose_spec
  have hsum : (4 : ℕ) • P = -((3 : ℕ) • P) := by
    rw [← add_eq_zero_iff_eq_neg]
    calc
      (4 : ℕ) • P + (3 : ℕ) • P = (7 : ℕ) • P := by abel
      _ = 0 := h7
  rw [hfour, hthree, WeierstrassCurve.Affine.Point.neg_some] at hsum
  have hx :=
    (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hsum |>.1
  have hcleared : b * (b - c) = c ^ 3 := by
    field_simp at hx
    linarith [hx]
  linarith [hcleared]

/-- The order-seven relation is rationally parametrized by `d = b/c`. -/
theorem orderSeven_parametrization
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrel : b ^ 2 - b * c - c ^ 3 = 0) :
    ∃ d : ℚ, d ≠ 0 ∧ d ≠ 1 ∧
      b = d ^ 3 - d ^ 2 ∧ c = d ^ 2 - d := by
  refine ⟨b / c, div_ne_zero hb hc, ?_, ?_, ?_⟩
  · intro h1
    have hbc : b = c := by
      field_simp at h1
      linarith [h1]
    rw [hbc] at hrel
    have : c ^ 2 * c = 0 := by linarith [hrel]
    exact hc (by
      rcases mul_eq_zero.mp this with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      · exact h)
  · field_simp
    linear_combination -hrel
  · field_simp
    linear_combination -hrel

/-- The discriminant of the parametrized order-seven family. -/
theorem orderSeven_Δ (d : ℚ) :
    (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateNormalCurve]
  ring

/-- The invariant `c₄` of the parametrized order-seven family. -/
theorem orderSeven_c₄ (d : ℚ) :
    (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ =
      (d ^ 2 - d + 1) *
        (d ^ 6 - 11 * d ^ 5 + 30 * d ^ 4 - 15 * d ^ 3 -
          10 * d ^ 2 + 5 * d + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    tateNormalCurve]
  ring

/-- The cleared `j`-identity for the order-seven hauptmodul value on the
parametrized family: with `t₇ = 49d(d-1)/(d³-8d²+5d+1)`,

`(t₇²+13t₇+49)(t₇²+245t₇+2401)³ · Δ = c₄³ · t₇⁷`. -/
theorem orderSeven_hauptmodul_identity
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    ((49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 2 +
          13 * (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) + 49) *
        ((49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 2 +
          245 * (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) +
          2401) ^ 3 *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 *
        (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 7 := by
  rw [orderSeven_Δ, orderSeven_c₄]
  set K : ℚ := d ^ 3 - 8 * d ^ 2 + 5 * d + 1 with hKdef
  field_simp [hK]
  simp only [hKdef]
  ring

end MazurTorsion.Kubert
