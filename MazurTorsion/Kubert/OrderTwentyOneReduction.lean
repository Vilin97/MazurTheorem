/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.ThreeNormalForm
import MazurTorsion.Kubert.OrderSevenParametrization
import MazurTorsion.NumberTheory.XZeroTwentyOneDescent

/-!
# The order-twenty-one hauptmodul certificate

A rational point of exact order twenty-one provides a point of exact order
seven and a point of exact order three.  The order-seven multiple
normalizes the curve into the parametrized `X₁(7)` Tate family, and the
order-three multiple further produces the order-three normal form.  Both
normal forms carry cleared `j`-identities for their hauptmodul values, so
the two values satisfy the recorded fibre-product equation of `X₀(3)` and
`X₀(7)`:

`HauptmodulPair t₃ t₇` with `t₃ ≠ 0` and `t₇ ≠ 0`.

The cleared `j`-links back to the original curve are retained for the
final exceptional-`j` exclusions.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Two cleared hauptmodul `j`-identities against a common curve glue into
the fibre-product equation. -/
theorem hauptmodulPair_of_cleared
    {t₃ t₇ Δ C : ℚ} (hΔ : Δ ≠ 0)
    (h3 : (t₃ + 27) * (t₃ + 3) ^ 3 * Δ = C ^ 3 * t₃)
    (h7 : (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * Δ = C ^ 3 * t₇ ^ 7) :
    MazurTorsion.XZeroTwentyOne.HauptmodulPair t₃ t₇ := by
  unfold MazurTorsion.XZeroTwentyOne.HauptmodulPair
  apply mul_left_cancel₀ hΔ
  linear_combination t₇ ^ 7 * h3 - t₃ * h7

/-- Exact order twenty-one normalizes the curve into the parametrized
order-seven Tate family, carrying the discriminant and `c₄` scales and the
image of the original point. -/
theorem orderTwentyOne_tate_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21) :
    ∃ (d u : ℚ) (_ : d ≠ 0) (_ : d ≠ 1) (_ : u ≠ 0)
      (h00 : (tateNormalCurve (d ^ 3 - d ^ 2)
        (d ^ 2 - d)).toAffine.Nonsingular 0 0)
      (e : E.toAffine.Point ≃+
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).toAffine.Point),
      e ((3 : ℕ) • P) = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * E.Δ =
          (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ ∧
        u ^ 4 * E.c₄ =
          (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ := by
  have h210 : (21 : ℕ) • P = 0 := by
    rw [← h21]
    exact addOrderOf_nsmul_eq_zero P
  have hnot : ∀ n : ℕ, ¬ (21 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (h21 ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hQ0 : (3 : ℕ) • P ≠ 0 := hnot 3 (by norm_num)
  have hQ2 : (3 : ℕ) • P + (3 : ℕ) • P ≠ 0 := by
    intro h
    exact hnot 6 (by norm_num) (by rw [show (6 : ℕ) • P =
      (3 : ℕ) • P + (3 : ℕ) • P by abel]; exact h)
  have hQ3 : (3 : ℕ) • P + (3 : ℕ) • P + (3 : ℕ) • P ≠ 0 := by
    intro h
    exact hnot 9 (by norm_num) (by rw [show (9 : ℕ) • P =
      (3 : ℕ) • P + (3 : ℕ) • P + (3 : ℕ) • P by abel]; exact h)
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, hc₄⟩ :=
    exists_tateNormalCurve_scaled E ((3 : ℕ) • P) hQ2 hQ3
  have horigin0 :
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) ≠ 0 := by
    rw [← heQ]
    intro h
    exact hQ0 (by simpa using e.injective (by simpa using h))
  have h7smul :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heQ, ← map_nsmul]
    have : (7 : ℕ) • ((3 : ℕ) • P) = (21 : ℕ) • P := by
      rw [← mul_nsmul]
    rw [this, h210, map_zero]
  obtain ⟨hc, hrel⟩ :=
    orderSeven_tate_relation b c hb h00 horigin0 h7smul
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    orderSeven_parametrization b c hb hc hrel
  subst hbeq
  subst hceq
  exact ⟨d, u, hd0, hd1, hu, h00, e, heQ, hdisc, hc₄⟩

/-- A rational point of exact order twenty-one produces noncuspidal
rational hauptmodul values satisfying the `X₀(3)`–`X₀(7)` fibre-product
equation, with cleared `j`-links to the ambient curve. -/
theorem exists_hauptmodulPair_of_order_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21) :
    ∃ t₃ t₇ : ℚ, t₃ ≠ 0 ∧ t₇ ≠ 0 ∧
      MazurTorsion.XZeroTwentyOne.HauptmodulPair t₃ t₇ ∧
      (t₃ + 27) * (t₃ + 3) ^ 3 * E.Δ = E.c₄ ^ 3 * t₃ ∧
      (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * E.Δ = E.c₄ ^ 3 * t₇ ^ 7 := by
  have hΔE : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  -- the order-seven side
  obtain ⟨d, u, hd0, hd1, hu, h00₇, e₇, -, hdisc₇, hc₄₇⟩ :=
    orderTwentyOne_tate_package E P h21
  have hΔfam :
      (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
        d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) :=
    orderSeven_Δ d
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hzero
    apply hΔE
    have h12 : u ^ 12 * E.Δ = 0 := by
      rw [hdisc₇, hΔfam, hzero, mul_zero]
    rcases mul_eq_zero.mp h12 with h | h
    · exact absurd h (pow_ne_zero 12 hu)
    · exact h
  set t₇ : ℚ :=
    49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) with ht₇def
  have ht₇0 : t₇ ≠ 0 := by
    rw [ht₇def]
    apply div_ne_zero _ hK
    exact mul_ne_zero (mul_ne_zero (by norm_num) hd0)
      (sub_ne_zero.mpr hd1)
  have h7fam := orderSeven_hauptmodul_identity d hd0 hd1 hK
  have h7 : (t₇ ^ 2 + 13 * t₇ + 49) *
      (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * E.Δ = E.c₄ ^ 3 * t₇ ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hu)
    calc
      u ^ 12 * ((t₇ ^ 2 + 13 * t₇ + 49) *
          (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * E.Δ) =
          (t₇ ^ 2 + 13 * t₇ + 49) *
            (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * (u ^ 12 * E.Δ) := by
        ring
      _ = (t₇ ^ 2 + 13 * t₇ + 49) *
            (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 *
            (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
        rw [hdisc₇]
      _ = (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 *
            t₇ ^ 7 := by
        rw [ht₇def]
        exact h7fam
      _ = (u ^ 4 * E.c₄) ^ 3 * t₇ ^ 7 := by rw [hc₄₇]
      _ = u ^ 12 * (E.c₄ ^ 3 * t₇ ^ 7) := by ring
  -- the order-three side
  have h70 : (7 : ℕ) • P ≠ 0 := by
    intro hzero
    have := addOrderOf_dvd_of_nsmul_eq_zero hzero
    rw [h21] at this
    omega
  have h73 : (7 : ℕ) • P + (7 : ℕ) • P + (7 : ℕ) • P = 0 := by
    rw [show (7 : ℕ) • P + (7 : ℕ) • P + (7 : ℕ) • P =
      (21 : ℕ) • P by abel, ← h21]
    exact addOrderOf_nsmul_eq_zero P
  obtain ⟨a₁, a₃, ha₃, h00₃, e₃, -, hΔ₃, hc₄₃⟩ :=
    exists_threeNormalCurve E ((7 : ℕ) • P) h70 h73
  set t₃ : ℚ := (a₁ ^ 3 - 27 * a₃) / a₃ with ht₃def
  have hΔ₃fam : (threeNormalCurve a₁ a₃).Δ =
      a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃) := threeNormalCurve_Δ a₁ a₃
  have hnum : a₁ ^ 3 - 27 * a₃ ≠ 0 := by
    intro hzero
    apply hΔE
    rw [hΔ₃, hΔ₃fam, hzero, mul_zero]
  have ht₃0 : t₃ ≠ 0 := by
    rw [ht₃def]
    exact div_ne_zero hnum ha₃
  have h3fam := threeNormal_hauptmodul_identity a₁ a₃ ha₃
  have h3 : (t₃ + 27) * (t₃ + 3) ^ 3 * E.Δ = E.c₄ ^ 3 * t₃ := by
    rw [hΔ₃, hc₄₃, ht₃def]
    exact h3fam
  exact ⟨t₃, t₇, ht₃0, ht₇0,
    hauptmodulPair_of_cleared hΔE h3 h7, h3, h7⟩

end MazurTorsion.Kubert
