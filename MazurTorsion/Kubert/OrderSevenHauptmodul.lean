/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenParametrization
import MazurTorsion.Kubert.OrderSevenCorrespondence

/-!
# The Hauptmodul attached to an exact order-seven point

Tate normalization of an exact order-seven point produces a nonzero
level-seven Hauptmodul.  This file retains the cleared `j`-identity against
the original Weierstrass curve, so consumers need not expose the auxiliary
normal-form coordinate change.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- An exact order-seven point supplies a noncuspidal level-seven Hauptmodul
whose cleared `j`-identity is measured against the original curve. -/
theorem exists_orderSevenHauptmodul_of_exactOrder
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (R : W.toAffine.Point) (hR : addOrderOf R = 7) :
    ∃ B : ℚ, B ≠ 0 ∧
      orderSevenJNumerator B * W.Δ = W.c₄ ^ 3 * B ^ 7 := by
  have hnot : ∀ n : ℕ, ¬(7 ∣ n) → (n : ℕ) • R ≠ 0 := by
    intro n hn hzero
    exact hn (hR ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hR2 : R + R ≠ 0 := by
    intro h
    exact hnot 2 (by norm_num) (by simpa [two_nsmul] using h)
  have hR3 : R + R + R ≠ 0 := by
    intro h
    exact hnot 3 (by norm_num) (by
      rw [show (3 : ℕ) • R = R + R + R by abel]
      exact h)
  obtain ⟨b, c, u, hu, hb, h00, e, heR, hdisc, hc₄, -⟩ :=
    exists_tateNormalCurve_scaled W R hR2 hR3
  have h7R : (7 : ℕ) • R = 0 := by
    rw [← hR]
    exact addOrderOf_nsmul_eq_zero R
  have h7origin :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heR, ← map_nsmul, h7R, map_zero]
  obtain ⟨hc, hrel⟩ :=
    orderSeven_tate_relation b c hb h00
      (WeierstrassCurve.Affine.Point.some_ne_zero h00) h7origin
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    orderSeven_parametrization b c hb hc hrel
  subst b
  subst c
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hK0
    have hΔzero :
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ = 0 := by
      rw [orderSeven_Δ, hK0]
      ring
    have hΔne :
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ ≠ 0 := by
      rw [← hdisc]
      exact mul_ne_zero (pow_ne_zero 12 hu) W.isUnit_Δ.ne_zero
    exact hΔne hΔzero
  let B : ℚ := 49 * d * (d - 1) /
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)
  have hB : B ≠ 0 := by
    dsimp only [B]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hd0)
        (sub_ne_zero.mpr hd1)) hK
  refine ⟨B, hB, ?_⟩
  have hfam := orderSeven_hauptmodul_identity d hd0 hd1 hK
  apply mul_left_cancel₀ (pow_ne_zero 12 hu)
  calc
    u ^ 12 * (orderSevenJNumerator B * W.Δ) =
        orderSevenJNumerator B * (u ^ 12 * W.Δ) := by ring
    _ = orderSevenJNumerator B *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
      rw [hdisc]
    _ = (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 * B ^ 7 := by
      dsimp only [B, orderSevenJNumerator]
      exact hfam
    _ = (u ^ 4 * W.c₄) ^ 3 * B ^ 7 := by rw [hc₄]
    _ = u ^ 12 * (W.c₄ ^ 3 * B ^ 7) := by ring

end MazurTorsion.Kubert
