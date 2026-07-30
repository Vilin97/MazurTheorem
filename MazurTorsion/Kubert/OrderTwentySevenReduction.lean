/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderNineReduction
import MazurTorsion.Kubert.OrderEighteenModel

/-!
# The order-twenty-seven family reduction

A rational point of exact order twenty-seven has an order-nine triple,
which normalizes the curve into the rationally parametrized `X₁(9)` Tate
family

`b = f²(f-1)(f²-f+1)`, `c = f²(f-1)`.

This file packages the normalization: the parameter constraints, the
discriminant and `c₄` formulas of the family, the scaling data, and the
transported coordinates of the original point, whose triple is the
marked origin.  It is the ground floor of the order-twenty-seven
hauptmodul tower.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The order-nine Tate parameter values. -/
@[simp] def nineB (f : ℚ) : ℚ := f ^ 2 * (f - 1) * (f ^ 2 - f + 1)

@[simp] def nineC (f : ℚ) : ℚ := f ^ 2 * (f - 1)

/-- The discriminant of the parametrized order-nine family. -/
theorem orderNine_Δ (f : ℚ) :
    (tateNormalCurve (nineB f) (nineC f)).Δ =
      f ^ 9 * (f - 1) ^ 9 * (f ^ 2 - f + 1) ^ 3 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateNormalCurve, nineB, nineC]
  ring

/-- The invariant `c₄` of the parametrized order-nine family. -/
theorem orderNine_c₄ (f : ℚ) :
    (tateNormalCurve (nineB f) (nineC f)).c₄ =
      (f ^ 3 - 3 * f ^ 2 + 1) *
        (f ^ 9 - 9 * f ^ 8 + 27 * f ^ 7 - 48 * f ^ 6 + 54 * f ^ 5 -
          45 * f ^ 4 + 27 * f ^ 3 - 9 * f ^ 2 + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    tateNormalCurve, nineB, nineC]
  ring

/-- Exact order twenty-seven normalizes the curve into the parametrized
order-nine Tate family, carrying the scaling data, the marked image of
the order-nine triple, and the coordinates of the transported point. -/
theorem orderTwentySeven_family_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h27 : addOrderOf P = 27) :
    ∃ (f u : ℚ) (_ : f ≠ 0) (_ : f ≠ 1)
      (_ : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (_ : u ≠ 0)
      (h00 : (tateNormalCurve (nineB f)
        (nineC f)).toAffine.Nonsingular 0 0)
      (e : E.toAffine.Point ≃+
        (tateNormalCurve (nineB f) (nineC f)).toAffine.Point),
      e ((3 : ℕ) • P) = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * E.Δ = (tateNormalCurve (nineB f) (nineC f)).Δ ∧
        u ^ 4 * E.c₄ = (tateNormalCurve (nineB f) (nineC f)).c₄ ∧
        addOrderOf (e P) = 27 ∧
        (3 : ℕ) • e P = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
  have h270 : (27 : ℕ) • P = 0 := by
    rw [← h27]
    exact addOrderOf_nsmul_eq_zero P
  have hnot : ∀ n : ℕ, ¬ (27 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (h27 ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hQ2 : (3 : ℕ) • P + (3 : ℕ) • P ≠ 0 := by
    intro h
    exact hnot 6 (by norm_num) (by rw [show (6 : ℕ) • P =
      (3 : ℕ) • P + (3 : ℕ) • P by abel]; exact h)
  have hQ3 : (3 : ℕ) • P + (3 : ℕ) • P + (3 : ℕ) • P ≠ 0 := by
    intro h
    exact hnot 9 (by norm_num) (by rw [show (9 : ℕ) • P =
      (3 : ℕ) • P + (3 : ℕ) • P + (3 : ℕ) • P by abel]; exact h)
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, hc₄, -⟩ :=
    exists_tateNormalCurve_scaled E ((3 : ℕ) • P) hQ2 hQ3
  -- the marked point has exact order nine
  have horder9 : addOrderOf
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 9 := by
    rw [← heQ]
    have hpres : addOrderOf (e ((3 : ℕ) • P)) =
        addOrderOf ((3 : ℕ) • P) := by
      apply Nat.dvd_antisymm
      · exact addOrderOf_map_dvd e.toAddMonoidHom ((3 : ℕ) • P)
      · conv_lhs => rw [← e.symm_apply_apply ((3 : ℕ) • P)]
        exact addOrderOf_map_dvd e.symm.toAddMonoidHom
          (e ((3 : ℕ) • P))
    rw [hpres]
    -- `addOrderOf (3 • P) = 9`
    have h9smul : (9 : ℕ) • ((3 : ℕ) • P) = 0 := by
      rw [← mul_nsmul]
      norm_num
      exact h270
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h9smul
    have h30 : (3 : ℕ) • P ≠ 0 := hnot 3 (by norm_num)
    have h3smul : (3 : ℕ) • ((3 : ℕ) • P) ≠ 0 := by
      rw [← mul_nsmul]
      norm_num
      exact hnot 9 (by norm_num)
    have hdvd' : addOrderOf ((3 : ℕ) • P) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact hdvd
    rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp
        hdvd' with ⟨k, hk2, hkval⟩
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · exfalso
      apply h30
      have hone := addOrderOf_nsmul_eq_zero ((3 : ℕ) • P)
      rw [hkval, pow_zero, one_nsmul] at hone
      exact hone
    · exfalso
      apply h3smul
      have hthree := addOrderOf_nsmul_eq_zero ((3 : ℕ) • P)
      rwa [hkval, pow_one] at hthree
    · rw [hkval]
      norm_num
  -- the order-nine relation and its parametrization
  have hnine := orderNinePolynomial_eq_zero_of_marked_order
    b c hb h00 horder9
  have hc := c_ne_zero_of_marked_order_nine b c hb h00 horder9
  have hbc := parameters_ne_of_marked_order_nine b c hb h00 horder9
  obtain ⟨f, hcparam, hbparam⟩ :
      ∃ f : ℚ, c = f ^ 2 * (f - 1) ∧
        b = c * (f ^ 2 - f + 1) :=
    ⟨orderNineParameterD b c,
      (orderNine_parameterization b c hc hbc hnine).1,
      (orderNine_parameterization b c hc hbc hnine).2⟩
  have hbval : b = nineB f := by
    rw [nineB, hbparam, hcparam]
  have hcval : c = nineC f := by
    rw [nineC]
    exact hcparam
  subst hbval
  subst hcval
  have hf0 : f ≠ 0 := by
    intro h0
    apply hc
    rw [nineC, h0]
    ring
  have hf1 : f ≠ 1 := by
    intro h1
    apply hc
    rw [nineC, h1]
    ring
  have hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0 := by
    intro hzero
    have hΔ0 : (tateNormalCurve (nineB f) (nineC f)).Δ = 0 := by
      rw [orderNine_Δ, hzero, mul_zero]
    have hΔne : (tateNormalCurve (nineB f) (nineC f)).Δ ≠ 0 := by
      rw [← hdisc]
      exact mul_ne_zero (pow_ne_zero 12 hu) E.isUnit_Δ.ne_zero
    exact hΔne hΔ0
  -- transported order of the point itself
  have horder27 : addOrderOf (e P) = 27 := by
    have hpres : addOrderOf (e P) = addOrderOf P := by
      apply Nat.dvd_antisymm
      · exact addOrderOf_map_dvd e.toAddMonoidHom P
      · conv_lhs => rw [← e.symm_apply_apply P]
        exact addOrderOf_map_dvd e.symm.toAddMonoidHom (e P)
    rw [hpres, h27]
  refine ⟨f, u, hf0, hf1, hK, hu, h00, e, heQ, hdisc, hc₄,
    horder27, ?_⟩
  rw [← map_nsmul]
  exact heQ

end MazurTorsion.Kubert
