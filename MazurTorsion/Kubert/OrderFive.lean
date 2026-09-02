/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalFormMultiples
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The order-five Tate family

The marked point `(0, 0)` on Tate normal form has exact order five precisely
on the diagonal `b = c`.  This file records that elementary group-law
reduction and the resulting one-parameter family

`y² + (1-c)xy - cy = x³ - cx²`.

The interface is kept in the Kubert layer because it is consumed both by the
exceptional `ZMod 2 × ZMod 10` argument and by the order-twenty-five
five-division normalization.  It asserts no quotient or Fricke transport.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The diagonal Tate-normal-form family with marked point of order five. -/
def orderFiveCurve (c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalCurve c c

@[simp] lemma orderFiveCurve_a₁ (c : ℚ) : (orderFiveCurve c).a₁ = 1 - c := rfl
@[simp] lemma orderFiveCurve_a₂ (c : ℚ) : (orderFiveCurve c).a₂ = -c := rfl
@[simp] lemma orderFiveCurve_a₃ (c : ℚ) : (orderFiveCurve c).a₃ = -c := rfl
@[simp] lemma orderFiveCurve_a₄ (c : ℚ) : (orderFiveCurve c).a₄ = 0 := rfl
@[simp] lemma orderFiveCurve_a₆ (c : ℚ) : (orderFiveCurve c).a₆ = 0 := rfl

/-- Discriminant of the order-five Tate family. -/
theorem orderFiveCurve_discriminant (c : ℚ) :
    (orderFiveCurve c).Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  simp only [orderFiveCurve, tateNormalCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- Exact order five forces the two Tate parameters to coincide. -/
theorem tateNormalCurve_parameters_eq_of_order_five
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5) :
    b = c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨hns₂, hdouble⟩ := two_mul_origin_coordinates b c hb h00
  obtain ⟨hns₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  have hfive : (5 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hsum : P + P + P + (P + P) = 0 := by
    rw [← hfive]
    abel
  rw [htriple, hdouble, add_eq_zero_iff_eq_neg,
    WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq] at hsum
  exact hsum.1.symm

end MazurTorsion.Kubert
