/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalFormMultiples
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
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

/-- The polynomial giving the `c₄` invariant of the order-five family. -/
def orderFiveC4Polynomial (c : ℚ) : ℚ :=
  c ^ 4 - 12 * c ^ 3 + 14 * c ^ 2 + 12 * c + 1

/-- The `c₄` invariant of the order-five Tate family. -/
theorem orderFiveCurve_c₄ (c : ℚ) :
    (orderFiveCurve c).c₄ = orderFiveC4Polynomial c := by
  simp only [orderFiveCurve, tateNormalCurve, orderFiveC4Polynomial,
    WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
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

/-- The marked origin on the diagonal family is killed by five. -/
theorem five_nsmul_orderFiveOrigin
    (c : ℚ) (hc : c ≠ 0)
    (h00 : (orderFiveCurve c).toAffine.Nonsingular 0 0) :
    (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (orderFiveCurve c).toAffine.Point) = 0 := by
  change (5 : ℕ) •
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve c c).toAffine.Point) = 0
  let P : (tateNormalCurve c c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨h₂, hdouble⟩ :=
    two_mul_origin_coordinates c c hc h00
  obtain ⟨h₃, htriple⟩ :=
    three_mul_origin_coordinates c c hc h00
  have hneg :
      WeierstrassCurve.Affine.Point.some c (c - c) h₃ =
        -(WeierstrassCurve.Affine.Point.some c (c * c) h₂) := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some
      (orderFiveCurve c) rfl (by
        simp only [tateNormalCurve,
          WeierstrassCurve.Affine.negY]
        ring)
  calc
    (5 : ℕ) • P = (P + P + P) + (P + P) := by abel
    _ = WeierstrassCurve.Affine.Point.some c (c - c) h₃ +
          WeierstrassCurve.Affine.Point.some c (c * c) h₂ := by
        rw [htriple, hdouble]
    _ = 0 := by rw [hneg, neg_add_cancel]

/-- An affine point whose abscissa is one of the two poles of the paired
Vélu formula belongs to the marked order-five subgroup. -/
theorem five_nsmul_eq_zero_of_orderFive_kernel_abscissa
    {c x y : ℚ} (hc : c ≠ 0)
    (hP : (orderFiveCurve c).toAffine.Nonsingular x y)
    (hx : x = 0 ∨ x = c) :
    (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y hP :
          (orderFiveCurve c).toAffine.Point) = 0 := by
  change (tateNormalCurve c c).toAffine.Nonsingular x y at hP
  change (5 : ℕ) •
      (WeierstrassCurve.Affine.Point.some x y hP :
        (tateNormalCurve c c).toAffine.Point) = 0
  let h00 : (tateNormalCurve c c).toAffine.Nonsingular 0 0 :=
    tateNormalCurve_nonsingular_origin c c hc
  let O : (tateNormalCurve c c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveO : (5 : ℕ) • O = 0 :=
    five_nsmul_orderFiveOrigin c hc h00
  obtain ⟨h₂, hdouble⟩ :=
    two_mul_origin_coordinates c c hc h00
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  rcases hx with hx0 | hxc
  · subst x
    have hy : y = 0 ∨ y = c := by
      have hyprod : y * (y - c) = 0 := by
        simp only [tateNormalCurve_a₁, tateNormalCurve_a₂,
          tateNormalCurve_a₃, tateNormalCurve_a₄,
          tateNormalCurve_a₆] at hcurve
        linear_combination hcurve
      rcases mul_eq_zero.mp hyprod with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    rcases hy with hy0 | hyc
    · subst y
      simpa only [O] using hfiveO
    · have hneg :
          (WeierstrassCurve.Affine.Point.some 0 y hP :
              (tateNormalCurve c c).toAffine.Point) = -O := by
        change (WeierstrassCurve.Affine.Point.some 0 y hP :
            (tateNormalCurve c c).toAffine.Point) =
          -(WeierstrassCurve.Affine.Point.some 0 0 h00)
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some_eq_some
          (tateNormalCurve c c) rfl (by
            simp only [tateNormalCurve,
              WeierstrassCurve.Affine.negY]
            calc
              y = c := hyc
              _ = -0 - (1 - c) * 0 - -c := by ring)
      rw [hneg]
      calc
        (5 : ℕ) • (-O) = -((5 : ℕ) • O) := by abel
        _ = 0 := by rw [hfiveO, neg_zero]
  · subst x
    have hy : y = 0 ∨ y = c * c := by
      have hyprod : y * (y - c * c) = 0 := by
        simp only [tateNormalCurve_a₁, tateNormalCurve_a₂,
          tateNormalCurve_a₃, tateNormalCurve_a₄,
          tateNormalCurve_a₆] at hcurve
        linear_combination hcurve
      rcases mul_eq_zero.mp hyprod with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    have hfiveDouble :
        (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some c (c * c) h₂ :
              (tateNormalCurve c c).toAffine.Point) = 0 := by
      rw [← hdouble]
      change (5 : ℕ) • (O + O) = 0
      rw [nsmul_add, hfiveO, zero_add]
    rcases hy with hy0 | hyc
    · have hneg :
          (WeierstrassCurve.Affine.Point.some c y hP :
              (tateNormalCurve c c).toAffine.Point) =
            -(WeierstrassCurve.Affine.Point.some c (c * c) h₂) := by
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some_eq_some
          (tateNormalCurve c c) rfl (by
            simp only [tateNormalCurve,
              WeierstrassCurve.Affine.negY]
            rw [hy0]
            ring)
      rw [hneg]
      calc
        (5 : ℕ) •
            (-(WeierstrassCurve.Affine.Point.some c (c * c) h₂)) =
              -((5 : ℕ) •
                (WeierstrassCurve.Affine.Point.some c (c * c) h₂)) := by
                  abel
        _ = 0 := by rw [hfiveDouble, neg_zero]
    · have heq :
          (WeierstrassCurve.Affine.Point.some c y hP :
              (tateNormalCurve c c).toAffine.Point) =
            WeierstrassCurve.Affine.Point.some c (c * c) h₂ := by
        exact WeierstrassCurve.Affine.Point.some_eq_some
          (tateNormalCurve c c) rfl hyc
      rw [heq]
      exact hfiveDouble

/-- Explicit Tate normalization at an affine point of exact order five
produces equal, nonzero Tate parameters. This pins down the parameter chosen
by the normalization, rather than merely asserting that some order-five
parameter exists. -/
theorem pointTate_parameters_eq_of_order_five
    (W : WeierstrassCurve ℚ)
    {X Y : ℚ} (hns : W.toAffine.Nonsingular X Y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some X Y hns :
        W.toAffine.Point) = 5) :
    pointTateBeta W X Y ≠ 0 ∧
      pointTateAlpha W X Y ≠ 0 ∧
      pointTateB W X Y = pointTateC W X Y ∧
      pointTateC W X Y ≠ 0 := by
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some X Y hns
  have hnot : ∀ n : ℕ, ¬(5 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hP2 : P + P ≠ 0 := by
    intro h
    exact hnot 2 (by norm_num) (by simpa [two_nsmul] using h)
  have hP3 : P + P + P ≠ 0 := by
    intro h
    exact hnot 3 (by norm_num) (by
      rw [show (3 : ℕ) • P = P + P + P by abel]
      exact h)
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h ↦
    hP2 (by
      dsimp only [P]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have hbeta : pointTateBeta W X Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    unfold pointTateBeta at h
    linarith
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    simpa only [pointTateBeta] using hbeta
  set lambda : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hlambda
  have hlambdaPoint : lambda = pointTateLambda W X Y := by
    rw [hlambda]
    rfl
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, lambda, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = pointTateBeta W X Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp [pointTateBeta]
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hlambda]
    field_simp [htangentDenom]
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have hC₁a₂ : (C₁ • W).a₂ = pointTateAlpha W X Y := by
    rw [WeierstrassCurve.variableChange_a₂, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    simp only [pointTateAlpha]
    rw [← hlambdaPoint]
    ring
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl (by rw [hC₁a₃]; exact hbeta)⟩
  have hmap₁ :
      WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
    dsimp only [P]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [C₁]) (by simp [C₁])
  have halpha : pointTateAlpha W X Y ≠ 0 := by
    rw [← hC₁a₂]
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact hbeta) h00₁
    have himage :=
      congrArg (WeierstrassCurve.Affine.Point.equivVariableChange W C₁)
        htriple
    rwa [map_add, map_add, map_zero, hmap₁] at himage
  let scale : ℚˣ := Units.mk0
    (pointTateBeta W X Y / pointTateAlpha W X Y)
    (div_ne_zero hbeta halpha)
  let C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩
  have hscale : (scale : ℚ) =
      pointTateBeta W X Y / pointTateAlpha W X Y := rfl
  have hscale0 : (scale : ℚ) ≠ 0 := scale.ne_zero
  let b : ℚ := -(C₂ • (C₁ • W)).a₂
  let c : ℚ := 1 - (C₂ • (C₁ • W)).a₁
  have hC₂a₄ : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄]
    simp [C₂, hC₁a₄]
  have hC₂a₆ : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆]
    simp [C₂, hC₁a₆]
  have hC₂a₂a₃ :
      (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₂]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [hC₁a₃, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
    ring
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ =
        ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂]
    simp [C₂]
  have hC₂a₂ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hC₂a₂, hC₁a₂]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hscale0)) halpha
  have hb0 : b ≠ 0 := by
    dsimp only [b]
    exact neg_ne_zero.mpr hC₂a₂ne
  have hcurve : C₂ • (C₁ • W) = tateNormalCurve b c := by
    ext <;> simp [tateNormalCurve, b, c, hC₂a₄, hC₂a₆,
      hC₂a₂a₃]
  have h00₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₂a₆, Or.inl (by rw [hC₂a₂a₃]; exact hC₂a₂ne)⟩
  let h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0 :=
    hcurve ▸ h00₂
  let e : W.toAffine.Point ≃+ (tateNormalCurve b c).toAffine.Point :=
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (WeierstrassCurve.Affine.Point.equivOfEq hcurve))
  have heP : e P = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    have hfirst :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [C₂]) (by simp [C₂])
    simp only [e, AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, WeierstrassCurve.Affine.Point.equivOfEq_some]
  have horderOrigin :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact horder
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb0 h00 horderOrigin
  have hbFormula : b = pointTateB W X Y := by
    dsimp only [b, pointTateB]
    rw [hC₂a₂, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
  have hcFormula : c = pointTateC W X Y := by
    dsimp only [c, pointTateC]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₁, inv_one, Units.val_one, one_mul]
    rw [hlambdaPoint, hscale]
    field_simp [hbeta, halpha]
    ring
  have hparameters : pointTateB W X Y = pointTateC W X Y :=
    hbFormula.symm.trans (hbc.trans hcFormula)
  refine ⟨hbeta, halpha, hparameters, ?_⟩
  rw [← hparameters, ← hbFormula]
  exact hb0

/-- An exact order-five point admits order-five Tate normalization while
retaining the invariant scales and the marked-point equivalence. -/
theorem exists_orderFiveCurve_scaled
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (horder : addOrderOf P = 5) :
    ∃ (c u : ℚ) (_ : c ≠ 0) (_ : c ^ 2 - 11 * c - 1 ≠ 0)
      (_ : u ≠ 0)
      (h00 : (orderFiveCurve c).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (orderFiveCurve c).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * W.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * W.c₄ = (orderFiveCurve c).c₄ ∧
        u ^ 6 * W.c₆ = (orderFiveCurve c).c₆ := by
  have hnot : ∀ n : ℕ, ¬ (5 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hP2 : P + P ≠ 0 := by
    intro hzero
    apply hnot 2 (by norm_num)
    simpa only [two_nsmul] using hzero
  have hP3 : P + P + P ≠ 0 := by
    intro hzero
    apply hnot 3 (by norm_num)
    calc
      (3 : ℕ) • P = P + P + P := by abel
      _ = 0 := hzero
  obtain ⟨b, c, u, hu, hb, h00, e, heP, hdisc, hc₄, hc₆⟩ :=
    exists_tateNormalCurve_scaled W P hP2 hP3
  have horderOrigin :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 5 := by
    rw [← heP, AddEquiv.addOrderOf_eq]
    exact horder
  have hbc : b = c :=
    tateNormalCurve_parameters_eq_of_order_five b c hb h00 horderOrigin
  subst b
  have hfactor : c ^ 2 - 11 * c - 1 ≠ 0 := by
    intro hzero
    have hDeltaZero : (orderFiveCurve c).Δ = 0 := by
      rw [orderFiveCurve_discriminant, hzero, mul_zero]
    have hdiscFive : u ^ 12 * W.Δ = (orderFiveCurve c).Δ := by
      exact hdisc
    have hDeltaNe : (orderFiveCurve c).Δ ≠ 0 := by
      rw [← hdiscFive]
      exact mul_ne_zero (pow_ne_zero 12 hu) W.isUnit_Δ.ne_zero
    exact hDeltaNe hDeltaZero
  exact ⟨c, u, hb, hfactor, hu, h00, e, heP, hdisc, hc₄, hc₆⟩

/-- Eliminating the normalization scale gives the cleared `j`-identity
attached to an exact order-five point.  This is the invariant interface used
to compare the original marked five-subgroup with a residual five-subgroup
on an isogenous quotient. -/
theorem exists_orderFiveParameter_relation_of_exactOrder
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (horder : addOrderOf P = 5) :
    ∃ c : ℚ, c ≠ 0 ∧ c ^ 2 - 11 * c - 1 ≠ 0 ∧
      orderFiveC4Polynomial c ^ 3 * W.Δ =
        W.c₄ ^ 3 * (c ^ 5 * (c ^ 2 - 11 * c - 1)) := by
  obtain ⟨c, u, hc, hfactor, -, -, -, -, hdisc, hc₄, -⟩ :=
    exists_orderFiveCurve_scaled W P horder
  refine ⟨c, hc, hfactor, ?_⟩
  calc
    orderFiveC4Polynomial c ^ 3 * W.Δ =
        (orderFiveCurve c).c₄ ^ 3 * W.Δ := by
      rw [orderFiveCurve_c₄]
    _ = (u ^ 4 * W.c₄) ^ 3 * W.Δ := by rw [hc₄]
    _ = W.c₄ ^ 3 * (u ^ 12 * W.Δ) := by ring
    _ = W.c₄ ^ 3 * (orderFiveCurve c).Δ := by rw [hdisc]
    _ = W.c₄ ^ 3 *
        (c ^ 5 * (c ^ 2 - 11 * c - 1)) := by
      rw [orderFiveCurve_discriminant]

end MazurTorsion.Kubert
