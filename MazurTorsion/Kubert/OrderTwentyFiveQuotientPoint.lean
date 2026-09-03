/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveNormalizedModel
import MazurTorsion.Kubert.OrderFiveIsogenyDoubling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The explicit order-five quotient point attached to an order-twenty-five point

Normalize the Tate normal form at the fifth multiple of its marked
order-twenty-five point.  The fifth multiple becomes the standard origin on
the diagonal order-five family.  The original generator remains an exact
order-twenty-five point, avoids both kernel poles of the degree-five Vélu map,
and therefore has an exact-order-five image on the quotient.

The named downstream consumer is the quotient-side first-degeneracy bridge in
`OrderTwentyFiveQuotientDegeneracy`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

private def normalizedX
    (W : WeierstrassCurve ℚ) (X Y x : ℚ) : ℚ :=
  (x - X) / (pointTateBeta W X Y / pointTateAlpha W X Y) ^ 2

private def normalizedY
    (W : WeierstrassCurve ℚ) (X Y x y : ℚ) : ℚ :=
  (y - pointTateLambda W X Y * (x - X) - Y) /
    (pointTateBeta W X Y / pointTateAlpha W X Y) ^ 3

private theorem explicitNormalization
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {X Y : ℚ} (hns : W.toAffine.Nonsingular X Y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some X Y hns : W.toAffine.Point) = 5) :
    ∃ (_ : (orderFiveCurve (pointTateC W X Y)).IsElliptic)
      (h00 : (orderFiveCurve (pointTateC W X Y)).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+
        (orderFiveCurve (pointTateC W X Y)).toAffine.Point),
      e (WeierstrassCurve.Affine.Point.some X Y hns) =
          WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        (∀ {x y : ℚ} (hxy : W.toAffine.Nonsingular x y),
            ∃ hnormalized :
                (orderFiveCurve (pointTateC W X Y)).toAffine.Nonsingular
                  (normalizedX W X Y x) (normalizedY W X Y x y),
              e (WeierstrassCurve.Affine.Point.some x y hxy) =
                WeierstrassCurve.Affine.Point.some
                  (normalizedX W X Y x) (normalizedY W X Y x y) hnormalized) ∧
        (orderFiveCurve (pointTateC W X Y)).c₄ ^ 3 * W.Δ =
          W.c₄ ^ 3 * (orderFiveCurve (pointTateC W X Y)).Δ := by
  obtain ⟨hbeta, halpha, hparameters, hc⟩ :=
    pointTate_parameters_eq_of_order_five W hns horder
  let scale : ℚˣ := Units.mk0
    (pointTateBeta W X Y / pointTateAlpha W X Y)
    (div_ne_zero hbeta halpha)
  let C₁ : WeierstrassCurve.VariableChange ℚ :=
    ⟨1, X, pointTateLambda W X Y, Y⟩
  let C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩
  have hscale : (scale : ℚ) =
      pointTateBeta W X Y / pointTateAlpha W X Y := rfl
  have hC₁a₃ : (C₁ • W).a₃ = pointTateBeta W X Y := by
    rw [WeierstrassCurve.variableChange_a₃]
    simp [C₁, pointTateBeta]
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄]
    simp only [C₁, inv_one, Units.val_one, one_pow, one_mul]
    rw [pointTateLambda]
    field_simp [hbeta]
    simp only [pointTateBeta]
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆]
    simp only [C₁, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have hC₁a₂ : (C₁ • W).a₂ = pointTateAlpha W X Y := by
    rw [WeierstrassCurve.variableChange_a₂]
    simp only [C₁, inv_one, Units.val_one, one_pow, one_mul]
    simp only [pointTateAlpha]
    ring
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
  let b : ℚ := -(C₂ • (C₁ • W)).a₂
  let c : ℚ := 1 - (C₂ • (C₁ • W)).a₁
  have hcurveBC : C₂ • (C₁ • W) = tateNormalCurve b c := by
    ext <;> simp [tateNormalCurve, b, c, hC₂a₄, hC₂a₆, hC₂a₂a₃]
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ =
        ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂]
    simp [C₂]
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
    rw [hscale]
    field_simp [hbeta, halpha]
    ring
  have hcurve :
      C₂ • (C₁ • W) = orderFiveCurve (pointTateC W X Y) := by
    rw [hcurveBC, orderFiveCurve, hbFormula, hcFormula, hparameters]
  let e : W.toAffine.Point ≃+
      (orderFiveCurve (pointTateC W X Y)).toAffine.Point :=
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (WeierstrassCurve.Affine.Point.equivOfEq hcurve))
  have hcoordinates :
      ∀ {x y : ℚ} (hxy : W.toAffine.Nonsingular x y),
        ∃ hnormalized :
            (orderFiveCurve (pointTateC W X Y)).toAffine.Nonsingular
              (normalizedX W X Y x) (normalizedY W X Y x y),
          e (WeierstrassCurve.Affine.Point.some x y hxy) =
            WeierstrassCurve.Affine.Point.some
              (normalizedX W X Y x) (normalizedY W X Y x y) hnormalized := by
    intro x y hxy
    let x₁ : ℚ := x - X
    let y₁ : ℚ := y - pointTateLambda W X Y * (x - X) - Y
    let x₂ : ℚ := x₁ / (scale : ℚ) ^ 2
    let y₂ : ℚ := y₁ / (scale : ℚ) ^ 3
    have h₁ : (C₁ • W).toAffine.Nonsingular x₁ y₁ := by
      apply (WeierstrassCurve.Affine.variableChange_nonsingular W C₁ x₁ y₁).mp
      have hx₁ : (C₁.u : ℚ) ^ 2 * x₁ + C₁.r = x := by
        simp [C₁, x₁]
      have hy₁ :
          (C₁.u : ℚ) ^ 3 * y₁ + (C₁.u : ℚ) ^ 2 * C₁.s * x₁ + C₁.t = y := by
        simp [C₁, x₁, y₁]
        ring
      rw [hx₁, hy₁]
      exact hxy
    have hx₂ : (scale : ℚ) ^ 2 * x₂ = x₁ := by
      dsimp only [x₂]
      field_simp [scale.ne_zero]
    have hy₂ : (scale : ℚ) ^ 3 * y₂ = y₁ := by
      dsimp only [y₂]
      field_simp [scale.ne_zero]
    have h₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular x₂ y₂ := by
      apply (WeierstrassCurve.Affine.variableChange_nonsingular
        (C₁ • W) C₂ x₂ y₂).mp
      have hx₂' : (C₂.u : ℚ) ^ 2 * x₂ + C₂.r = x₁ := by
        simpa [C₂] using hx₂
      have hy₂' :
          (C₂.u : ℚ) ^ 3 * y₂ + (C₂.u : ℚ) ^ 2 * C₂.s * x₂ + C₂.t = y₁ := by
        simpa [C₂] using hy₂
      rw [hx₂', hy₂']
      exact h₁
    have hfirst :
        WeierstrassCurve.Affine.Point.equivVariableChange W C₁
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) =
          WeierstrassCurve.Affine.Point.some x y hxy := by
      rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some W
        (by simp [C₁, x₁]) (by simp [C₁, x₁, y₁]; ring)
    have hsecond :
        WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
          WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ := by
      rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some (C₁ • W)
        (by simpa [C₂] using hx₂) (by simpa [C₂] using hy₂)
    have hxNormalized : x₂ = normalizedX W X Y x := by
      simp only [x₂, x₁, normalizedX, hscale]
    have hyNormalized : y₂ = normalizedY W X Y x y := by
      simp only [y₂, y₁, normalizedY, hscale]
    let hnormalized :
        (orderFiveCurve (pointTateC W X Y)).toAffine.Nonsingular
          (normalizedX W X Y x) (normalizedY W X Y x y) := by
      rw [← hxNormalized, ← hyNormalized, ← hcurve]
      exact h₂
    refine ⟨hnormalized, ?_⟩
    simp only [e, AddEquiv.trans_apply, ← hfirst, AddEquiv.symm_apply_apply,
      ← hsecond, WeierstrassCurve.Affine.Point.equivOfEq_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some _ hxNormalized hyNormalized
  obtain ⟨hmarked, hmarkedEq⟩ := hcoordinates hns
  have h00 :
      (orderFiveCurve (pointTateC W X Y)).toAffine.Nonsingular 0 0 :=
    tateNormalCurve_nonsingular_origin _ _ hc
  letI : (C₁ • W).IsElliptic := inferInstance
  letI : (C₂ • (C₁ • W)).IsElliptic := inferInstance
  have hElliptic : (orderFiveCurve (pointTateC W X Y)).IsElliptic :=
    hcurve ▸ inferInstance
  have hdisc :
      ((scale : ℚ))⁻¹ ^ 12 * W.Δ =
        (orderFiveCurve (pointTateC W X Y)).Δ := by
    rw [← hcurve, WeierstrassCurve.variableChange_Δ,
      WeierstrassCurve.variableChange_Δ]
    simp [C₁, C₂]
  have hc₄ :
      ((scale : ℚ))⁻¹ ^ 4 * W.c₄ =
        (orderFiveCurve (pointTateC W X Y)).c₄ := by
    rw [← hcurve, WeierstrassCurve.variableChange_c₄,
      WeierstrassCurve.variableChange_c₄]
    simp [C₁, C₂]
  refine ⟨hElliptic, h00, e, ?_, hcoordinates, ?_⟩
  · rw [hmarkedEq]
    exact WeierstrassCurve.Affine.Point.some_eq_some _
      (by simp [normalizedX]) (by simp [normalizedY])
  · rw [← hc₄, ← hdisc]
    ring

/-- The order-five parameter obtained by normalizing the marked curve at
its fifth multiple. -/
def orderTwentyFiveFiveTateParameter (b c : ℚ) : ℚ :=
  pointTateC
    (tateNormalCurve b c) (tateFiveX b c) (tateFiveY b c)

/-- Abscissa of the original generator after normalization at its fifth
multiple. -/
def orderTwentyFiveFiveNormalizedGeneratorX (b c : ℚ) : ℚ :=
  (0 - tateFiveX b c) /
    (pointTateBeta (tateNormalCurve b c) (tateFiveX b c) (tateFiveY b c) /
      pointTateAlpha (tateNormalCurve b c) (tateFiveX b c) (tateFiveY b c)) ^ 2

/-- Ordinate of the original generator after normalization at its fifth
multiple. -/
def orderTwentyFiveFiveNormalizedGeneratorY (b c : ℚ) : ℚ :=
  (0 - pointTateLambda
        (tateNormalCurve b c) (tateFiveX b c) (tateFiveY b c) *
      (0 - tateFiveX b c) - tateFiveY b c) /
    (pointTateBeta (tateNormalCurve b c) (tateFiveX b c) (tateFiveY b c) /
      pointTateAlpha (tateNormalCurve b c) (tateFiveX b c) (tateFiveY b c)) ^ 3

/-- Abscissa of the residual order-five generator on the explicit quotient. -/
def orderTwentyFiveQuotientGeneratorX (b c : ℚ) : ℚ :=
  orderFiveVeluX (orderTwentyFiveFiveTateParameter b c)
    (orderTwentyFiveFiveNormalizedGeneratorX b c)

/-- Ordinate of the residual order-five generator on the explicit quotient. -/
def orderTwentyFiveQuotientGeneratorY (b c : ℚ) : ℚ :=
  orderFiveVeluY (orderTwentyFiveFiveTateParameter b c)
    (orderTwentyFiveFiveNormalizedGeneratorX b c)
    (orderTwentyFiveFiveNormalizedGeneratorY b c)

/-- The order-five family obtained by normalizing at `5P` is noncuspidal. -/
theorem orderTwentyFiveFiveTateParameter_ne
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    orderTwentyFiveFiveTateParameter b c ≠ 0 ∧
      orderTwentyFiveFiveTateParameter b c ^ 2 -
          11 * orderTwentyFiveFiveTateParameter b c - 1 ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨hc, hbc, hfactor⟩ :=
    orderTwentyFiveNoncuspidalFactor_eq_zero_of_marked_order
      b c hb h00 horder
  obtain ⟨hfiveNs, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hfiveOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) hfiveNs : W.toAffine.Point) = 5 := by
    rw [← hfive, addOrderOf_nsmul' P (by norm_num), horder]
    norm_num
  obtain ⟨hsourceElliptic, -, -, -, -, -⟩ :=
    explicitNormalization W hfiveNs hfiveOrder
  letI : (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).IsElliptic := by
    simpa only [orderTwentyFiveFiveTateParameter, W] using hsourceElliptic
  exact orderFiveCurve_parameters_ne
    (orderTwentyFiveFiveTateParameter b c)

/-- Explicit normalization at `5P` carries the original generator to an
order-twenty-five point on the diagonal order-five family, and its Vélu
image is an exact-order-five point on the quotient. -/
theorem explicitQuotientPointPackage
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ (hc5 : orderTwentyFiveFiveTateParameter b c ≠ 0)
      (hfactor5 :
        orderTwentyFiveFiveTateParameter b c ^ 2 -
            11 * orderTwentyFiveFiveTateParameter b c - 1 ≠ 0)
      (hsource :
        (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).toAffine.Nonsingular
          (orderTwentyFiveFiveNormalizedGeneratorX b c)
          (orderTwentyFiveFiveNormalizedGeneratorY b c))
      (htarget :
        (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c)).toAffine.Nonsingular
          (orderTwentyFiveQuotientGeneratorX b c)
          (orderTwentyFiveQuotientGeneratorY b c)),
      (letI :
          (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).IsElliptic :=
        orderFiveCurve_isElliptic
          (orderTwentyFiveFiveTateParameter b c) hc5 hfactor5
      addOrderOf
          (WeierstrassCurve.Affine.Point.some
            (orderTwentyFiveFiveNormalizedGeneratorX b c)
            (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource :
            (orderFiveCurve
              (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) = 25 ∧
        (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some
              (orderTwentyFiveFiveNormalizedGeneratorX b c)
              (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource :
              (orderFiveCurve
                (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) =
          orderFiveOrigin (orderTwentyFiveFiveTateParameter b c) ∧
        orderTwentyFiveFiveNormalizedGeneratorX b c ≠ 0 ∧
        orderTwentyFiveFiveNormalizedGeneratorX b c ≠
          orderTwentyFiveFiveTateParameter b c ∧
        addOrderOf
          (WeierstrassCurve.Affine.Point.some
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c) htarget :
            (orderFiveVeluTarget
              (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) = 5 ∧
        pointTateBeta
            (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c) ≠ 0 ∧
        pointTateAlpha
            (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c) ≠ 0 ∧
        pointTateB
            (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c) =
          pointTateC
            (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c) ∧
        pointTateC
            (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c) ≠ 0) := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  obtain ⟨hc, hbc, -⟩ :=
    orderTwentyFiveNoncuspidalFactor_eq_zero_of_marked_order
      b c hb h00 horder
  obtain ⟨hfiveNs, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hfiveOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) hfiveNs : W.toAffine.Point) = 5 := by
    rw [← hfive, addOrderOf_nsmul' P (by norm_num), horder]
    norm_num
  obtain ⟨hsourceElliptic, horigin, e, heFive, hcoordinates, -⟩ :=
    explicitNormalization W hfiveNs hfiveOrder
  obtain ⟨hc5, hfactor5⟩ :=
    orderTwentyFiveFiveTateParameter_ne b c hb h00 horder
  letI : (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).IsElliptic := by
    simpa only [orderTwentyFiveFiveTateParameter, W] using hsourceElliptic
  let ePublic : W.toAffine.Point ≃+
      (orderFiveCurve
        (orderTwentyFiveFiveTateParameter b c)).toAffine.Point := e
  obtain ⟨hsourceRaw, heP⟩ := hcoordinates h00
  let hsource :
      (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).toAffine.Nonsingular
        (orderTwentyFiveFiveNormalizedGeneratorX b c)
        (orderTwentyFiveFiveNormalizedGeneratorY b c) := hsourceRaw
  have hePPublic :
      ePublic P = WeierstrassCurve.Affine.Point.some
        (orderTwentyFiveFiveNormalizedGeneratorX b c)
        (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource := heP
  have hsourceOrder :
      addOrderOf
          (WeierstrassCurve.Affine.Point.some
            (orderTwentyFiveFiveNormalizedGeneratorX b c)
            (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource :
            (orderFiveCurve
              (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) = 25 := by
    rw [← hePPublic, AddEquiv.addOrderOf_eq]
    exact horder
  let horiginPublic :
      (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).toAffine.Nonsingular
        0 0 := horigin
  have heFiveAtOrigin :
      ePublic (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) hfiveNs) =
        WeierstrassCurve.Affine.Point.some 0 0 horiginPublic := heFive
  have heFivePublic :
      ePublic (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) hfiveNs) =
        orderFiveOrigin (orderTwentyFiveFiveTateParameter b c) := by
    rw [heFiveAtOrigin]
    exact WeierstrassCurve.Affine.Point.some_eq_some _ rfl rfl
  have hsourceFive :
      (5 : ℕ) •
          (WeierstrassCurve.Affine.Point.some
            (orderTwentyFiveFiveNormalizedGeneratorX b c)
            (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource :
            (orderFiveCurve
              (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) =
        orderFiveOrigin (orderTwentyFiveFiveTateParameter b c) := by
    calc
      (5 : ℕ) •
          (WeierstrassCurve.Affine.Point.some
            (orderTwentyFiveFiveNormalizedGeneratorX b c)
            (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource :
            (orderFiveCurve
              (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) =
        (5 : ℕ) • ePublic P := by rw [hePPublic]
      _ = ePublic ((5 : ℕ) • P) := (map_nsmul ePublic 5 P).symm
      _ = ePublic (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) hfiveNs) := by rw [hfive]
      _ = orderFiveOrigin (orderTwentyFiveFiveTateParameter b c) :=
        heFivePublic
  have himageOrder :=
    addOrderOf_orderFivePointMap_of_orderTwentyFive
      hsourceOrder hsourceFive
  have hnotKernel :
      ¬ OrderFiveKernelX (orderTwentyFiveFiveTateParameter b c)
        (orderTwentyFiveFiveNormalizedGeneratorX b c) := by
    intro hkernel
    have hmapZero :=
      (orderFivePointMap_some_eq_zero_iff hsource).mpr hkernel
    rw [hmapZero, addOrderOf_zero] at himageOrder
    norm_num at himageOrder
  have hx0 : orderTwentyFiveFiveNormalizedGeneratorX b c ≠ 0 :=
    fun h ↦ hnotKernel (Or.inl h)
  have hxc :
      orderTwentyFiveFiveNormalizedGeneratorX b c ≠
        orderTwentyFiveFiveTateParameter b c :=
    fun h ↦ hnotKernel (Or.inr h)
  let htarget :
      (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c)).toAffine.Nonsingular
        (orderTwentyFiveQuotientGeneratorX b c)
        (orderTwentyFiveQuotientGeneratorY b c) :=
    (orderFiveVeluTarget
        (orderTwentyFiveFiveTateParameter b c)).toAffine.equation_iff_nonsingular.mp
      (by simpa only [orderTwentyFiveQuotientGeneratorX,
          orderTwentyFiveQuotientGeneratorY] using
        orderFiveVelu_equation hsource hx0 hxc)
  have himageEq :
      orderFivePointMap (orderTwentyFiveFiveTateParameter b c)
          (WeierstrassCurve.Affine.Point.some
            (orderTwentyFiveFiveNormalizedGeneratorX b c)
            (orderTwentyFiveFiveNormalizedGeneratorY b c) hsource) =
        WeierstrassCurve.Affine.Point.some
          (orderTwentyFiveQuotientGeneratorX b c)
          (orderTwentyFiveQuotientGeneratorY b c) htarget := by
    rw [orderFivePointMap_some_of_not_kernelX hsource hnotKernel]
    rfl
  have htargetOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some
          (orderTwentyFiveQuotientGeneratorX b c)
          (orderTwentyFiveQuotientGeneratorY b c) htarget :
          (orderFiveVeluTarget
            (orderTwentyFiveFiveTateParameter b c)).toAffine.Point) = 5 := by
    rw [← himageEq]
    exact himageOrder
  obtain ⟨hbeta, halpha, hparameters, hparameter⟩ :=
    pointTate_parameters_eq_of_order_five
      (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
      htarget htargetOrder
  exact ⟨hc5, hfactor5, hsource, htarget,
    hsourceOrder, hsourceFive, hx0, hxc,
    htargetOrder, hbeta, halpha, hparameters, hparameter⟩

/-- The point-selected Tate parameter on the explicit quotient satisfies the
same invariant relation as the source order-five parameter.  This pins the
relation to the actual quotient point, rather than to an existentially chosen
Tate normalization. -/
theorem orderTwentyFiveQuotientParameter_relation
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    orderTwentyFiveFiveDivisionRelation
        (orderTwentyFiveFiveTateParameter b c)
        (pointTateC
          (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
          (orderTwentyFiveQuotientGeneratorX b c)
          (orderTwentyFiveQuotientGeneratorY b c)) = 0 := by
  obtain ⟨hc5, hfactor5, -, htarget, -, -, -, -, htargetOrder, -, -, -, -⟩ :=
    explicitQuotientPointPackage b c hb h00 horder
  letI : (orderFiveCurve (orderTwentyFiveFiveTateParameter b c)).IsElliptic :=
    orderFiveCurve_isElliptic
      (orderTwentyFiveFiveTateParameter b c) hc5 hfactor5
  obtain ⟨-, -, -, -, -, hinvariant⟩ :=
    explicitNormalization
      (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
      htarget htargetOrder
  rw [orderFiveCurve_c₄, orderFiveCurve_discriminant,
    orderFiveVeluTarget_discriminant,
    orderFiveVeluTarget_c₄] at hinvariant
  exact sub_eq_zero.mpr hinvariant

end MazurTorsion.Kubert
