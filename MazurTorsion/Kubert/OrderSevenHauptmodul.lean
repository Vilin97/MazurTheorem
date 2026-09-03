/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenParametrization
public import MazurTorsion.Kubert.OrderSevenCorrespondence

/-!
# The Hauptmodul attached to an exact order-seven point

Tate normalization of an exact order-seven point produces a nonzero
level-seven Hauptmodul.  This file retains the cleared `j`-identity against
the original Weierstrass curve, so consumers need not expose the auxiliary
normal-form coordinate change.
-/
@[expose] public section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The level-seven Hauptmodul obtained by explicit Tate normalization at
an affine point. -/
def orderSevenHauptmodulAt
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  let d := pointTateParameter W x y
  49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)

/-- The explicit Tate-normalization formula at an affine point of exact
order seven is noncuspidal and satisfies the cleared level-seven
Hauptmodul identity. -/
theorem orderSevenHauptmodulAt_spec
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {X Y : ℚ} (hns : W.toAffine.Nonsingular X Y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some X Y hns :
        W.toAffine.Point) = 7) :
    orderSevenHauptmodulAt W X Y ≠ 0 ∧
      orderSevenJNumerator (orderSevenHauptmodulAt W X Y) * W.Δ =
        W.c₄ ^ 3 * orderSevenHauptmodulAt W X Y ^ 7 := by
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some X Y hns
  have hnot : ∀ n : ℕ, ¬(7 ∣ n) → (n : ℕ) • P ≠ 0 := by
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
  have hC₁a₂ :
      (C₁ • W).a₂ = pointTateAlpha W X Y := by
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
  have h7P : (7 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have h7origin :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heP, ← map_nsmul, h7P, map_zero]
  obtain ⟨hc0, hrel⟩ := orderSeven_tate_relation b c hb0 h00
    (WeierstrassCurve.Affine.Point.some_ne_zero h00) h7origin
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    orderSeven_parametrization b c hb0 hc0 hrel
  have hbdc : b = d * c := by
    rw [hbeq, hceq]
    ring
  have hd_ratio : d = b / c := by
    exact (eq_div_iff hc0).mpr hbdc.symm
  have hb_formula :
      b = -pointTateAlpha W X Y ^ 3 / pointTateBeta W X Y ^ 2 := by
    dsimp only [b]
    rw [hC₂a₂, hC₁a₂, hscale]
    field_simp [hbeta, halpha]
  have hc_formula :
      c = (pointTateBeta W X Y - pointTateAlpha W X Y *
          (W.a₁ + 2 * pointTateLambda W X Y)) /
        pointTateBeta W X Y := by
    dsimp only [c]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₂, Units.val_inv_eq_inv_val]
    rw [WeierstrassCurve.variableChange_a₁]
    simp only [C₁, inv_one, Units.val_one, one_mul]
    rw [hlambdaPoint]
    rw [hscale]
    field_simp [hbeta, halpha]
    ring
  have hgamma :
      pointTateBeta W X Y - pointTateAlpha W X Y *
          (W.a₁ + 2 * pointTateLambda W X Y) ≠ 0 := by
    intro hzero
    apply hc0
    rw [hc_formula, hzero]
    simp
  have hratio : b / c = pointTateParameter W X Y := by
    rw [hb_formula, hc_formula]
    simp only [pointTateParameter]
    field_simp [hbeta, hgamma]
  have hdpoint : d = pointTateParameter W X Y :=
    hd_ratio.trans hratio
  have hdisc :
      ((scale : ℚ))⁻¹ ^ 12 * W.Δ = (tateNormalCurve b c).Δ := by
    rw [← hcurve, WeierstrassCurve.variableChange_Δ,
      WeierstrassCurve.variableChange_Δ]
    simp [C₁, C₂]
  have hc₄ :
      ((scale : ℚ))⁻¹ ^ 4 * W.c₄ = (tateNormalCurve b c).c₄ := by
    rw [← hcurve, WeierstrassCurve.variableChange_c₄,
      WeierstrassCurve.variableChange_c₄]
    simp [C₁, C₂]
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hK0
    have hΔzero : (tateNormalCurve b c).Δ = 0 := by
      rw [hbeq, hceq, orderSeven_Δ, hK0]
      ring
    have hΔne : (tateNormalCurve b c).Δ ≠ 0 := by
      rw [← hdisc]
      exact mul_ne_zero (pow_ne_zero 12 (inv_ne_zero hscale0))
        W.isUnit_Δ.ne_zero
    exact hΔne hΔzero
  let B : ℚ := 49 * d * (d - 1) /
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)
  have hBat : orderSevenHauptmodulAt W X Y = B := by
    simp only [orderSevenHauptmodulAt]
    rw [← hdpoint]
  rw [hBat]
  have hB0 : B ≠ 0 := by
    dsimp only [B]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hd0)
        (sub_ne_zero.mpr hd1)) hK
  refine ⟨hB0, ?_⟩
  have hfam := orderSeven_hauptmodul_identity d hd0 hd1 hK
  apply mul_left_cancel₀ (pow_ne_zero 12 (inv_ne_zero hscale0))
  calc
    ((scale : ℚ))⁻¹ ^ 12 * (orderSevenJNumerator B * W.Δ) =
        orderSevenJNumerator B * (((scale : ℚ))⁻¹ ^ 12 * W.Δ) := by ring
    _ = orderSevenJNumerator B * (tateNormalCurve b c).Δ := by
      rw [hdisc]
    _ = orderSevenJNumerator B *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
      rw [hbeq, hceq]
    _ = (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 * B ^ 7 := by
      dsimp only [B, orderSevenJNumerator]
      exact hfam
    _ = (tateNormalCurve b c).c₄ ^ 3 * B ^ 7 := by
      rw [hbeq, hceq]
    _ = (((scale : ℚ))⁻¹ ^ 4 * W.c₄) ^ 3 * B ^ 7 := by
      rw [hc₄]
    _ = ((scale : ℚ))⁻¹ ^ 12 * (W.c₄ ^ 3 * B ^ 7) := by ring

/-- An exact order-seven point supplies a noncuspidal level-seven Hauptmodul
whose cleared `j`-identity is measured against the original curve. -/
theorem exists_orderSevenHauptmodul_of_exactOrder
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (R : W.toAffine.Point) (hR : addOrderOf R = 7) :
    ∃ B : ℚ, B ≠ 0 ∧
      orderSevenJNumerator B * W.Δ = W.c₄ ^ 3 * B ^ 7 := by
  cases R with
  | zero =>
      have hfalse : (1 : ℕ) = 7 := by
        rw [← hR]
        exact (addOrderOf_zero (G := W.toAffine.Point)).symm
      norm_num at hfalse
  | some X Y hns =>
      exact ⟨orderSevenHauptmodulAt W X Y,
        orderSevenHauptmodulAt_spec W hns hR⟩

end MazurTorsion.Kubert
