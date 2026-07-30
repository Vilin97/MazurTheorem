/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.TateNormalForm

/-!
# The order-three normal form

A rational point of exact order three normalizes to the marked origin of

`y² + a₁xy + a₃y = x³`

by a translation and a shear alone, so the discriminant and `c₄` are
preserved on the nose.  The associated `X₀(3)` hauptmodul value is

`t₃ = (a₁³ - 27a₃)/a₃`,

and the cleared `j`-identity `(t₃+27)(t₃+3)³·Δ = c₄³·t₃` holds on the
normal form.  This is the three-side input to the composite-level
hauptmodul certificates.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The order-three normal form `y² + a₁xy + a₃y = x³`. -/
def threeNormalCurve (a₁ a₃ : ℚ) : WeierstrassCurve ℚ :=
  ⟨a₁, 0, a₃, 0, 0⟩

@[simp] lemma threeNormalCurve_a₁ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).a₁ = a₁ := rfl
@[simp] lemma threeNormalCurve_a₂ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).a₂ = 0 := rfl
@[simp] lemma threeNormalCurve_a₃ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).a₃ = a₃ := rfl
@[simp] lemma threeNormalCurve_a₄ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).a₄ = 0 := rfl
@[simp] lemma threeNormalCurve_a₆ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).a₆ = 0 := rfl

/-- The discriminant of the order-three normal form. -/
lemma threeNormalCurve_Δ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).Δ = a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, threeNormalCurve]
  ring

/-- The invariant `c₄` of the order-three normal form. -/
lemma threeNormalCurve_c₄ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).c₄ = a₁ * (a₁ ^ 3 - 24 * a₃) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    threeNormalCurve]
  ring

/-- On a curve with `a₂ = a₄ = 0` and nonvertical tangent at the origin,
vanishing of thrice the origin forces `a₂ = 0` to be complemented by no
condition; conversely, when `3·(0,0) = 0` on a curve with `a₄ = a₆ = 0`
and `a₃ ≠ 0`, the coefficient `a₂` must vanish. -/
lemma a₂_eq_zero_of_three_nsmul_origin_eq_zero
    (W : WeierstrassCurve ℚ) (ha₄ : W.a₄ = 0)
    (ha₃ : W.a₃ ≠ 0) (h00 : W.toAffine.Nonsingular 0 0)
    (htriple :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 = 0) :
    W.a₂ = 0 := by
  have hvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    simp only [WeierstrassCurve.Affine.negY]
    intro h
    apply ha₃
    linarith
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertical]
    simp only [WeierstrassCurve.Affine.negY, ha₄]
    ring_nf
  have hdouble :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        -WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    rw [← add_eq_zero_iff_eq_neg]
    exact htriple
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' hvertical,
    WeierstrassCurve.Affine.Point.neg_some] at hdouble
  have hx :=
    (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hdouble |>.1
  rw [WeierstrassCurve.Affine.addX, hslope] at hx
  linarith [hx]

/-- Normalization of an exact order-three point to the marked origin of the
order-three normal form.  The translation-shear change has `u = 1`, so the
discriminant and `c₄` are preserved exactly. -/
theorem exists_threeNormalCurve
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (hP0 : P ≠ 0)
    (hP3 : P + P + P = 0) :
    ∃ (a₁ a₃ : ℚ) (_ : a₃ ≠ 0)
      (h00 : (threeNormalCurve a₁ a₃).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (threeNormalCurve a₁ a₃).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        W.Δ = (threeNormalCurve a₁ a₃).Δ ∧
        W.c₄ = (threeNormalCurve a₁ a₃).c₄ := by
  have hP2 : P + P ≠ 0 := by
    intro h2
    apply hP0
    calc
      P = P + P + P - (P + P) := by abel
      _ = 0 := by rw [hP3, h2, sub_zero]
  obtain ⟨X, Y, hns, hPxy⟩ :
      ∃ (X Y : ℚ) (h : W.toAffine.Nonsingular X Y),
        P = WeierstrassCurve.Affine.Point.some X Y h := by
    rcases hcase : P with _ | ⟨X, Y, h⟩
    · exact absurd (by rw [hcase]; rfl) hP0
    · exact ⟨X, Y, h, rfl⟩
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h =>
    hP2 (by
      rw [hPxy]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    linarith
  set s : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hs
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, s, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = W.a₃ + X * W.a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs]
    field_simp
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have hC₁a₃ne : (C₁ • W).a₃ ≠ 0 := by
    rw [hC₁a₃]
    exact htangentDenom
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl hC₁a₃ne⟩
  have hmap₁ :
      WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some, hPxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [hC₁]) (by simp [hC₁])
  have htriple₁ :
      WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 := by
    have := congrArg
      (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm hP3
    rw [map_add, map_add, map_zero] at this
    have hpre :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange
        W C₁).symm_apply_apply _
    rwa [hpre] at this
  have hC₁a₂ : (C₁ • W).a₂ = 0 :=
    a₂_eq_zero_of_three_nsmul_origin_eq_zero
      (C₁ • W) hC₁a₄ hC₁a₃ne h00₁ htriple₁
  have hcurve :
      C₁ • W = threeNormalCurve (C₁ • W).a₁ (C₁ • W).a₃ := by
    ext <;> simp [threeNormalCurve, hC₁a₂, hC₁a₄, hC₁a₆]
  have hΔ : W.Δ = (C₁ • W).Δ := by
    rw [WeierstrassCurve.variableChange_Δ, hC₁]
    simp
  have hc₄ : W.c₄ = (C₁ • W).c₄ := by
    rw [WeierstrassCurve.variableChange_c₄, hC₁]
    simp
  refine ⟨(C₁ • W).a₁, (C₁ • W).a₃, hC₁a₃ne,
    hcurve ▸ h00₁,
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      (WeierstrassCurve.Affine.Point.equivOfEq hcurve), ?_, ?_, ?_⟩
  · have hfirst :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange
        W C₁).symm_apply_apply _
    simp only [AddEquiv.trans_apply, hfirst,
      WeierstrassCurve.Affine.Point.equivOfEq_some]
  · rw [hΔ, hcurve]
    rfl
  · rw [hc₄, hcurve]
    rfl

/-- The cleared `j`-identity for the order-three hauptmodul value on the
normal form: with `t₃ = (a₁³-27a₃)/a₃`,

`(t₃+27)(t₃+3)³ · Δ = c₄³ · t₃`. -/
theorem threeNormal_hauptmodul_identity
    (a₁ a₃ : ℚ) (ha₃ : a₃ ≠ 0) :
    ((a₁ ^ 3 - 27 * a₃) / a₃ + 27) *
        ((a₁ ^ 3 - 27 * a₃) / a₃ + 3) ^ 3 *
        (threeNormalCurve a₁ a₃).Δ =
      (threeNormalCurve a₁ a₃).c₄ ^ 3 *
        ((a₁ ^ 3 - 27 * a₃) / a₃) := by
  rw [threeNormalCurve_Δ, threeNormalCurve_c₄]
  field_simp
  ring

end MazurTorsion.Kubert
