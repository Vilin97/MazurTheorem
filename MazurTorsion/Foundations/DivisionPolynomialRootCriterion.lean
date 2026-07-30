/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.OddPrimeFullTorsion
import MazurTorsion.Foundations.ThreeTorsion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Division-polynomial roots from scalar multiplication

This file proves the forward division-polynomial root criterion at `5` and `7`. The proof uses
only the affine group law and the first few univariate division polynomials.
-/

namespace MazurTorsion.DivisionPolynomialRootCriterion

open Polynomial
open scoped WeierstrassCurve.Affine

private lemma exists_coordinates_of_ne_zero
    (W : WeierstrassCurve ℚ) (P : W.toAffine.Point)
    (hP : P ≠ 0) :
    ∃ x y, ∃ h : W.toAffine.Nonsingular x y,
      P = WeierstrassCurve.Affine.Point.some x y h := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h => exact ⟨x, y, h, rfl⟩

private lemma double_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    Polynomial.eval x (W.Φ 2) =
      x₂ * Polynomial.eval x (W.ΨSq 2) := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  let slope := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hx₂ : W.toAffine.addX x x slope = x₂ := by
    have hsum :
        WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP =
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (WeierstrassCurve.Affine.Point.some.inj
      (hadd.symm.trans hsum)).1
  have hden : y - W.toAffine.negY x y =
      2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hden_ne : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [← hden]
    exact sub_ne_zero.mpr hy
  have hslope :
      slope =
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
          (2 * y + W.a₁ * x + W.a₃) := by
    dsimp [slope]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hden]
  have hslope_mul :
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hslope, div_mul_cancel₀ _ hden_ne]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hD :
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        Polynomial.eval x (W.ΨSq 2) := by
    simp only [WeierstrassCurve.ΨSq_two, WeierstrassCurve.Ψ₂Sq,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hcurve
  have hψ₃ :=
    ThreeTorsion.three_division_tangent_identity hcurve hslope_mul
  have hx₂' : slope ^ 2 + W.a₁ * slope - W.a₂ - 2 * x = x₂ := by
    simp only [WeierstrassCurve.Affine.addX] at hx₂
    linear_combination hx₂
  have hψ₃eval :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) := by
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hψ₃
  have hΦ :
      Polynomial.eval x (W.Φ 2) =
        x * Polynomial.eval x (W.ΨSq 2) -
          Polynomial.eval x W.Ψ₃ := by
    simp only [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  calc
    Polynomial.eval x (W.Φ 2) =
        x * Polynomial.eval x (W.ΨSq 2) -
          Polynomial.eval x W.Ψ₃ := hΦ
    _ = x * Polynomial.eval x (W.ΨSq 2) +
        (2 * y + W.a₁ * x + W.a₃) ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) := by
            rw [hψ₃eval]
            ring
    _ = x * Polynomial.eval x (W.ΨSq 2) +
        Polynomial.eval x (W.ΨSq 2) * (x₂ - x) := by
            rw [hD]
            linear_combination
              Polynomial.eval x (W.ΨSq 2) * hx₂'
    _ = x₂ * Polynomial.eval x (W.ΨSq 2) := by ring

private lemma preΨ_four_double_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    Polynomial.eval x W.preΨ₄ =
      (2 * y + W.a₁ * x + W.a₃) ^ 3 *
        (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  let slope := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hsum :
      WeierstrassCurve.Affine.Point.some x y hP +
          WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    simpa [two_nsmul] using hdouble
  have hcoords :=
    WeierstrassCurve.Affine.Point.some.inj (hadd.symm.trans hsum)
  have hx₂ : slope ^ 2 + W.a₁ * slope - W.a₂ - 2 * x = x₂ := by
    have hx := hcoords.1
    simp only [WeierstrassCurve.Affine.addX] at hx
    linear_combination hx
  have hy₂ :
      y₂ = -(slope * (x₂ - x) + y) - W.a₁ * x₂ - W.a₃ := by
    have hycoord := hcoords.2
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY] at hycoord
    rw [hcoords.1] at hycoord
    change
      -(slope * (x₂ - x) + y) - W.a₁ * x₂ - W.a₃ = y₂
      at hycoord
    exact hycoord.symm
  have hden : y - W.toAffine.negY x y =
      2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hslope_mul :
      slope * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    dsimp [slope]
    rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
      div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hψ :=
    ThreeTorsion.three_division_tangent_identity hcurve hslope_mul
  have hψeval :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 * (x₂ - x) := by
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hψ -
      (2 * y + W.a₁ * x + W.a₃) ^ 2 * hx₂
  have hvertical :
      2 * y₂ + W.a₁ * x₂ + W.a₃ =
        -(2 * slope + W.a₁) * (x₂ - x) -
          (2 * y + W.a₁ * x + W.a₃) := by
    linear_combination 2 * hy₂
  have hpre :
      Polynomial.eval x W.preΨ₄ =
        (2 * y + W.a₁ * x + W.a₃) *
            (2 * slope + W.a₁) * Polynomial.eval x W.Ψ₃ -
          (2 * y + W.a₁ * x + W.a₃) ^ 4 := by
    simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination
      -2 * (3 * x ^ 4 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 3 +
        3 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 +
        3 * (W.a₃ ^ 2 + 4 * W.a₆) * x +
        (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ -
          W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 -
          W.a₄ ^ 2)) * hslope_mul +
      8 * ((2 * y + W.a₁ * x + W.a₃) ^ 2 -
        2 * (y ^ 2 + W.a₁ * x * y + W.a₃ * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))) * hcurve
  calc
    Polynomial.eval x W.preΨ₄ =
        (2 * y + W.a₁ * x + W.a₃) *
            (2 * slope + W.a₁) * Polynomial.eval x W.Ψ₃ -
          (2 * y + W.a₁ * x + W.a₃) ^ 4 := hpre
    _ = (2 * y + W.a₁ * x + W.a₃) ^ 3 *
        (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
          rw [hψeval, hvertical]
          ring

private lemma two_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 2) =
      x * Polynomial.eval x (W.ΨSq 2) -
        Polynomial.eval x W.Ψ₃ := by
  simp only [WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma triple_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ x₃ y₃ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₃ : W.toAffine.Nonsingular x₃ y₃)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂)
    (htriple :
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃) :
    Polynomial.eval x (W.Φ 3) =
      x₃ * Polynomial.eval x (W.ΨSq 3) := by
  let P := WeierstrassCurve.Affine.Point.some x y hP
  let P₂ := WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have hx : x ≠ x₂ := by
    intro hx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hx with heq | heq
    · apply hP_ne
      have htwice : (2 : ℕ) • P = P :=
        hdouble.trans heq.symm
      rw [two_nsmul] at htwice
      have hcancel : P + P = P + 0 := by
        exact htwice.trans (add_zero P).symm
      exact add_left_cancel hcancel
    · have hneg : P = -((2 : ℕ) • P) := by
        rw [hdouble]
        exact heq
      have hzero : (3 : ℕ) • P = 0 := by
        have hsum : P + (2 : ℕ) • P = 0 :=
          (add_eq_zero_iff_eq_neg).2 hneg
        rw [show (3 : ℕ) = 1 + 2 by norm_num,
          add_nsmul, one_nsmul]
        exact hsum
      change (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ at htriple
      rw [hzero] at htriple
      exact WeierstrassCurve.Affine.Point.some_ne_zero hP₃
        htriple.symm
  have hadd :
      P + P₂ = WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ := by
    change
      WeierstrassCurve.Affine.Point.some x y hP +
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃
    rw [← hdouble]
    rw [← htriple]
    rw [show (3 : ℕ) = 1 + 2 by norm_num,
      add_nsmul, one_nsmul]
  have hadd_formula :=
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := W.toAffine) (h₁ := hP) (h₂ := hP₂) hx
  have hx_add :
      W.toAffine.addX x x₂ (W.toAffine.slope x x₂ y y₂) = x₃ :=
    (WeierstrassCurve.Affine.Point.some.inj
      (hadd_formula.symm.trans hadd)).1
  have hsub :
      P + (-P₂) = -P := by
    change
      WeierstrassCurve.Affine.Point.some x y hP +
          (-WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) =
        -WeierstrassCurve.Affine.Point.some x y hP
    rw [← hdouble]
    rw [two_nsmul]
    abel
  have hP₂neg :
      W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
    (W.toAffine.nonsingular_neg x₂ y₂).mpr hP₂
  have hsub_formula :=
    WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := W.toAffine) (h₁ := hP) (h₂ := hP₂neg) hx
  have hx_sub :
      W.toAffine.addX x x₂
          (W.toAffine.slope x x₂ y (W.toAffine.negY x₂ y₂)) = x := by
    have heq := hsub_formula.symm.trans hsub
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have haddX :=
    W.toAffine.addX_eq_addX_negY_sub y y₂ hx
  rw [hx_add, hx_sub] at haddX
  have hvertical :
      y - W.toAffine.negY x y =
        2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hvertical₂ :
      y₂ - W.toAffine.negY x₂ y₂ =
        2 * y₂ + W.a₁ * x₂ + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  rw [hvertical, hvertical₂] at haddX
  have hden_ne : x₂ - x ≠ 0 :=
    sub_ne_zero.mpr hx.symm
  have hsecant :
      (x₂ - x) ^ 2 * (x - x₃) =
        (2 * y + W.a₁ * x + W.a₃) *
          (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
    field_simp [hden_ne] at haddX
    linear_combination -haddX
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hD :
      Polynomial.eval x (W.ΨSq 2) =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simp only [WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination -4 * hcurve
  have hA :=
    double_abscissa_formula W hP hP₂ hdouble
  have htwo := two_cross_identity W x
  have hψ :
      Polynomial.eval x W.Ψ₃ =
        -(2 * y + W.a₁ * x + W.a₃) ^ 2 * (x₂ - x) := by
    linear_combination htwo - hA -
      (x₂ - x) * hD
  have hpre :=
    preΨ_four_double_formula W hP hP₂ hdouble
  have hD₂ :
      Polynomial.eval x W.Ψ₂Sq =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simpa only [WeierstrassCurve.ΨSq_two] using hD
  simp only [WeierstrassCurve.Φ_three,
    WeierstrassCurve.ΨSq_three, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hpre, hD₂, hψ]
  linear_combination
    (2 * y + W.a₁ * x + W.a₃) ^ 4 * hsecant

private lemma four_Φ_composition
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    let A := Polynomial.eval x (W.Φ 2)
    let D := Polynomial.eval x (W.ΨSq 2)
    Polynomial.eval x (W.Φ 4) =
      A ^ 4 - W.b₄ * A ^ 2 * D ^ 2 -
        2 * W.b₆ * A * D ^ 3 - W.b₈ * D ^ 4 := by
  dsimp
  simp only [WeierstrassCurve.Φ_four, WeierstrassCurve.Φ_two,
    WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private lemma four_ΨSq_composition
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    let A := Polynomial.eval x (W.Φ 2)
    let D := Polynomial.eval x (W.ΨSq 2)
    Polynomial.eval x (W.ΨSq 4) =
      4 * A ^ 3 * D + W.b₂ * A ^ 2 * D ^ 2 +
        2 * W.b₄ * A * D ^ 3 + W.b₆ * D ^ 4 := by
  dsimp
  simp only [WeierstrassCurve.ΨSq_four,
    WeierstrassCurve.Φ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.preΨ₄,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma quadruple_abscissa_formula
    (W : WeierstrassCurve ℚ) {x y x₂ y₂ x₄ y₄ : ℚ}
    (hP : W.toAffine.Nonsingular x y)
    (hP₂ : W.toAffine.Nonsingular x₂ y₂)
    (hP₄ : W.toAffine.Nonsingular x₄ y₄)
    (hdouble :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂)
    (hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄) :
    Polynomial.eval x (W.Φ 4) =
      x₄ * Polynomial.eval x (W.ΨSq 4) := by
  have hA :=
    double_abscissa_formula W hP hP₂ hdouble
  have hA₂ :=
    double_abscissa_formula W hP₂ hP₄ hdouble₂
  have hΦ :
      Polynomial.eval x (W.Φ 4) =
        Polynomial.eval x (W.ΨSq 2) ^ 4 *
          Polynomial.eval x₂ (W.Φ 2) := by
    rw [four_Φ_composition]
    rw [hA]
    simp only [WeierstrassCurve.Φ_two, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  have hΨ :
      Polynomial.eval x (W.ΨSq 4) =
        Polynomial.eval x (W.ΨSq 2) ^ 4 *
          Polynomial.eval x₂ (W.ΨSq 2) := by
    rw [four_ΨSq_composition]
    rw [hA]
    simp only [WeierstrassCurve.ΨSq_two,
      WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [hΦ, hA₂, hΨ]
  ring

private lemma five_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 4) =
      x * Polynomial.eval x (W.ΨSq 4) -
        Polynomial.eval x W.Ψ₃ *
          Polynomial.eval x (W.preΨ' 5) := by
  have hpre :
      W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      W.preΨ'_odd 0]
    norm_num
  rw [hpre]
  simp only [WeierstrassCurve.Φ_four,
    WeierstrassCurve.ΨSq_four, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

private lemma seven_cross_identity
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    Polynomial.eval x (W.Φ 4) *
          Polynomial.eval x (W.ΨSq 3) -
        Polynomial.eval x (W.Φ 3) *
          Polynomial.eval x (W.ΨSq 4) =
      -Polynomial.eval x (W.preΨ' 7) := by
  have hfive :
      W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      W.preΨ'_odd 0]
    norm_num
  have hseven :
      W.preΨ' 7 =
        (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 -
          W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
    rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num,
      W.preΨ'_odd 1]
    norm_num [hfive]
  rw [hseven]
  simp only [WeierstrassCurve.Φ_four,
    WeierstrassCurve.Φ_three, WeierstrassCurve.ΨSq_four,
    WeierstrassCurve.ΨSq_three, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- The forward fifth-division-polynomial root criterion over `ℚ`. -/
theorem hasDivisionPolynomialRootCriterion_five
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    OddPrimeFullTorsion.HasDivisionPolynomialRootCriterion W 5 := by
  intro x y hP hfive
  let P := WeierstrassCurve.Affine.Point.some x y hP
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    apply hP_ne
    have hsplit :
        (5 : ℕ) • P = (2 : ℕ) • P + (2 : ℕ) • P + P := by
      rw [show (5 : ℕ) = 2 + 2 + 1 by norm_num,
        add_nsmul, add_nsmul, one_nsmul]
    change (5 : ℕ) • P = 0 at hfive
    rw [hsplit, htwo, zero_add, zero_add] at hfive
    exact hfive
  have hfour_ne : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    apply hP_ne
    have hsplit : (5 : ℕ) • P = (4 : ℕ) • P + P := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num,
        add_nsmul, one_nsmul]
    change (5 : ℕ) • P = 0 at hfive
    rw [hsplit, hfour, zero_add] at hfive
    exact hfive
  obtain ⟨x₂, y₂, hP₂, hdouble⟩ :=
    exists_coordinates_of_ne_zero W ((2 : ℕ) • P) htwo_ne
  obtain ⟨x₄, y₄, hP₄, hfour⟩ :=
    exists_coordinates_of_ne_zero W ((4 : ℕ) • P) hfour_ne
  have hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ := by
    rw [← hdouble, ← hfour, ← mul_nsmul]
  have hfour_neg : (4 : ℕ) • P = -P := by
    apply (add_eq_zero_iff_eq_neg).mp
    have hsplit : (5 : ℕ) • P = (4 : ℕ) • P + P := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num,
        add_nsmul, one_nsmul]
    rw [← hsplit]
    exact hfive
  have hx₄ : x₄ = x := by
    have heq :
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ = -P :=
      hfour.symm.trans hfour_neg
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have hcoordinate :=
    quadruple_abscissa_formula W hP hP₂ hP₄ hdouble hdouble₂
  rw [hx₄] at hcoordinate
  have hψ₃_ne : Polynomial.eval x W.Ψ₃ ≠ 0 := by
    intro hψ₃
    have hthree :
        (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 :=
      (ThreeTorsion.three_nsmul_some_eq_zero_iff W hP).2 hψ₃
    apply htwo_ne
    have hsplit :
        (5 : ℕ) • P = (3 : ℕ) • P + (2 : ℕ) • P := by
      rw [show (5 : ℕ) = 3 + 2 by norm_num, add_nsmul]
    change (3 : ℕ) • P = 0 at hthree
    change (5 : ℕ) • P = 0 at hfive
    rw [hsplit, hthree, zero_add] at hfive
    exact hfive
  have hcross := five_cross_identity W x
  have hproduct :
      Polynomial.eval x W.Ψ₃ *
        Polynomial.eval x (W.preΨ' 5) = 0 := by
    linear_combination hcross - hcoordinate
  exact (mul_eq_zero.mp hproduct).resolve_left hψ₃_ne

/-- The forward seventh-division-polynomial root criterion over `ℚ`. -/
theorem hasDivisionPolynomialRootCriterion_seven
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    OddPrimeFullTorsion.HasDivisionPolynomialRootCriterion W 7 := by
  intro x y hP hseven
  let P := WeierstrassCurve.Affine.Point.some x y hP
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    apply hP_ne
    have hsplit :
        (7 : ℕ) • P =
          (2 : ℕ) • P + (2 : ℕ) • P + (2 : ℕ) • P + P := by
      rw [show (7 : ℕ) = 2 + 2 + 2 + 1 by norm_num,
        add_nsmul, add_nsmul, add_nsmul, one_nsmul]
    change (7 : ℕ) • P = 0 at hseven
    rw [hsplit, htwo, zero_add, zero_add, zero_add] at hseven
    exact hseven
  have hthree_ne : (3 : ℕ) • P ≠ 0 := by
    intro hthree
    apply hP_ne
    have hsplit :
        (7 : ℕ) • P = (3 : ℕ) • P + (3 : ℕ) • P + P := by
      rw [show (7 : ℕ) = 3 + 3 + 1 by norm_num,
        add_nsmul, add_nsmul, one_nsmul]
    change (7 : ℕ) • P = 0 at hseven
    rw [hsplit, hthree, zero_add, zero_add] at hseven
    exact hseven
  have hfour_ne : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    apply hP_ne
    have hsplitSeven :
        (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by
      rw [show (7 : ℕ) = 4 + 3 by norm_num, add_nsmul]
    have hthree : (3 : ℕ) • P = 0 := by
      change (7 : ℕ) • P = 0 at hseven
      rw [hsplitSeven, hfour, zero_add] at hseven
      exact hseven
    have hsplitFour :
        (4 : ℕ) • P = (3 : ℕ) • P + P := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num,
        add_nsmul, one_nsmul]
    rw [hsplitFour, hthree, zero_add] at hfour
    exact hfour
  obtain ⟨x₂, y₂, hP₂, hdouble⟩ :=
    exists_coordinates_of_ne_zero W ((2 : ℕ) • P) htwo_ne
  obtain ⟨x₃, y₃, hP₃, htriple⟩ :=
    exists_coordinates_of_ne_zero W ((3 : ℕ) • P) hthree_ne
  obtain ⟨x₄, y₄, hP₄, hfour⟩ :=
    exists_coordinates_of_ne_zero W ((4 : ℕ) • P) hfour_ne
  have hdouble₂ :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ =
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ := by
    rw [← hdouble, ← hfour, ← mul_nsmul]
  have hfour_neg_three :
      (4 : ℕ) • P = -((3 : ℕ) • P) := by
    apply (add_eq_zero_iff_eq_neg).mp
    have hsplit :
        (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by
      rw [show (7 : ℕ) = 4 + 3 by norm_num, add_nsmul]
    rw [← hsplit]
    exact hseven
  have hx₄₃ : x₄ = x₃ := by
    have heq :
        WeierstrassCurve.Affine.Point.some x₄ y₄ hP₄ =
          -WeierstrassCurve.Affine.Point.some x₃ y₃ hP₃ := by
      rw [← hfour, ← htriple]
      exact hfour_neg_three
    exact (WeierstrassCurve.Affine.Point.some.inj heq).1
  have hcoordinate₃ :=
    triple_abscissa_formula W hP hP₂ hP₃ hdouble htriple
  have hcoordinate₄ :=
    quadruple_abscissa_formula W hP hP₂ hP₄ hdouble hdouble₂
  have hleft :
      Polynomial.eval x (W.Φ 4) *
            Polynomial.eval x (W.ΨSq 3) -
          Polynomial.eval x (W.Φ 3) *
            Polynomial.eval x (W.ΨSq 4) = 0 := by
    rw [hcoordinate₄, hcoordinate₃, hx₄₃]
    ring
  have hcross := seven_cross_identity W x
  linear_combination hcross - hleft

end MazurTorsion.DivisionPolynomialRootCriterion
