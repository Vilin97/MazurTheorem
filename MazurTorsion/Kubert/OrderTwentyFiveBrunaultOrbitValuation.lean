/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
# Valuation vectors for the order-twenty-five Brunault orbit

This file isolates the integer-linear part of the three-adic orbit argument.
For a vanishing sum of four nonzero terms, a nonarchimedean valuation attains
its minimum at least twice.  Applying that necessary condition to the five
cyclic Lécacheux relations gives the five hypotheses below, while the norm-one
relation gives the zero-sum hypothesis.

The resulting valuation vector is either zero or lies on one of the five
oriented cusp rays.  This theorem is deliberately independent of the raw
orbit formulas: a downstream marked-point consumer must first prove all five
cyclic relations for those formulas.
-/

namespace MazurTorsion.Kubert

/-- Four integers have a repeated minimum. -/
def orderTwentyFiveRepeatedMinFour (a b c d : ℤ) : Prop :=
  (a = b ∧ a ≤ c ∧ a ≤ d) ∨
    (a = c ∧ a ≤ b ∧ a ≤ d) ∨
    (a = d ∧ a ≤ b ∧ a ≤ c) ∨
    (b = c ∧ b ≤ a ∧ b ≤ d) ∨
    (b = d ∧ b ≤ a ∧ b ≤ c) ∨
    (c = d ∧ c ≤ a ∧ c ≤ b)

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_one
    (a b c d e : ℤ)
    (h₀ : a = c ∧ a ≤ a + b ∧ a ≤ a + d)
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₁ h₂ h₃ h₄
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_two
    (a b c d e : ℤ)
    (h₀ : a = a + b ∧ a ≤ c ∧ a ≤ a + d)
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₁ h₂ h₃ h₄
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_three
    (a b c d e : ℤ)
    (h₀ : a = a + d ∧ a ≤ c ∧ a ≤ a + b)
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₁ h₂ h₃ h₄
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_one
    (a b c d e : ℤ)
    (_h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (_h₁ : b = d ∧ b ≤ b + c ∧ b ≤ b + e)
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (_hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₂ h₃ h₄
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_two
    (a b c d e : ℤ)
    (_h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (_h₁ : b = b + c ∧ b ≤ d ∧ b ≤ b + e)
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (_hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₂ h₃ h₄
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_three
    (a b c d e : ℤ)
    (_h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (_h₁ : b = b + e ∧ b ≤ d ∧ b ≤ b + c)
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (_hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₂ h₃ h₄
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_four
    (a b c d e : ℤ)
    (_h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (_h₁ : d = b + c ∧ d ≤ b ∧ d ≤ b + e)
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (_hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₂ h₃ h₄
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_five
    (a b c d e : ℤ)
    (_h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (_h₁ : d = b + e ∧ d ≤ b ∧ d ≤ b + c)
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (_hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₂ h₃ h₄
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_six
    (a b c d e : ℤ)
    (_h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (_h₁ : b + c = b + e ∧ b + c ≤ b ∧ b + c ≤ d)
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (_hsum : a + b + c + d + e = 0)
    (_hd : d < 0) (_hda : d ≤ a) (_hdb : d ≤ b)
    (_hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₂ h₃ h₄
  rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four
    (a b c d e : ℤ)
    (h₀ : c = a + b ∧ c ≤ a ∧ c ≤ a + d)
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (hsum : a + b + c + d + e = 0)
    (hd : d < 0) (hda : d ≤ a) (hdb : d ≤ b)
    (hdc : d ≤ c) (hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  simp only [orderTwentyFiveRepeatedMinFour] at h₁
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_one
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_two
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_three
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_four
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_five
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four_six
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_five
    (a b c d e : ℤ)
    (h₀ : c = a + d ∧ c ≤ a ∧ c ≤ a + b)
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (hsum : a + b + c + d + e = 0)
    (hd : d < 0) (hda : d ≤ a) (_hdb : d ≤ b)
    (hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₁ h₂ h₃ h₄
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_six
    (a b c d e : ℤ)
    (h₀ : a + b = a + d ∧ a + b ≤ a ∧ a + b ≤ c)
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (hsum : a + b + c + d + e = 0)
    (hd : d < 0) (hda : d ≤ a) (_hdb : d ≤ b)
    (hdc : d ≤ c) (_hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  refine ⟨-b, ?_⟩
  simp only [orderTwentyFiveRepeatedMinFour] at h₁ h₂ h₃ h₄
  rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ | h₃ <;>
    rcases h₄ with h₄ | h₄ | h₄ | h₄ | h₄ | h₄ <;>
    omega

private theorem orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min
    (a b c d e : ℤ)
    (h₀ : orderTwentyFiveRepeatedMinFour a c (a + b) (a + d))
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (hsum : a + b + c + d + e = 0)
    (hd : d < 0) (hda : d ≤ a) (hdb : d ≤ b)
    (hdc : d ≤ c) (hde : d ≤ e) :
    ∃ t : ℤ, 0 < t ∧
      a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t := by
  simp only [orderTwentyFiveRepeatedMinFour] at h₀
  rcases h₀ with h₀ | h₀ | h₀ | h₀ | h₀ | h₀
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_one
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_two
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_three
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_four
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_five
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde
  · exact orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min_case_six
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum hd hda hdb hdc hde

/-- The five tropicalized Lécacheux relations and the norm-one relation
leave only the zero vector and the five cyclic cusp rays.

The coordinates are ordered as `(x₀, x₁, x₂, x₃, x₄)`.  With the
additive `padicValRat` convention, the scalar on a nonzero ray is positive;
the opposite rays do not satisfy the repeated-minimum conditions. -/
theorem orderTwentyFiveOrbitValuation_classification
    (a b c d e : ℤ)
    (h₀ : orderTwentyFiveRepeatedMinFour a c (a + b) (a + d))
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (hsum : a + b + c + d + e = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
      ∃ t : ℤ, 0 < t ∧
        ((a = 3 * t ∧ b = -t ∧ c = t ∧ d = -2 * t ∧ e = -t) ∨
          (a = -t ∧ b = t ∧ c = -2 * t ∧ d = -t ∧ e = 3 * t) ∨
          (a = t ∧ b = -2 * t ∧ c = -t ∧ d = 3 * t ∧ e = -t) ∨
          (a = -2 * t ∧ b = -t ∧ c = 3 * t ∧ d = -t ∧ e = t) ∨
          (a = -t ∧ b = 3 * t ∧ c = -t ∧ d = t ∧ e = -2 * t)) := by
  by_cases hzero : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0
  · exact Or.inl hzero
  · right
    have hmin :
        (a ≤ b ∧ a ≤ c ∧ a ≤ d ∧ a ≤ e) ∨
          (b ≤ a ∧ b ≤ c ∧ b ≤ d ∧ b ≤ e) ∨
          (c ≤ a ∧ c ≤ b ∧ c ≤ d ∧ c ≤ e) ∨
          (d ≤ a ∧ d ≤ b ∧ d ≤ c ∧ d ≤ e) ∨
          (e ≤ a ∧ e ≤ b ∧ e ≤ c ∧ e ≤ d) := by
      omega
    rcases hmin with ha | hb | hc | hd | he
    · have haNeg : a < 0 := by omega
      obtain ⟨t, ht, hc', hd', he', ha', hb'⟩ :=
        orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min
          c d e a b h₂ h₃ h₄ h₀ h₁ (by omega) haNeg ha.2.1 ha.2.2.1
          ha.2.2.2 ha.1
      exact ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inl (by omega))))⟩
    · have hbNeg : b < 0 := by omega
      obtain ⟨t, ht, hd', he', ha', hb', hc'⟩ :=
        orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min
          d e a b c h₃ h₄ h₀ h₁ h₂ (by omega) hbNeg hb.2.2.1 hb.2.2.2
          hb.1 hb.2.1
      exact ⟨t, ht, Or.inr (Or.inr (Or.inl (by omega)))⟩
    · have hcNeg : c < 0 := by omega
      obtain ⟨t, ht, he', ha', hb', hc', hd'⟩ :=
        orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min
          e a b c d h₄ h₀ h₁ h₂ h₃ (by omega) hcNeg hc.2.2.2 hc.1 hc.2.1
          hc.2.2.1
      exact ⟨t, ht, Or.inr (Or.inl (by omega))⟩
    · have hdNeg : d < 0 := by omega
      obtain ⟨t, ht, ha', hb', hc', hd', he'⟩ :=
        orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min
          a b c d e h₀ h₁ h₂ h₃ h₄ hsum hdNeg hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      exact ⟨t, ht, Or.inl (by omega)⟩
    · have heNeg : e < 0 := by omega
      obtain ⟨t, ht, hb', hc', hd', he', ha'⟩ :=
        orderTwentyFiveOrbitValuation_eq_cuspRay_of_fourth_min
          b c d e a h₁ h₂ h₃ h₄ h₀ (by omega) heNeg he.2.1 he.2.2.1
          he.2.2.2 he.1
      exact ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr (by omega))))⟩

/-- Under the same orbit constraints, one valuation-zero coordinate excludes
all five nonzero cusp rays and forces the whole valuation vector to vanish.

A raw-orbit consumer still has to prove that its four terms are nonzero before
deriving each repeated-minimum hypothesis, transport norm one to the displayed
valuation sum, and supply the valuation-zero coordinate. -/
theorem orderTwentyFiveOrbitValuation_eq_zero_of_first_eq_zero
    (a b c d e : ℤ)
    (h₀ : orderTwentyFiveRepeatedMinFour a c (a + b) (a + d))
    (h₁ : orderTwentyFiveRepeatedMinFour b d (b + c) (b + e))
    (h₂ : orderTwentyFiveRepeatedMinFour c e (c + d) (c + a))
    (h₃ : orderTwentyFiveRepeatedMinFour d a (d + e) (d + b))
    (h₄ : orderTwentyFiveRepeatedMinFour e b (e + a) (e + c))
    (hsum : a + b + c + d + e = 0)
    (ha : a = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  obtain hzero | ⟨t, ht, hray⟩ :=
    orderTwentyFiveOrbitValuation_classification
      a b c d e h₀ h₁ h₂ h₃ h₄ hsum
  · exact hzero
  · rcases hray with hray | hray | hray | hray | hray <;> omega

end MazurTorsion.Kubert
