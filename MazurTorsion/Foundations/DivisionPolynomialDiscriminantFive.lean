/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Discriminant of the fifth division polynomial

This file computes the discriminant of the universal fifth division polynomial of a
Weierstrass curve over `ℚ`. The calculation first translates the curve to a model with
`b₂ = 0`, then uses a compact resultant certificate built from low-degree polynomial
identities.
-/

open Polynomial

namespace MazurTorsion.DivisionPolynomialDiscriminantFive

private noncomputable def D (u v : ℚ) : ℚ[X] :=
  4 * X ^ 3 + 2 * C u * X + C v

private noncomputable def S (u : ℚ) : ℚ[X] :=
  6 * X ^ 2 + C u

/-- Four times the normal-form third division polynomial. -/
private noncomputable def A (u v : ℚ) : ℚ[X] :=
  12 * X ^ 4 + 12 * C u * X ^ 2 + 12 * C v * X - C u ^ 2

/-- Four times the normal-form auxiliary fourth division polynomial. -/
private noncomputable def B (u v : ℚ) : ℚ[X] :=
  8 * X ^ 6 + 20 * C u * X ^ 4 + 40 * C v * X ^ 3 -
    10 * C u ^ 2 * X ^ 2 - 4 * C u * C v * X -
    (C u ^ 3 + 4 * C v ^ 2)

/-- Sixty-four times the normal-form fifth division polynomial. -/
private noncomputable def F (u v : ℚ) : ℚ[X] :=
  16 * B u v * D u v ^ 2 - A u v ^ 3

private noncomputable def H (u v : ℚ) : ℚ[X] :=
  48 * X ^ 8 + 224 * C u * X ^ 6 + 672 * C v * X ^ 5 -
    280 * C u ^ 2 * X ^ 4 - 224 * C u * C v * X ^ 3 -
    (40 * C u ^ 3 + 240 * C v ^ 2) * X ^ 2 + 8 * C u ^ 2 * C v * X -
    (5 * C u ^ 4 + 16 * C u * C v ^ 2)

private def delta (u v : ℚ) : ℚ :=
  8 * u ^ 3 + 27 * v ^ 2

private lemma natDegree_D (u v : ℚ) : (D u v).natDegree = 3 := by
  unfold D
  compute_degree!

private lemma natDegree_S (u : ℚ) : (S u).natDegree = 2 := by
  unfold S
  compute_degree!

private lemma natDegree_A (u v : ℚ) : (A u v).natDegree = 4 := by
  unfold A
  compute_degree!

private lemma natDegree_B (u v : ℚ) : (B u v).natDegree = 6 := by
  unfold B
  compute_degree!

private lemma natDegree_H (u v : ℚ) : (H u v).natDegree = 8 := by
  unfold H
  compute_degree!

private lemma leadingCoeff_D (u v : ℚ) : (D u v).leadingCoeff = 4 := by
  rw [leadingCoeff, natDegree_D]
  simp [D]

private lemma leadingCoeff_A (u v : ℚ) : (A u v).leadingCoeff = 12 := by
  rw [leadingCoeff, natDegree_A]
  unfold A
  compute_degree!

private lemma leadingCoeff_B (u v : ℚ) : (B u v).leadingCoeff = 8 := by
  rw [leadingCoeff, natDegree_B]
  unfold B
  compute_degree!

private lemma leadingCoeff_sixteen : (16 : ℚ[X]).leadingCoeff = 16 := by
  change (C (16 : ℚ) : ℚ[X]).leadingCoeff = 16
  simp

private lemma natDegree_F (u v : ℚ) : (F u v).natDegree = 12 := by
  have hB : B u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (B u v).natDegree by rw [natDegree_B]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have h₁ : (16 * B u v * D u v ^ 2).natDegree = 12 := by
    rw [natDegree_mul (mul_ne_zero (by norm_num) hB) (pow_ne_zero 2 hD),
      natDegree_mul (by norm_num) hB, natDegree_pow, natDegree_B, natDegree_D]
    norm_num
  have h₂ : (A u v ^ 3).natDegree = 12 := by
    simp [natDegree_pow, natDegree_A]
  have hlc₁ : (16 * B u v * D u v ^ 2).leadingCoeff = 2048 := by
    norm_num [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_B, leadingCoeff_D,
      leadingCoeff_sixteen]
  have hlc₂ : (A u v ^ 3).leadingCoeff = 1728 := by
    norm_num [leadingCoeff_pow, leadingCoeff_A]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)]
  rw [F, sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, hlc₁, hlc₂]
    norm_num

private lemma leadingCoeff_F (u v : ℚ) : (F u v).leadingCoeff = 320 := by
  have hB : B u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (B u v).natDegree by rw [natDegree_B]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have h₁ : (16 * B u v * D u v ^ 2).natDegree = 12 := by
    rw [natDegree_mul (mul_ne_zero (by norm_num) hB) (pow_ne_zero 2 hD),
      natDegree_mul (by norm_num) hB, natDegree_pow, natDegree_B, natDegree_D]
    norm_num
  have h₂ : (A u v ^ 3).natDegree = 12 := by
    simp [natDegree_pow, natDegree_A]
  have hdeg :
      (16 * B u v * D u v ^ 2).degree = (A u v ^ 3).degree := by
    rw [(degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₂]
  rw [F, leadingCoeff_sub_of_degree_eq hdeg]
  · norm_num [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_B, leadingCoeff_D,
      leadingCoeff_A, leadingCoeff_sixteen]
  · norm_num [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_B, leadingCoeff_D,
      leadingCoeff_A, leadingCoeff_sixteen]

private lemma derivative_D (u v : ℚ) :
    (D u v).derivative = 2 * S u := by
  simp [D, S, derivative_add, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma derivative_A (u v : ℚ) :
    (A u v).derivative = 12 * D u v := by
  simp [A, D, derivative_add, derivative_sub, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma A_identity (u v : ℚ) :
    A u v = 12 * X * D u v - S u ^ 2 := by
  simp [A, D, S]
  ring

private lemma B_identity (u v : ℚ) :
    B u v + 4 * D u v ^ 2 = A u v * S u := by
  simp [B, A, D, S]
  ring

private lemma H_identity_B (u v : ℚ) :
    H u v = 4 * B u v * S u - A u v ^ 2 := by
  simp [H, B, A, S]
  ring

private lemma H_identity_derivative_B (u v : ℚ) :
    H u v = 4 * D u v * (B u v).derivative - 5 * A u v ^ 2 := by
  simp [H, B, A, D, derivative_add, derivative_sub, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma derivative_F (u v : ℚ) :
    (F u v).derivative = 20 * D u v * H u v := by
  calc
    (F u v).derivative =
        16 * (B u v).derivative * D u v ^ 2 +
          32 * B u v * D u v * (D u v).derivative -
          3 * A u v ^ 2 * (A u v).derivative := by
      simp [F, derivative_sub, derivative_mul, derivative_pow]
      simp only [map_ofNat]
      ring
    _ = 20 * D u v * H u v := by
      rw [derivative_A, derivative_D]
      calc
        16 * (B u v).derivative * D u v ^ 2 +
              32 * B u v * D u v * (2 * S u) -
              3 * A u v ^ 2 * (12 * D u v) =
            4 * D u v *
              ((4 * D u v * (B u v).derivative - 5 * A u v ^ 2) +
                4 * (4 * B u v * S u - A u v ^ 2)) := by ring
        _ = 20 * D u v * H u v := by
          rw [← H_identity_derivative_B, ← H_identity_B]
          ring

private lemma F_identity (u v : ℚ) :
    F u v + 4 * B u v ^ 2 = H u v * A u v := by
  simp [F, H, B, A, D]
  ring

private lemma discr_D (u v : ℚ) :
    (D u v).discr = -16 * delta u v := by
  have hdegree : (D u v).degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_D u v)
  rw [discr_of_degree_eq_three hdegree]
  simp [D, delta]
  ring

private lemma resultant_D_derivative (u v : ℚ) :
    (D u v).resultant (D u v).derivative = 64 * delta u v := by
  have hdegree : (D u v).degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_D u v)
  calc
    (D u v).resultant (D u v).derivative =
        (-1) ^ ((D u v).natDegree * ((D u v).natDegree - 1) / 2) *
          (D u v).leadingCoeff * (D u v).discr := by
      simpa using resultant_deriv (show 0 < (D u v).degree by rw [hdegree]; norm_num)
    _ = 64 * delta u v := by
      rw [natDegree_D, leadingCoeff_D, discr_D]
      norm_num
      ring

private lemma resultant_D_S (u v : ℚ) :
    (D u v).resultant (S u) = 8 * delta u v := by
  have hderivativeDegree : (D u v).derivative.natDegree = 2 := by
    rw [natDegree_derivative, natDegree_D]
  have hscale :
      (D u v).resultant (D u v).derivative 3 2 =
        2 ^ 3 * (D u v).resultant (S u) 3 2 := by
    rw [derivative_D]
    change
      (D u v).resultant (C (2 : ℚ) * S u) 3 2 =
        2 ^ 3 * (D u v).resultant (S u) 3 2
    exact resultant_C_mul_right (D u v) (S u) 3 2 (2 : ℚ)
  have hcubic := resultant_D_derivative u v
  rw [natDegree_D, hderivativeDegree] at hcubic
  rw [natDegree_D, natDegree_S]
  norm_num at hscale
  linarith

private lemma resultant_D_A (u v : ℚ) :
    (D u v).resultant (A u v) = -64 * delta u v ^ 2 := by
  have hAform :
      A u v = -(S u ^ 2) + D u v * (12 * X) := by
    rw [A_identity]
    ring
  have hmultiplier : (12 * X : ℚ[X]).natDegree ≤ 1 := by
    compute_degree!
  have hadd :
      (D u v).resultant (-(S u ^ 2) + D u v * (12 * X)) 3 4 =
        (D u v).resultant (-(S u ^ 2)) 3 4 :=
    resultant_add_mul_right (D u v) (-(S u ^ 2)) (12 * X) 3 4
      (by omega) (by rw [natDegree_D])
  have hscale :
      (D u v).resultant (-(S u ^ 2)) 3 4 =
        -(D u v).resultant (S u ^ 2) 3 4 := by
    have h := resultant_C_mul_right (D u v) (S u ^ 2) 3 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hmul :
      (D u v).resultant (S u ^ 2) 3 4 =
        (D u v).resultant (S u) 3 2 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_S] using
      resultant_mul_right (D u v) (S u) (S u) 3 (by rw [natDegree_D])
  have hDS := resultant_D_S u v
  rw [natDegree_D, natDegree_S] at hDS
  rw [natDegree_D, natDegree_A, hAform, hadd, hscale, hmul]
  rw [hDS]
  ring

private lemma resultant_B_A (u v : ℚ) :
    (B u v).resultant (A u v) = 2 ^ 20 * delta u v ^ 4 := by
  have hBform :
      B u v = -4 * D u v ^ 2 + A u v * S u := by
    rw [← B_identity]
    ring
  have hadd :
      (-4 * D u v ^ 2 + A u v * S u).resultant (A u v) 6 4 =
        (-4 * D u v ^ 2).resultant (A u v) 6 4 :=
    resultant_add_mul_left (-4 * D u v ^ 2) (A u v) (S u) 6 4
      (by rw [natDegree_S]) (by rw [natDegree_A])
  have hscale :
      (-4 * D u v ^ 2).resultant (A u v) 6 4 =
        4 ^ 4 * (D u v ^ 2).resultant (A u v) 6 4 := by
    have h := resultant_C_mul_left (D u v ^ 2) (A u v) 6 4 (-4 : ℚ)
    rw [C_neg, map_ofNat] at h
    norm_num at h
    exact h
  have hmul :
      (D u v ^ 2).resultant (A u v) 6 4 =
        (D u v).resultant (A u v) 3 4 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_D] using
      resultant_mul_left (D u v) (D u v) (A u v) 4 (by rw [natDegree_A])
  have hDA := resultant_D_A u v
  rw [natDegree_D, natDegree_A] at hDA
  rw [natDegree_B, natDegree_A, hBform, hadd, hscale, hmul, hDA]
  ring

private lemma resultant_B_H (u v : ℚ) :
    (B u v).resultant (H u v) = 2 ^ 40 * delta u v ^ 8 := by
  have hHform :
      H u v = -(A u v ^ 2) + B u v * (4 * S u) := by
    rw [H_identity_B]
    ring
  have hmultiplier : (4 * S u : ℚ[X]).natDegree ≤ 2 := by
    unfold S
    compute_degree!
  have hadd :
      (B u v).resultant (-(A u v ^ 2) + B u v * (4 * S u)) 6 8 =
        (B u v).resultant (-(A u v ^ 2)) 6 8 :=
    resultant_add_mul_right (B u v) (-(A u v ^ 2)) (4 * S u) 6 8
      (by omega) (by rw [natDegree_B])
  have hscale :
      (B u v).resultant (-(A u v ^ 2)) 6 8 =
        (B u v).resultant (A u v ^ 2) 6 8 := by
    have h := resultant_C_mul_right (B u v) (A u v ^ 2) 6 8 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hmul :
      (B u v).resultant (A u v ^ 2) 6 8 =
        (B u v).resultant (A u v) 6 4 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_A] using
      resultant_mul_right (B u v) (A u v) (A u v) 6 (by rw [natDegree_B])
  have hBA := resultant_B_A u v
  rw [natDegree_B, natDegree_A] at hBA
  rw [natDegree_B, natDegree_H, hHform, hadd, hscale, hmul, hBA]
  ring

private lemma resultant_F_H (u v : ℚ) :
    (F u v).resultant (H u v) = 2 ^ 96 * delta u v ^ 16 := by
  have hFform :
      F u v = -4 * B u v ^ 2 + H u v * A u v := by
    rw [← F_identity]
    ring
  have hadd :
      (-4 * B u v ^ 2 + H u v * A u v).resultant (H u v) 12 8 =
        (-4 * B u v ^ 2).resultant (H u v) 12 8 :=
    resultant_add_mul_left (-4 * B u v ^ 2) (H u v) (A u v) 12 8
      (by rw [natDegree_A]) (by rw [natDegree_H])
  have hscale :
      (-4 * B u v ^ 2).resultant (H u v) 12 8 =
        4 ^ 8 * (B u v ^ 2).resultant (H u v) 12 8 := by
    have h := resultant_C_mul_left (B u v ^ 2) (H u v) 12 8 (-4 : ℚ)
    rw [C_neg, map_ofNat] at h
    norm_num at h
    exact h
  have hmul :
      (B u v ^ 2).resultant (H u v) 12 8 =
        (B u v).resultant (H u v) 6 8 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_B] using
      resultant_mul_left (B u v) (B u v) (H u v) 8 (by rw [natDegree_H])
  have hBH := resultant_B_H u v
  rw [natDegree_B, natDegree_H] at hBH
  rw [natDegree_F, natDegree_H, hFform, hadd, hscale, hmul, hBH]
  ring

private lemma resultant_F_D (u v : ℚ) :
    (F u v).resultant (D u v) = 2 ^ 18 * delta u v ^ 6 := by
  have hFform :
      F u v = -(A u v ^ 3) + D u v * (16 * B u v * D u v) := by
    rw [F]
    ring
  have hmultiplier : (16 * B u v * D u v : ℚ[X]).natDegree ≤ 9 := by
    unfold B D
    compute_degree!
  have hadd :
      (-(A u v ^ 3) + D u v * (16 * B u v * D u v)).resultant (D u v) 12 3 =
        (-(A u v ^ 3)).resultant (D u v) 12 3 :=
    resultant_add_mul_left (-(A u v ^ 3)) (D u v) (16 * B u v * D u v) 12 3
      (by omega) (by rw [natDegree_D])
  have hscale :
      (-(A u v ^ 3)).resultant (D u v) 12 3 =
        -(A u v ^ 3).resultant (D u v) 12 3 := by
    have h := resultant_C_mul_left (A u v ^ 3) (D u v) 12 3 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hpow :
      (A u v ^ 3).resultant (D u v) 12 3 =
        (A u v).resultant (D u v) 4 3 ^ 3 := by
    simpa [natDegree_A] using
      resultant_pow_left (A u v) (D u v) 3 3
        (by rw [leadingCoeff_A]; norm_num) (by rw [natDegree_D])
  have hcomm := resultant_comm (D u v) (A u v) 3 4
  norm_num at hcomm
  have hDA := resultant_D_A u v
  rw [natDegree_D, natDegree_A] at hDA
  have hAD :
      (A u v).resultant (D u v) 4 3 = -64 * delta u v ^ 2 := by
    rw [← hcomm, hDA]
  rw [natDegree_F, natDegree_D, hFform, hadd, hscale, hpow, hAD]
  ring

private lemma resultant_F_derivative (u v : ℚ) :
    (F u v).resultant (F u v).derivative =
      2 ^ 138 * 5 ^ 12 * delta u v ^ 22 := by
  have hderivativeDegree : (F u v).derivative.natDegree = 11 := by
    rw [natDegree_derivative, natDegree_F]
  have hderivativeForm :
      (F u v).derivative = C (20 : ℚ) * (D u v * H u v) := by
    rw [derivative_F]
    simp only [map_ofNat]
    ring
  have hscale :
      (F u v).resultant (F u v).derivative 12 11 =
        20 ^ 12 * (F u v).resultant (D u v * H u v) 12 11 := by
    rw [hderivativeForm]
    exact resultant_C_mul_right (F u v) (D u v * H u v) 12 11 (20 : ℚ)
  have hmul :
      (F u v).resultant (D u v * H u v) 12 11 =
        (F u v).resultant (D u v) 12 3 * (F u v).resultant (H u v) 12 8 := by
    simpa [natDegree_D, natDegree_H] using
      resultant_mul_right (F u v) (D u v) (H u v) 12 (by rw [natDegree_F])
  have hFD := resultant_F_D u v
  rw [natDegree_F, natDegree_D] at hFD
  have hFH := resultant_F_H u v
  rw [natDegree_F, natDegree_H] at hFH
  rw [natDegree_F, hderivativeDegree, hscale, hmul, hFD, hFH]
  ring

private lemma normal_D (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    D W.b₄ W.b₆ = W.Ψ₂Sq := by
  simp [D, WeierstrassCurve.Ψ₂Sq, hb₂]
  simp only [map_ofNat]

private lemma normal_A (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    A W.b₄ W.b₆ = 4 * W.Ψ₃ := by
  have hb₈ : 4 * W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation, hb₂]
    ring
  have hC :
      (4 : ℚ[X]) * C W.b₈ = -(C W.b₄ ^ 2) := by
    simpa only [map_ofNat, C_mul, C_neg, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₈
  simp [A, WeierstrassCurve.Ψ₃, hb₂]
  linear_combination -hC

private lemma normal_B (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    B W.b₄ W.b₆ = 4 * W.preΨ₄ := by
  have hb₈ : 4 * W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation, hb₂]
    ring
  have hC :
      (4 : ℚ[X]) * C W.b₈ = -(C W.b₄ ^ 2) := by
    simpa only [map_ofNat, C_mul, C_neg, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₈
  simp [B, WeierstrassCurve.preΨ₄, hb₂]
  linear_combination -(10 * X ^ 2 + C W.b₄) * hC

private lemma preΨ_five (W : WeierstrassCurve ℚ) :
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num, W.preΨ'_odd 0]
  norm_num

private lemma normal_F (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    F W.b₄ W.b₆ = C (64 : ℚ) * W.preΨ' 5 := by
  rw [F, normal_B W hb₂, normal_A W hb₂, normal_D W hb₂, preΨ_five]
  simp only [map_ofNat]
  ring

private lemma normal_delta (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    delta W.b₄ W.b₆ = -W.Δ := by
  simp [delta, WeierstrassCurve.Δ, hb₂]
  ring

private lemma normal_resultant_five_derivative
    (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    (W.preΨ' 5).resultant (W.preΨ' 5).derivative =
      5 ^ 12 * delta W.b₄ W.b₆ ^ 22 := by
  let p := W.preΨ' 5
  have hpDegree : p.natDegree = 12 := by
    dsimp [p]
    rw [W.natDegree_preΨ' (n := 5) (by norm_num)]
    norm_num [show ¬Even 5 by decide]
  have hpDerivativeDegree : p.derivative.natDegree = 11 := by
    rw [natDegree_derivative, hpDegree]
  have hFDerivativeDegree : (F W.b₄ W.b₆).derivative.natDegree = 11 := by
    rw [natDegree_derivative, natDegree_F]
  have hF : F W.b₄ W.b₆ = C (64 : ℚ) * p := by
    simpa [p] using normal_F W hb₂
  have hFDerivative :
      (F W.b₄ W.b₆).derivative = C (64 : ℚ) * p.derivative := by
    rw [hF, derivative_mul]
    simp
  have hscale :
      (F W.b₄ W.b₆).resultant (F W.b₄ W.b₆).derivative 12 11 =
        64 ^ 23 * p.resultant p.derivative 12 11 := by
    rw [hFDerivative, hF]
    calc
      (C (64 : ℚ) * p).resultant (C (64 : ℚ) * p.derivative) 12 11 =
          64 ^ 11 * p.resultant (C (64 : ℚ) * p.derivative) 12 11 :=
        resultant_C_mul_left p (C (64 : ℚ) * p.derivative) 12 11 64
      _ = 64 ^ 11 * (64 ^ 12 * p.resultant p.derivative 12 11) := by
        rw [resultant_C_mul_right]
      _ = 64 ^ 23 * p.resultant p.derivative 12 11 := by ring
  have hresultant := resultant_F_derivative W.b₄ W.b₆
  rw [natDegree_F, hFDerivativeDegree, hscale] at hresultant
  rw [hpDegree, hpDerivativeDegree]
  norm_num at hresultant ⊢
  linarith

private lemma normal_discr_five
    (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    (W.preΨ' 5).discr = 5 ^ 11 * W.Δ ^ 22 := by
  let p := W.preΨ' 5
  have hpDegree : p.natDegree = 12 := by
    dsimp [p]
    rw [W.natDegree_preΨ' (n := 5) (by norm_num)]
    norm_num [show ¬Even 5 by decide]
  have hpDerivativeDegree : p.derivative.natDegree = 11 := by
    rw [natDegree_derivative, hpDegree]
  have hpLeadingCoeff : p.leadingCoeff = 5 := by
    dsimp [p]
    rw [W.leadingCoeff_preΨ' (n := 5) (by norm_num)]
    norm_num [show ¬Even 5 by decide]
  have hdegree : p.degree = 12 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr hpDegree
  have hrel := resultant_deriv (show 0 < p.degree by rw [hdegree]; norm_num)
  rw [hpDegree, hpLeadingCoeff] at hrel
  norm_num at hrel
  have hresultant := normal_resultant_five_derivative W hb₂
  change p.resultant p.derivative = _ at hresultant
  rw [hpDegree, hpDerivativeDegree] at hresultant
  rw [hresultant] at hrel
  rw [normal_delta W hb₂] at hrel
  change p.discr = _
  norm_num at hrel ⊢
  linarith

private def translation (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := r
  s := 0
  t := 0

private lemma taylor_two (r : ℚ) :
    Polynomial.taylor r (2 : ℚ[X]) = (2 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 2

private lemma taylor_three (r : ℚ) :
    Polynomial.taylor r (3 : ℚ[X]) = (3 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 3

private lemma taylor_five (r : ℚ) :
    Polynomial.taylor r (5 : ℚ[X]) = (5 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 5

private lemma taylor_ten (r : ℚ) :
    Polynomial.taylor r (10 : ℚ[X]) = (10 : ℚ[X]) :=
  map_ofNat (Polynomial.taylorAlgHom r) 10

private lemma translation_Ψ₂Sq (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).Ψ₂Sq = W.Ψ₂Sq.taylor r := by
  simp [translation, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆]
  simp only [map_ofNat]
  ring

private lemma translation_Ψ₃ (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).Ψ₃ = W.Ψ₃.taylor r := by
  simp [translation, WeierstrassCurve.Ψ₃, WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆,
    WeierstrassCurve.variableChange_b₈]
  simp only [taylor_three]
  simp only [map_ofNat]
  ring

private lemma translation_preΨ₄ (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).preΨ₄ = W.preΨ₄.taylor r := by
  have hC :
      (4 : ℚ[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 := by
    simpa only [map_ofNat, C_mul, C_sub, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) W.b_relation
  simp [translation, WeierstrassCurve.preΨ₄, WeierstrassCurve.variableChange_b₂,
    WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆,
    WeierstrassCurve.variableChange_b₈]
  simp only [taylor_two, taylor_five, taylor_ten]
  simp only [map_ofNat]
  linear_combination -(2 * C r * X + C r ^ 2) * hC

private lemma translation_preΨ_five (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).preΨ' 5 = (W.preΨ' 5).taylor r := by
  rw [preΨ_five, preΨ_five]
  rw [translation_preΨ₄, translation_Ψ₂Sq, translation_Ψ₃]
  simp

private lemma discr_taylor (f : ℚ[X]) (r : ℚ) :
    (f.taylor r).discr = f.discr := by
  by_cases hfDegree : f.natDegree = 0
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hfDegree
    simp
  have hfDegreePos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    omega
  have htaylorDegreePos : 0 < (f.taylor r).degree := by
    simpa using hfDegreePos
  have hderivative :
      (f.taylor r).derivative = f.derivative.taylor r := by
    simp [Polynomial.taylor_apply, derivative_comp]
  have hderivativeDegree :
      f.derivative.natDegree = f.natDegree - 1 := by
    rw [natDegree_derivative]
  have hresultantTaylor := resultant_taylor f f.derivative r
  rw [natDegree_taylor, natDegree_taylor, hderivativeDegree] at hresultantTaylor
  have hresultant := resultant_deriv hfDegreePos
  have hresultantTranslated := resultant_deriv htaylorDegreePos
  rw [hderivative, natDegree_taylor, leadingCoeff_taylor] at hresultantTranslated
  rw [hresultantTaylor, hresultant] at hresultantTranslated
  have hf : f ≠ 0 := by
    intro hf
    rw [hf, natDegree_zero] at hfDegree
    exact hfDegree rfl
  have hfactor :
      (-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hf)
  exact (mul_left_cancel₀ hfactor hresultantTranslated).symm

/-- The discriminant of the universal fifth division polynomial over `ℚ`. -/
theorem discr_preΨ_five (W : WeierstrassCurve ℚ) :
    (W.preΨ' 5).discr = (5 : ℚ) ^ 11 * W.Δ ^ 22 := by
  let r : ℚ := -W.b₂ / 12
  let W₀ : WeierstrassCurve ℚ := translation r • W
  have hb₂ : W₀.b₂ = 0 := by
    simp [W₀, translation, r, WeierstrassCurve.variableChange_b₂]
    ring
  have hnormal := normal_discr_five W₀ hb₂
  have hpolynomial := translation_preΨ_five W r
  have hΔ : W₀.Δ = W.Δ := by
    simp [W₀, translation, WeierstrassCurve.variableChange_Δ]
  calc
    (W.preΨ' 5).discr = ((W.preΨ' 5).taylor r).discr :=
      (discr_taylor (W.preΨ' 5) r).symm
    _ = (W₀.preΨ' 5).discr := by rw [← hpolynomial]
    _ = (5 : ℚ) ^ 11 * W₀.Δ ^ 22 := hnormal
    _ = (5 : ℚ) ^ 11 * W.Δ ^ 22 := by rw [hΔ]

end MazurTorsion.DivisionPolynomialDiscriminantFive
