/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Discriminant of the seventh division polynomial

This file computes the discriminant of the universal seventh division polynomial over
`ℚ`. A sparse degree-twenty auxiliary polynomial reduces all high-degree resultants to
two low-degree resultants. A translation then removes the `b₂ = 0` normalization.
-/

open Polynomial

namespace MazurTorsion.DivisionPolynomialDiscriminantSeven

private noncomputable def D (a b : ℚ) : ℚ[X] :=
  4 * X ^ 3 + 4 * C a * X + 4 * C b

private noncomputable def S (a : ℚ) : ℚ[X] :=
  6 * X ^ 2 + 2 * C a

private noncomputable def q (a b : ℚ) : ℚ[X] :=
  3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C a ^ 2

private noncomputable def r (a b : ℚ) : ℚ[X] :=
  2 * X ^ 6 + 10 * C a * X ^ 4 + 40 * C b * X ^ 3 -
    10 * C a ^ 2 * X ^ 2 - 8 * C a * C b * X -
    (2 * C a ^ 3 + 16 * C b ^ 2)

private noncomputable def p (u v : ℚ) : ℚ[X] :=
  r u v * D u v ^ 2 - q u v ^ 3

private noncomputable def s (u v : ℚ) : ℚ[X] :=
  p u v * q u v ^ 3 - r u v ^ 3 * D u v ^ 2

private noncomputable def h (u v : ℚ) : ℚ[X] :=
  D u v * (r u v).derivative - 5 * q u v ^ 2

private noncomputable def J (u v : ℚ) : ℚ[X] :=
  (2 * p u v - 5 * r u v ^ 2) * q u v ^ 2 +
    r u v ^ 2 * (D u v * (r u v).derivative - r u v * (D u v).derivative)

private def delta (a b : ℚ) : ℚ := 16 * (4 * a ^ 3 + 27 * b ^ 2)

private lemma natDegree_D (u v : ℚ) : (D u v).natDegree = 3 := by
  unfold D
  compute_degree!

private lemma natDegree_S (u : ℚ) : (S u).natDegree = 2 := by
  unfold S
  compute_degree!

private lemma natDegree_q (u v : ℚ) : (q u v).natDegree = 4 := by
  unfold q
  compute_degree!

private lemma natDegree_r (u v : ℚ) : (r u v).natDegree = 6 := by
  unfold r
  compute_degree!

private lemma leadingCoeff_D (u v : ℚ) : (D u v).leadingCoeff = 4 := by
  rw [leadingCoeff, natDegree_D]
  simp [D]

private lemma leadingCoeff_q (u v : ℚ) : (q u v).leadingCoeff = 3 := by
  rw [leadingCoeff, natDegree_q]
  unfold q
  compute_degree!

private lemma leadingCoeff_r (u v : ℚ) : (r u v).leadingCoeff = 2 := by
  rw [leadingCoeff, natDegree_r]
  unfold r
  compute_degree!

private lemma natDegree_p (u v : ℚ) : (p u v).natDegree = 12 := by
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have h₁ : (r u v * D u v ^ 2).natDegree = 12 := by
    rw [natDegree_mul hr (pow_ne_zero 2 hD), natDegree_pow, natDegree_r, natDegree_D]
  have h₂ : (q u v ^ 3).natDegree = 12 := by
    rw [natDegree_pow, natDegree_q]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)]
  rw [p, sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_r, leadingCoeff_D, leadingCoeff_q]
    norm_num

private lemma leadingCoeff_p (u v : ℚ) : (p u v).leadingCoeff = 5 := by
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have hdeg :
      (r u v * D u v ^ 2).degree = (q u v ^ 3).degree := by
    rw [degree_mul, degree_pow, degree_pow,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 6)).mpr (natDegree_r u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).mpr (natDegree_D u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 4)).mpr (natDegree_q u v)]
    norm_num
  rw [p, leadingCoeff_sub_of_degree_eq hdeg]
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_r, leadingCoeff_D, leadingCoeff_q]
    norm_num
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_r, leadingCoeff_D, leadingCoeff_q]
    norm_num

private lemma natDegree_s (u v : ℚ) : (s u v).natDegree = 24 := by
  have hp : p u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (p u v).natDegree by rw [natDegree_p]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have h₁ : (p u v * q u v ^ 3).natDegree = 24 := by
    rw [natDegree_mul hp (pow_ne_zero 3 hq), natDegree_pow, natDegree_p, natDegree_q]
  have h₂ : (r u v ^ 3 * D u v ^ 2).natDegree = 24 := by
    rw [natDegree_mul (pow_ne_zero 3 hr) (pow_ne_zero 2 hD),
      natDegree_pow, natDegree_pow, natDegree_r, natDegree_D]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 24)]
  rw [s, sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 24)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 24)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow, leadingCoeff_p, leadingCoeff_q,
      leadingCoeff_r, leadingCoeff_D]
    norm_num

private lemma leadingCoeff_s (u v : ℚ) : (s u v).leadingCoeff = 7 := by
  have hp : p u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (p u v).natDegree by rw [natDegree_p]; norm_num)
  have hq : q u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q u v).natDegree by rw [natDegree_q]; norm_num)
  have hr : r u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r u v).natDegree by rw [natDegree_r]; norm_num)
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hdeg :
      (p u v * q u v ^ 3).degree = (r u v ^ 3 * D u v ^ 2).degree := by
    rw [degree_mul, degree_mul,
      degree_pow, degree_pow, degree_pow,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr (natDegree_p u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 4)).mpr (natDegree_q u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 6)).mpr (natDegree_r u v),
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 3)).mpr (natDegree_D u v)]
    norm_num
  rw [s, leadingCoeff_sub_of_degree_eq hdeg]
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow, leadingCoeff_p, leadingCoeff_q, leadingCoeff_r, leadingCoeff_D]
    norm_num
  · rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_pow,
      leadingCoeff_pow, leadingCoeff_p, leadingCoeff_q, leadingCoeff_r, leadingCoeff_D]
    norm_num

private lemma natDegree_p_sub_r_sq (a b : ℚ) :
    (p a b - r a b ^ 2).natDegree = 12 := by
  have hp : p a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (p a b).natDegree by rw [natDegree_p]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have h₁ : (p a b).natDegree = 12 := natDegree_p a b
  have h₂ : (r a b ^ 2).natDegree = 12 := by
    rw [natDegree_pow, natDegree_r]
  rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)]
  rw [sub_eq_add_neg, degree_add_eq_of_leadingCoeff_add_ne_zero]
  · rw [degree_neg, (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₁,
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num : 0 < 12)).mpr h₂]
    simp
  · rw [leadingCoeff_neg, leadingCoeff_pow, leadingCoeff_p, leadingCoeff_r]
    norm_num

private lemma derivative_D (u v : ℚ) : (D u v).derivative = 2 * S u := by
  simp [D, S, derivative_add, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma derivative_q (u v : ℚ) : (q u v).derivative = 3 * D u v := by
  simp [q, D, derivative_add, derivative_sub, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma q_identity (u v : ℚ) :
    4 * q u v = 12 * X * D u v - S u ^ 2 := by
  simp [q, D, S]
  ring

private lemma r_identity (u v : ℚ) :
    r u v + D u v ^ 2 = q u v * S u := by
  simp [r, D, q, S]
  ring

private lemma h_identity (u v : ℚ) :
    h u v = r u v * S u - q u v ^ 2 := by
  simp [h, r, D, q, S, derivative_add, derivative_sub, derivative_pow]
  simp only [map_ofNat]
  ring

private lemma p_h_identity (u v : ℚ) :
    p u v + r u v ^ 2 = h u v * q u v := by
  rw [p, h_identity]
  calc
    (r u v * D u v ^ 2 - q u v ^ 3) + r u v ^ 2 =
        r u v * (r u v + D u v ^ 2) - q u v ^ 3 := by ring
    _ = r u v * (q u v * S u) - q u v ^ 3 := by rw [r_identity]
    _ = (r u v * S u - q u v ^ 2) * q u v := by ring

private lemma h_derivative_identity (u v : ℚ) :
    D u v * (r u v).derivative = h u v + 5 * q u v ^ 2 := by
  simp [h]

private lemma J_simple_identity (u v : ℚ) :
    J u v = 2 * p u v * q u v ^ 2 -
      r u v ^ 3 * S u - r u v ^ 2 * q u v ^ 2 := by
  rw [J, derivative_D, h_derivative_identity, h_identity]
  ring

private lemma derivative_p (u v : ℚ) :
    (p u v).derivative = 5 * D u v * h u v := by
  rw [p, derivative_sub, derivative_mul, derivative_pow, derivative_pow,
    derivative_D, derivative_q]
  calc
    (r u v).derivative * D u v ^ 2 +
        r u v * (2 * D u v ^ 1 * (2 * S u)) -
        3 * q u v ^ 2 * (3 * D u v) =
      D u v * (D u v * (r u v).derivative +
        4 * r u v * S u - 9 * q u v ^ 2) := by ring
    _ = 5 * D u v * h u v := by
      rw [h_derivative_identity, h_identity]
      ring

private lemma derivative_s (u v : ℚ) :
    (s u v).derivative = 7 * D u v * J u v := by
  rw [s, derivative_sub, derivative_mul, derivative_pow, derivative_mul,
    derivative_pow, derivative_pow, derivative_p, derivative_q, derivative_D,
    J_simple_identity]
  calc
    5 * D u v * h u v * q u v ^ 3 +
        p u v * (3 * q u v ^ 2 * (3 * D u v)) -
        (3 * r u v ^ 2 * (r u v).derivative * D u v ^ 2 +
          r u v ^ 3 * (2 * D u v ^ 1 * (2 * S u))) =
      D u v * (5 * h u v * q u v ^ 3 + 9 * p u v * q u v ^ 2 -
        3 * r u v ^ 2 * (D u v * (r u v).derivative) -
        4 * r u v ^ 3 * S u) := by ring
    _ = D u v * (5 * (h u v * q u v) * q u v ^ 2 +
        9 * p u v * q u v ^ 2 -
        3 * r u v ^ 2 * (h u v + 5 * q u v ^ 2) -
        4 * r u v ^ 3 * S u) := by
      rw [h_derivative_identity]
      ring
    _ = D u v * (5 * (p u v + r u v ^ 2) * q u v ^ 2 +
        9 * p u v * q u v ^ 2 -
        3 * r u v ^ 2 * (h u v + 5 * q u v ^ 2) -
        4 * r u v ^ 3 * S u) := by rw [p_h_identity]
    _ = 7 * D u v *
        (2 * p u v * q u v ^ 2 -
          r u v ^ 3 * S u - r u v ^ 2 * q u v ^ 2) := by
      rw [h_identity]
      ring

private lemma natDegree_J (u v : ℚ) : (J u v).natDegree = 20 := by
  have hD : D u v ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D u v).natDegree by rw [natDegree_D]; norm_num)
  have hJ : J u v ≠ 0 := by
    intro hzero
    have hsderivZero : (s u v).derivative = 0 := by
      rw [derivative_s, hzero]
      ring
    have hsderivNonzero : (s u v).derivative ≠ 0 :=
      ne_zero_of_natDegree_gt
        (show 0 < (s u v).derivative.natDegree by
          rw [natDegree_derivative, natDegree_s]
          norm_num)
    exact hsderivNonzero hsderivZero
  have hsderivdeg : (s u v).derivative.natDegree = 23 := by
    rw [natDegree_derivative, natDegree_s]
  rw [derivative_s, natDegree_mul (mul_ne_zero (by norm_num) hD) hJ,
    natDegree_mul (by norm_num) hD, natDegree_D] at hsderivdeg
  norm_num at hsderivdeg
  omega

private lemma q_mul_J (u v : ℚ) :
    q u v * J u v =
      2 * s u v + r u v ^ 2 * (p u v - r u v ^ 2) := by
  rw [J_simple_identity, s]
  calc
    q u v *
        (2 * p u v * q u v ^ 2 -
          r u v ^ 3 * S u - r u v ^ 2 * q u v ^ 2) =
      2 * p u v * q u v ^ 3 - r u v ^ 3 * (q u v * S u) -
        r u v ^ 2 * q u v ^ 3 := by ring
    _ = 2 * p u v * q u v ^ 3 - r u v ^ 3 * (r u v + D u v ^ 2) -
        r u v ^ 2 * q u v ^ 3 := by rw [← r_identity]
    _ = 2 * (p u v * q u v ^ 3 - r u v ^ 3 * D u v ^ 2) +
        r u v ^ 2 * ((r u v * D u v ^ 2 - q u v ^ 3) - r u v ^ 2) := by ring
    _ = 2 * (p u v * q u v ^ 3 - r u v ^ 3 * D u v ^ 2) +
        r u v ^ 2 * (p u v - r u v ^ 2) := by rw [← p]

private lemma discr_D (a b : ℚ) :
    (D a b).discr = -16 * delta a b := by
  have hdegree : (D a b).degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_D a b)
  rw [discr_of_degree_eq_three hdegree]
  simp [D, delta]
  ring

private lemma resultant_D_derivative (a b : ℚ) :
    (D a b).resultant (D a b).derivative = 64 * delta a b := by
  have hdegree : (D a b).degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_D a b)
  calc
    (D a b).resultant (D a b).derivative =
        (-1) ^ ((D a b).natDegree * ((D a b).natDegree - 1) / 2) *
          (D a b).leadingCoeff * (D a b).discr := by
      simpa using resultant_deriv
        (show 0 < (D a b).degree by rw [hdegree]; norm_num)
    _ = 64 * delta a b := by
      rw [natDegree_D, leadingCoeff_D, discr_D]
      norm_num
      ring

private lemma resultant_D_S (a b : ℚ) :
    (D a b).resultant (S a) = 8 * delta a b := by
  have hderivativeDegree : (D a b).derivative.natDegree = 2 := by
    rw [natDegree_derivative, natDegree_D]
  have hscale :
      (D a b).resultant (D a b).derivative 3 2 =
        2 ^ 3 * (D a b).resultant (S a) 3 2 := by
    rw [derivative_D]
    change
      (D a b).resultant (C (2 : ℚ) * S a) 3 2 =
        2 ^ 3 * (D a b).resultant (S a) 3 2
    exact resultant_C_mul_right (D a b) (S a) 3 2 (2 : ℚ)
  have hcubic := resultant_D_derivative a b
  rw [natDegree_D, hderivativeDegree] at hcubic
  rw [natDegree_D, natDegree_S]
  norm_num at hscale
  linarith

private lemma resultant_D_four_q (a b : ℚ) :
    (D a b).resultant (4 * q a b) 3 4 = -64 * delta a b ^ 2 := by
  have hqform :
      4 * q a b = -(S a ^ 2) + D a b * (12 * X) := by
    rw [q_identity]
    ring
  have hmultiplier : (12 * X : ℚ[X]).natDegree ≤ 1 := by
    compute_degree!
  have hadd :
      (D a b).resultant (-(S a ^ 2) + D a b * (12 * X)) 3 4 =
        (D a b).resultant (-(S a ^ 2)) 3 4 :=
    resultant_add_mul_right (D a b) (-(S a ^ 2)) (12 * X) 3 4
      (by omega) (by rw [natDegree_D])
  have hscale :
      (D a b).resultant (-(S a ^ 2)) 3 4 =
        -(D a b).resultant (S a ^ 2) 3 4 := by
    have h := resultant_C_mul_right (D a b) (S a ^ 2) 3 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hmul :
      (D a b).resultant (S a ^ 2) 3 4 =
        (D a b).resultant (S a) 3 2 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_S] using
      resultant_mul_right (D a b) (S a) (S a) 3 (by rw [natDegree_D])
  have hDS := resultant_D_S a b
  rw [natDegree_D, natDegree_S] at hDS
  rw [hqform, hadd, hscale, hmul, hDS]
  ring

private lemma resultant_D_q (a b : ℚ) :
    (D a b).resultant (q a b) = -delta a b ^ 2 := by
  have hscale :
      (D a b).resultant (4 * q a b) 3 4 =
        4 ^ 3 * (D a b).resultant (q a b) 3 4 := by
    change
      (D a b).resultant (C (4 : ℚ) * q a b) 3 4 =
        4 ^ 3 * (D a b).resultant (q a b) 3 4
    exact resultant_C_mul_right (D a b) (q a b) 3 4 (4 : ℚ)
  have hfour := resultant_D_four_q a b
  rw [natDegree_D, natDegree_q]
  rw [hfour] at hscale
  norm_num at hscale
  linarith

private lemma resultant_r_q (a b : ℚ) :
    (r a b).resultant (q a b) = delta a b ^ 4 := by
  have hrform :
      r a b = -(D a b ^ 2) + q a b * S a := by
    rw [← r_identity]
    ring
  have hadd :
      (-(D a b ^ 2) + q a b * S a).resultant (q a b) 6 4 =
        (-(D a b ^ 2)).resultant (q a b) 6 4 :=
    resultant_add_mul_left (-(D a b ^ 2)) (q a b) (S a) 6 4
      (by rw [natDegree_S]) (by rw [natDegree_q])
  have hscale :
      (-(D a b ^ 2)).resultant (q a b) 6 4 =
        (D a b ^ 2).resultant (q a b) 6 4 := by
    have h := resultant_C_mul_left (D a b ^ 2) (q a b) 6 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at h
    norm_num at h
    exact h
  have hmul :
      (D a b ^ 2).resultant (q a b) 6 4 =
        (D a b).resultant (q a b) 3 4 ^ 2 := by
    rw [pow_two, pow_two]
    simpa [natDegree_D] using
      resultant_mul_left (D a b) (D a b) (q a b) 4 (by rw [natDegree_q])
  have hDq := resultant_D_q a b
  rw [natDegree_D, natDegree_q] at hDq
  rw [natDegree_r, natDegree_q, hrform, hadd, hscale, hmul, hDq]
  ring

private lemma resultant_s_q (a b : ℚ) :
    (s a b).resultant (q a b) = delta a b ^ 16 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hD : D a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D a b).natDegree by rw [natDegree_D]; norm_num)
  have hsform :
      s a b = -(r a b ^ 3 * D a b ^ 2) + q a b * (p a b * q a b ^ 2) := by
    rw [s]
    ring
  have hmultiplier : (p a b * q a b ^ 2).natDegree ≤ 20 := by
    rw [natDegree_mul
      (ne_zero_of_natDegree_gt
        (show 0 < (p a b).natDegree by rw [natDegree_p]; norm_num))
      (pow_ne_zero 2 hq), natDegree_pow, natDegree_p, natDegree_q]
  have hadd :
      (-(r a b ^ 3 * D a b ^ 2) + q a b * (p a b * q a b ^ 2)).resultant
          (q a b) 24 4 =
        (-(r a b ^ 3 * D a b ^ 2)).resultant (q a b) 24 4 :=
    resultant_add_mul_left (-(r a b ^ 3 * D a b ^ 2)) (q a b)
      (p a b * q a b ^ 2) 24 4 (by omega) (by rw [natDegree_q])
  have hscale :
      (-(r a b ^ 3 * D a b ^ 2)).resultant (q a b) 24 4 =
        (r a b ^ 3 * D a b ^ 2).resultant (q a b) 24 4 := by
    have hh := resultant_C_mul_left (r a b ^ 3 * D a b ^ 2) (q a b) 24 4 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hmul :
      (r a b ^ 3 * D a b ^ 2).resultant (q a b) 24 4 =
        (r a b ^ 3).resultant (q a b) 18 4 *
          (D a b ^ 2).resultant (q a b) 6 4 := by
    have hr3deg : (r a b ^ 3).natDegree = 18 := by
      rw [natDegree_pow, natDegree_r]
    have hD2deg : (D a b ^ 2).natDegree = 6 := by
      rw [natDegree_pow, natDegree_D]
    have hh := resultant_mul_left (r a b ^ 3) (D a b ^ 2) (q a b) 4
      (by rw [natDegree_q])
    rw [hr3deg, hD2deg] at hh
    norm_num at hh
    exact hh
  have hrpow :
      (r a b ^ 3).resultant (q a b) 18 4 =
        (r a b).resultant (q a b) 6 4 ^ 3 := by
    have hr3deg : (r a b ^ 3).natDegree = 18 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_pow_left (r a b) (q a b) 3 4
      (by rw [leadingCoeff_r]; norm_num) (by rw [natDegree_q])
    rw [hr3deg, natDegree_r] at hh
    exact hh
  have hDpow :
      (D a b ^ 2).resultant (q a b) 6 4 =
        (D a b).resultant (q a b) 3 4 ^ 2 := by
    have hD2deg : (D a b ^ 2).natDegree = 6 := by
      rw [natDegree_pow, natDegree_D]
    have hh := resultant_pow_left (D a b) (q a b) 2 4
      (by rw [leadingCoeff_D]; norm_num) (by rw [natDegree_q])
    rw [hD2deg, natDegree_D] at hh
    exact hh
  have hrq := resultant_r_q a b
  rw [natDegree_r, natDegree_q] at hrq
  have hDq := resultant_D_q a b
  rw [natDegree_D, natDegree_q] at hDq
  rw [natDegree_s, natDegree_q, hsform, hadd, hscale, hmul, hrpow, hDpow, hrq, hDq]
  ring

private lemma resultant_s_r (a b : ℚ) :
    (s a b).resultant (r a b) = delta a b ^ 24 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hD : D a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D a b).natDegree by rw [natDegree_D]; norm_num)
  let T : ℚ[X] := D a b ^ 2 * q a b ^ 3 - r a b ^ 2 * D a b ^ 2
  have hsform :
      s a b = -(q a b ^ 6) + r a b * T := by
    dsimp only [T]
    rw [s, p]
    ring
  have hTdeg : T.natDegree ≤ 18 := by
    dsimp only [T]
    calc
      (D a b ^ 2 * q a b ^ 3 - r a b ^ 2 * D a b ^ 2).natDegree ≤
          max (D a b ^ 2 * q a b ^ 3).natDegree
            (r a b ^ 2 * D a b ^ 2).natDegree := natDegree_sub_le _ _
      _ = 18 := by
        rw [natDegree_mul (pow_ne_zero 2 hD) (pow_ne_zero 3 hq),
          natDegree_mul (pow_ne_zero 2 hr) (pow_ne_zero 2 hD),
          natDegree_pow, natDegree_D]
        rw [natDegree_pow, natDegree_q]
        rw [natDegree_pow, natDegree_r]
        norm_num
  have hadd :
      (-(q a b ^ 6) + r a b * T).resultant (r a b) 24 6 =
        (-(q a b ^ 6)).resultant (r a b) 24 6 :=
    resultant_add_mul_left (-(q a b ^ 6)) (r a b) T 24 6
      (by omega) (by rw [natDegree_r])
  have hscale :
      (-(q a b ^ 6)).resultant (r a b) 24 6 =
        (q a b ^ 6).resultant (r a b) 24 6 := by
    have hh := resultant_C_mul_left (q a b ^ 6) (r a b) 24 6 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hqpow :
      (q a b ^ 6).resultant (r a b) 24 6 =
        (q a b).resultant (r a b) 4 6 ^ 6 := by
    have hq6deg : (q a b ^ 6).natDegree = 24 := by
      rw [natDegree_pow, natDegree_q]
    have hh := resultant_pow_left (q a b) (r a b) 6 6
      (by rw [leadingCoeff_q]; norm_num) (by rw [natDegree_r])
    rw [hq6deg, natDegree_q] at hh
    exact hh
  have hcomm := resultant_comm (q a b) (r a b) 4 6
  norm_num at hcomm
  have hrq := resultant_r_q a b
  rw [natDegree_r, natDegree_q] at hrq
  have hqr :
      (q a b).resultant (r a b) 4 6 = delta a b ^ 4 := by
    rw [hcomm, hrq]
  rw [natDegree_s, natDegree_r, hsform, hadd, hscale, hqpow, hqr]
  ring

private lemma resultant_r_p_sub_r_sq (a b : ℚ) :
    (r a b).resultant (p a b - r a b ^ 2) = delta a b ^ 12 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hform :
      p a b - r a b ^ 2 =
        -(q a b ^ 3) + r a b * (D a b ^ 2 - r a b) := by
    rw [p]
    ring
  have hmultiplier : (D a b ^ 2 - r a b).natDegree ≤ 6 := by
    calc
      (D a b ^ 2 - r a b).natDegree ≤
          max (D a b ^ 2).natDegree (r a b).natDegree := natDegree_sub_le _ _
      _ = 6 := by
        rw [natDegree_pow, natDegree_D, natDegree_r]
        norm_num
  have hadd :
      (r a b).resultant (-(q a b ^ 3) + r a b * (D a b ^ 2 - r a b)) 6 12 =
        (r a b).resultant (-(q a b ^ 3)) 6 12 :=
    resultant_add_mul_right (r a b) (-(q a b ^ 3)) (D a b ^ 2 - r a b) 6 12
      (by omega) (by rw [natDegree_r])
  have hscale :
      (r a b).resultant (-(q a b ^ 3)) 6 12 =
        (r a b).resultant (q a b ^ 3) 6 12 := by
    have hh := resultant_C_mul_right (r a b) (q a b ^ 3) 6 12 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hqpow :
      (r a b).resultant (q a b ^ 3) 6 12 =
        (r a b).resultant (q a b) 6 4 ^ 3 := by
    have hq3deg : (q a b ^ 3).natDegree = 12 := by
      rw [natDegree_pow, natDegree_q]
    have hh := resultant_pow_right (r a b) (q a b) 6 3
      (by rw [natDegree_r]) (by rw [leadingCoeff_q]; norm_num)
    rw [hq3deg, natDegree_q] at hh
    exact hh
  have hrq := resultant_r_q a b
  rw [natDegree_r, natDegree_q] at hrq
  rw [natDegree_r, natDegree_p_sub_r_sq, hform, hadd, hscale, hqpow, hrq]
  ring

private lemma resultant_s_p_sub_r_sq (a b : ℚ) :
    (s a b).resultant (p a b - r a b ^ 2) = delta a b ^ 48 := by
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hsform :
      s a b = -(r a b ^ 4) +
        (p a b - r a b ^ 2) * (q a b ^ 3 - r a b ^ 2) := by
    rw [s, p]
    ring
  have hmultiplier : (q a b ^ 3 - r a b ^ 2).natDegree ≤ 12 := by
    calc
      (q a b ^ 3 - r a b ^ 2).natDegree ≤
          max (q a b ^ 3).natDegree (r a b ^ 2).natDegree := natDegree_sub_le _ _
      _ = 12 := by
        rw [natDegree_pow, natDegree_q]
        rw [natDegree_pow, natDegree_r]
        norm_num
  have hadd :
      (-(r a b ^ 4) +
          (p a b - r a b ^ 2) * (q a b ^ 3 - r a b ^ 2)).resultant
            (p a b - r a b ^ 2) 24 12 =
        (-(r a b ^ 4)).resultant (p a b - r a b ^ 2) 24 12 :=
    resultant_add_mul_left (-(r a b ^ 4)) (p a b - r a b ^ 2)
      (q a b ^ 3 - r a b ^ 2) 24 12
      (by omega) (by rw [natDegree_p_sub_r_sq])
  have hscale :
      (-(r a b ^ 4)).resultant (p a b - r a b ^ 2) 24 12 =
        (r a b ^ 4).resultant (p a b - r a b ^ 2) 24 12 := by
    have hh := resultant_C_mul_left (r a b ^ 4) (p a b - r a b ^ 2) 24 12 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hrpow :
      (r a b ^ 4).resultant (p a b - r a b ^ 2) 24 12 =
        (r a b).resultant (p a b - r a b ^ 2) 6 12 ^ 4 := by
    have hr4deg : (r a b ^ 4).natDegree = 24 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_pow_left (r a b) (p a b - r a b ^ 2) 4 12
      (by rw [leadingCoeff_r]; norm_num) (by rw [natDegree_p_sub_r_sq])
    rw [hr4deg, natDegree_r] at hh
    exact hh
  have hrh := resultant_r_p_sub_r_sq a b
  rw [natDegree_r, natDegree_p_sub_r_sq] at hrh
  rw [natDegree_s, natDegree_p_sub_r_sq, hsform, hadd, hscale, hrpow, hrh]
  ring

private lemma resultant_s_J (a b : ℚ) (hdelta : delta a b ≠ 0) :
    (s a b).resultant (J a b) = delta a b ^ 80 := by
  have hs : s a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (s a b).natDegree by rw [natDegree_s]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hform :
      q a b * J a b =
        r a b ^ 2 * (p a b - r a b ^ 2) + s a b * 2 := by
    rw [q_mul_J]
    ring
  have hadd :
      (s a b).resultant
          (r a b ^ 2 * (p a b - r a b ^ 2) + s a b * 2) 24 24 =
        (s a b).resultant (r a b ^ 2 * (p a b - r a b ^ 2)) 24 24 := by
    have htwo : (2 : ℚ[X]).natDegree ≤ 0 := by compute_degree!
    exact resultant_add_mul_right (s a b)
      (r a b ^ 2 * (p a b - r a b ^ 2)) 2 24 24
      (by omega) (by rw [natDegree_s])
  have hleft :
      (s a b).resultant (q a b * J a b) 24 24 =
        (s a b).resultant (q a b) 24 4 *
          (s a b).resultant (J a b) 24 20 := by
    simpa [natDegree_q, natDegree_J] using
      resultant_mul_right (s a b) (q a b) (J a b) 24
        (by rw [natDegree_s])
  have hright :
      (s a b).resultant (r a b ^ 2 * (p a b - r a b ^ 2)) 24 24 =
        (s a b).resultant (r a b ^ 2) 24 12 *
          (s a b).resultant (p a b - r a b ^ 2) 24 12 := by
    have hr2deg : (r a b ^ 2).natDegree = 12 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_mul_right (s a b) (r a b ^ 2)
      (p a b - r a b ^ 2) 24 (by rw [natDegree_s])
    rw [hr2deg, natDegree_p_sub_r_sq] at hh
    exact hh
  have hrpow :
      (s a b).resultant (r a b ^ 2) 24 12 =
        (s a b).resultant (r a b) 24 6 ^ 2 := by
    have hr2deg : (r a b ^ 2).natDegree = 12 := by
      rw [natDegree_pow, natDegree_r]
    have hh := resultant_pow_right (s a b) (r a b) 24 2
      (by rw [natDegree_s]) (by rw [leadingCoeff_r]; norm_num)
    rw [hr2deg, natDegree_r] at hh
    exact hh
  have hmaster :
      (s a b).resultant (q a b) 24 4 *
          (s a b).resultant (J a b) 24 20 =
        (s a b).resultant (r a b) 24 6 ^ 2 *
          (s a b).resultant (p a b - r a b ^ 2) 24 12 := by
    calc
      _ = (s a b).resultant (q a b * J a b) 24 24 := hleft.symm
      _ = (s a b).resultant
          (r a b ^ 2 * (p a b - r a b ^ 2) + s a b * 2) 24 24 := by rw [hform]
      _ = (s a b).resultant (r a b ^ 2 * (p a b - r a b ^ 2)) 24 24 := hadd
      _ = _ := by rw [hright, hrpow]
  have hsq := resultant_s_q a b
  rw [natDegree_s, natDegree_q] at hsq
  have hsr := resultant_s_r a b
  rw [natDegree_s, natDegree_r] at hsr
  have hsh := resultant_s_p_sub_r_sq a b
  rw [natDegree_s, natDegree_p_sub_r_sq] at hsh
  rw [hsq, hsr, hsh] at hmaster
  have hpow : delta a b ^ 16 ≠ 0 := pow_ne_zero 16 hdelta
  rw [natDegree_s, natDegree_J]
  apply mul_left_cancel₀ hpow
  calc
    delta a b ^ 16 * (s a b).resultant (J a b) 24 20 =
        (delta a b ^ 24) ^ 2 * delta a b ^ 48 := hmaster
    _ = delta a b ^ 16 * delta a b ^ 80 := by ring

private lemma resultant_s_D (a b : ℚ) :
    (s a b).resultant (D a b) = -delta a b ^ 12 := by
  have hq : q a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (q a b).natDegree by rw [natDegree_q]; norm_num)
  have hr : r a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (r a b).natDegree by rw [natDegree_r]; norm_num)
  have hD : D a b ≠ 0 :=
    ne_zero_of_natDegree_gt (show 0 < (D a b).natDegree by rw [natDegree_D]; norm_num)
  let T : ℚ[X] := D a b * (r a b * q a b ^ 3 - r a b ^ 3)
  have hsform :
      s a b = -(q a b ^ 6) + D a b * T := by
    dsimp only [T]
    rw [s, p]
    ring
  have hTdeg : T.natDegree ≤ 21 := by
    dsimp only [T]
    calc
      (D a b * (r a b * q a b ^ 3 - r a b ^ 3)).natDegree ≤
          (D a b).natDegree +
            (r a b * q a b ^ 3 - r a b ^ 3).natDegree := natDegree_mul_le
      _ ≤ (D a b).natDegree +
          max (r a b * q a b ^ 3).natDegree (r a b ^ 3).natDegree := by
            gcongr
            exact natDegree_sub_le _ _
      _ = 21 := by
        rw [natDegree_D, natDegree_mul hr (pow_ne_zero 3 hq),
          natDegree_pow, natDegree_r]
        rw [natDegree_pow, natDegree_q]
        rw [natDegree_r]
        norm_num
  have hadd :
      (-(q a b ^ 6) + D a b * T).resultant (D a b) 24 3 =
        (-(q a b ^ 6)).resultant (D a b) 24 3 :=
    resultant_add_mul_left (-(q a b ^ 6)) (D a b) T 24 3
      (by omega) (by rw [natDegree_D])
  have hscale :
      (-(q a b ^ 6)).resultant (D a b) 24 3 =
        -(q a b ^ 6).resultant (D a b) 24 3 := by
    have hh := resultant_C_mul_left (q a b ^ 6) (D a b) 24 3 (-1 : ℚ)
    rw [C_neg, C_1, neg_mul, one_mul] at hh
    norm_num at hh
    exact hh
  have hqpow :
      (q a b ^ 6).resultant (D a b) 24 3 =
        (q a b).resultant (D a b) 4 3 ^ 6 := by
    have hq6deg : (q a b ^ 6).natDegree = 24 := by
      rw [natDegree_pow, natDegree_q]
    have hh := resultant_pow_left (q a b) (D a b) 6 3
      (by rw [leadingCoeff_q]; norm_num) (by rw [natDegree_D])
    rw [hq6deg, natDegree_q] at hh
    exact hh
  have hcomm := resultant_comm (q a b) (D a b) 4 3
  norm_num at hcomm
  have hDq := resultant_D_q a b
  rw [natDegree_D, natDegree_q] at hDq
  have hqD :
      (q a b).resultant (D a b) 4 3 = -delta a b ^ 2 := by
    rw [hcomm, hDq]
  rw [natDegree_s, natDegree_D, hsform, hadd, hscale, hqpow, hqD]
  ring

private lemma resultant_s_derivative (a b : ℚ) :
    (s a b).resultant (s a b).derivative =
      -(7 ^ 24 * delta a b ^ 92) := by
  have hderivativeDegree : (s a b).derivative.natDegree = 23 := by
    rw [natDegree_derivative, natDegree_s]
  have hderivativeForm :
      (s a b).derivative = C (7 : ℚ) * (D a b * J a b) := by
    rw [derivative_s]
    simp only [map_ofNat]
    ring
  have hscale :
      (s a b).resultant (s a b).derivative 24 23 =
        7 ^ 24 * (s a b).resultant (D a b * J a b) 24 23 := by
    rw [hderivativeForm]
    exact resultant_C_mul_right (s a b) (D a b * J a b) 24 23 (7 : ℚ)
  have hmul :
      (s a b).resultant (D a b * J a b) 24 23 =
        (s a b).resultant (D a b) 24 3 *
          (s a b).resultant (J a b) 24 20 := by
    simpa [natDegree_D, natDegree_J] using
      resultant_mul_right (s a b) (D a b) (J a b) 24 (by rw [natDegree_s])
  have hsD := resultant_s_D a b
  rw [natDegree_s, natDegree_D] at hsD
  by_cases hdelta : delta a b = 0
  · rw [natDegree_s, hderivativeDegree, hscale, hmul, hsD, hdelta]
    norm_num
  · have hsJ := resultant_s_J a b hdelta
    rw [natDegree_s, natDegree_J] at hsJ
    rw [natDegree_s, hderivativeDegree, hscale, hmul, hsD, hsJ]
    ring

private theorem discr_s (a b : ℚ) :
    (s a b).discr = -(7 ^ 23 * delta a b ^ 92) := by
  have hdegree : (s a b).degree = 24 :=
    (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mpr (natDegree_s a b)
  have hresultant :
      (s a b).resultant (s a b).derivative =
        (7 : ℚ) * (s a b).discr := by
    calc
      (s a b).resultant (s a b).derivative =
          (-1) ^ ((s a b).natDegree * ((s a b).natDegree - 1) / 2) *
            (s a b).leadingCoeff * (s a b).discr := by
        simpa using resultant_deriv
          (show 0 < (s a b).degree by rw [hdegree]; norm_num)
      _ = (7 : ℚ) * (s a b).discr := by
        rw [natDegree_s, leadingCoeff_s]
        norm_num
  have hcomputed := resultant_s_derivative a b
  rw [hresultant] at hcomputed
  linarith

private lemma normal_D (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    D (W.b₄ / 2) (W.b₆ / 4) = W.Ψ₂Sq := by
  have hb₄ : 2 * (W.b₄ / 2) = W.b₄ := by ring
  have hb₆ : 4 * (W.b₆ / 4) = W.b₆ := by ring
  have hCb₄ :
      (2 : ℚ[X]) * C (W.b₄ / 2) = C W.b₄ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₄
  have hCb₆ :
      (4 : ℚ[X]) * C (W.b₆ / 4) = C W.b₆ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₆
  simp [D, WeierstrassCurve.Ψ₂Sq, hb₂]
  simp only [map_ofNat]
  linear_combination 2 * X * hCb₄ + hCb₆

private lemma normal_q (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    q (W.b₄ / 2) (W.b₆ / 4) = W.Ψ₃ := by
  have hb₄ : 2 * (W.b₄ / 2) = W.b₄ := by ring
  have hb₆ : 4 * (W.b₆ / 4) = W.b₆ := by ring
  have hCb₄ :
      (2 : ℚ[X]) * C (W.b₄ / 2) = C W.b₄ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₄
  have hCb₆ :
      (4 : ℚ[X]) * C (W.b₆ / 4) = C W.b₆ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₆
  have hb₈ : 4 * W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation, hb₂]
    ring
  have hCb₈ :
      (4 : ℚ[X]) * C W.b₈ = -(C W.b₄ ^ 2) := by
    simpa only [map_ofNat, C_mul, C_neg, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₈
  have ha₂ :
      C (W.b₄ / 2) ^ 2 = -C W.b₈ := by
    apply mul_left_cancel₀ (show (4 : ℚ[X]) ≠ 0 by norm_num)
    linear_combination
      hCb₈ + (2 * C (W.b₄ / 2) + C W.b₄) * hCb₄
  simp [q, WeierstrassCurve.Ψ₃, hb₂]
  linear_combination
    3 * X ^ 2 * hCb₄ + 3 * X * hCb₆ - ha₂

private lemma normal_r (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    r (W.b₄ / 2) (W.b₆ / 4) = W.preΨ₄ := by
  have hb₄ : 2 * (W.b₄ / 2) = W.b₄ := by ring
  have hCb₄ :
      (2 : ℚ[X]) * C (W.b₄ / 2) = C W.b₄ := by
    simpa only [map_ofNat, C_mul] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₄
  have hS :
      S (W.b₄ / 2) = 6 * X ^ 2 + C W.b₄ := by
    simp [S]
    linear_combination hCb₄
  have hb₈ : 4 * W.b₈ = -W.b₄ ^ 2 := by
    rw [W.b_relation, hb₂]
    ring
  have hCb₈ :
      (4 : ℚ[X]) * C W.b₈ = -(C W.b₄ ^ 2) := by
    simpa only [map_ofNat, C_mul, C_neg, C_pow] using
      congrArg (fun z : ℚ ↦ (C z : ℚ[X])) hb₈
  have hW :
      W.preΨ₄ + W.Ψ₂Sq ^ 2 =
        W.Ψ₃ * (6 * X ^ 2 + C W.b₄) := by
    simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
      WeierstrassCurve.Ψ₃, hb₂]
    simp only [map_ofNat]
    linear_combination X ^ 2 * hCb₈
  have hshort := r_identity (W.b₄ / 2) (W.b₆ / 4)
  rw [normal_D W hb₂, normal_q W hb₂, hS] at hshort
  linear_combination hshort - hW

private lemma preΨ_five (W : WeierstrassCurve ℚ) :
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num, W.preΨ'_odd 0]
  norm_num

private lemma preΨ_seven (W : WeierstrassCurve ℚ) :
    W.preΨ' 7 =
      W.preΨ' 5 * W.Ψ₃ ^ 3 - W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
  rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num, W.preΨ'_odd 1]
  norm_num

private lemma normal_p (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    p (W.b₄ / 2) (W.b₆ / 4) = W.preΨ' 5 := by
  rw [p, normal_r W hb₂, normal_D W hb₂, normal_q W hb₂, preΨ_five]

private lemma normal_s (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    s (W.b₄ / 2) (W.b₆ / 4) = W.preΨ' 7 := by
  rw [s, normal_p W hb₂, normal_q W hb₂, normal_r W hb₂,
    normal_D W hb₂, preΨ_seven]

private lemma normal_delta (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    delta (W.b₄ / 2) (W.b₆ / 4) = -W.Δ := by
  simp [delta, WeierstrassCurve.Δ, hb₂]
  ring

private lemma normal_discr_seven
    (W : WeierstrassCurve ℚ) (hb₂ : W.b₂ = 0) :
    (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92) := by
  have h := discr_s (W.b₄ / 2) (W.b₆ / 4)
  rw [normal_s W hb₂, normal_delta W hb₂] at h
  rw [(show Even 92 by decide).neg_pow] at h
  norm_num at h ⊢
  exact h

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

private lemma translation_preΨ_seven (W : WeierstrassCurve ℚ) (r : ℚ) :
    (translation r • W).preΨ' 7 = (W.preΨ' 7).taylor r := by
  rw [preΨ_seven, preΨ_seven]
  rw [translation_preΨ_five, translation_Ψ₃, translation_preΨ₄,
    translation_Ψ₂Sq]
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

/-- The discriminant of the universal seventh division polynomial over `ℚ`. -/
theorem discr_preΨ_seven (W : WeierstrassCurve ℚ) :
    (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92) := by
  let r : ℚ := -W.b₂ / 12
  let W₀ : WeierstrassCurve ℚ := translation r • W
  have hb₂ : W₀.b₂ = 0 := by
    simp [W₀, translation, r, WeierstrassCurve.variableChange_b₂]
    ring
  have hnormal := normal_discr_seven W₀ hb₂
  have hpolynomial := translation_preΨ_seven W r
  have hΔ : W₀.Δ = W.Δ := by
    simp [W₀, translation, WeierstrassCurve.variableChange_Δ]
  calc
    (W.preΨ' 7).discr = ((W.preΨ' 7).taylor r).discr :=
      (discr_taylor (W.preΨ' 7) r).symm
    _ = (W₀.preΨ' 7).discr := by rw [← hpolynomial]
    _ = -((7 : ℚ) ^ 23 * W₀.Δ ^ 92) := hnormal
    _ = -((7 : ℚ) ^ 23 * W.Δ ^ 92) := by rw [hΔ]

end MazurTorsion.DivisionPolynomialDiscriminantSeven
