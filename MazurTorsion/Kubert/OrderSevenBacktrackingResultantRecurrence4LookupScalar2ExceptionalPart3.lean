/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C2_coeff_140
  recurrence4C2_coeff_141
  recurrence4C2_coeff_142
  recurrence4C2_coeff_143
  recurrence4C2_coeff_144
  recurrence4C2_coeff_145
  recurrence4ExceptionalProduct_coeff_364
  recurrence4ExceptionalProduct_coeff_365
  recurrence4ExceptionalProduct_coeff_366
  recurrence4ExceptionalProduct_coeff_367
  recurrence4ExceptionalProduct_coeff_368
  recurrence4ExceptionalProduct_coeff_369

private theorem recurrence4Scalar2Exceptional_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 364,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (509 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_509 :
    recurrence4Scalar2Exceptional.coeff 509 =
      -((3286127262682039007830194009 * 10 ^ 70 +
        7252333216864906666914134348701962631713958065318777628611718246924102) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (509 - x)) = _
  rw [show 510 = 364 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 6 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_509_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 365,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (510 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_510 :
    recurrence4Scalar2Exceptional.coeff 510 =
      -((2076904240066505215127 * 10 ^ 70 +
        3788953879459631752678301240927480122043782278961977386044038067585468) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (510 - x)) = _
  rw [show 511 = 365 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 5 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_510_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 366,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (511 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_511 :
    recurrence4Scalar2Exceptional.coeff 511 =
      -((529267548547218 * 10 ^ 70 +
        9708428880715532513914162398938068069892536116436912506037075619677750) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (511 - x)) = _
  rw [show 512 = 366 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 4 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_511_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 367,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (512 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_512 :
    recurrence4Scalar2Exceptional.coeff 512 =
      -((39070898 * 10 ^ 70 +
        6620426043111253058945577805156479327197819386653956563973635407743647) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (512 - x)) = _
  rw [show 513 = 367 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 3 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_512_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 368,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (513 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_513 :
    recurrence4Scalar2Exceptional.coeff 513 =
      (-8317359457646468060504239164769546151922568984850618923928186578545690 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (513 - x)) = _
  rw [show 514 = 368 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 2 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_513_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 369,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (514 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (514 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_514 :
    recurrence4Scalar2Exceptional.coeff 514 =
      (-53701746906274322922389292413329009090012362832185396756764943 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (514 - x)) = _
  rw [show 515 = 369 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 1 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_514_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
