/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar1First_coeff_515_prefix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (515 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (515 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_515_suffix_zero :
    (∑ x ∈ Finset.range 339,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (515 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_515 :
    recurrence4Scalar1First.coeff 515 =
      -((181212686851806 * 10 ^ 70 +
        6344919186569342232829911529605665353011424712188523895122698603624476) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 516,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (515 - x)) = _
  rw [show 516 = 173 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 4 +
      339 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_515_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_515_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_516_prefix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (516 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (516 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_516_suffix_zero :
    (∑ x ∈ Finset.range 340,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (516 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_516 :
    recurrence4Scalar1First.coeff 516 =
      ((3112088 * 10 ^ 70 +
        0024076210089255424221765049947752308546181515182446098530902092975258) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 517,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (516 - x)) = _
  rw [show 517 = 174 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 3 +
      340 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_516_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_516_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_517_prefix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (517 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (517 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_517_suffix_zero :
    (∑ x ∈ Finset.range 341,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (517 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_517 :
    recurrence4Scalar1First.coeff 517 =
      (565340432351615605706325199656968257027009433565882101368638158807811 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 518,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (517 - x)) = _
  rw [show 518 = 175 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 2 +
      341 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_517_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_517_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_518_prefix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (518 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (518 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_518_suffix_zero :
    (∑ x ∈ Finset.range 342,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (518 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_518 :
    recurrence4Scalar1First.coeff 518 =
      (-4487123134918589846730950290864048652497721798445366255291870 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 519,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (518 - x)) = _
  rw [show 519 = 176 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 1 +
      342 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_518_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_518_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
