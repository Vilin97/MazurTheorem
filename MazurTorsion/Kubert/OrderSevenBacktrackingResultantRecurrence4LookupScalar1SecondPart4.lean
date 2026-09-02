/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart4Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_170
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346

private theorem recurrence4Scalar1Second_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (514 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 342,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (514 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_514 :
    recurrence4Scalar1Second.coeff 514 =
      -((2124577144479389350989 * 10 ^ 70 +
        1421910258750192946595912664169085422830426514630592892161218088608522) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (514 - x)) = _
  rw [show 515 = 168 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 5 +
      342 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_515_prefix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (515 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (515 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_515_suffix_zero :
    (∑ x ∈ Finset.range 343,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (515 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_515 :
    recurrence4Scalar1Second.coeff 515 =
      -((69212679116566 * 10 ^ 70 +
        8316374112936684062489547928113762811047961966599025822687022948777622) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 516,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (515 - x)) = _
  rw [show 516 = 169 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 4 +
      343 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_515_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_515_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_516_prefix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (516 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (516 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_516_suffix_zero :
    (∑ x ∈ Finset.range 344,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (516 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_516 :
    recurrence4Scalar1Second.coeff 516 =
      ((23288281 * 10 ^ 70 +
        4666081459555843015416454507842443935586612970302828568259350617084102) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 517,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (516 - x)) = _
  rw [show 517 = 170 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 3 +
      344 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_516_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_516_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_517_prefix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (517 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (517 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_517_suffix_zero :
    (∑ x ∈ Finset.range 345,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (517 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_517 :
    recurrence4Scalar1Second.coeff 517 =
      (-2311079737304475474778387527364986089442482602123155564622613353935561 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 518,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (517 - x)) = _
  rw [show 518 = 171 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 2 +
      345 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_517_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_517_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_518_prefix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (518 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (518 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_518_suffix_zero :
    (∑ x ∈ Finset.range 346,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (518 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_518 :
    recurrence4Scalar1Second.coeff 518 =
      (605677739565168694016558168915973172692467089922983284195081 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 519,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (518 - x)) = _
  rw [show 519 = 172 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 1 +
      346 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_518_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_518_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
