/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0MainPart4Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4QuotientConstant_coeff_336
  recurrence4QuotientConstant_coeff_337
  recurrence4QuotientConstant_coeff_338
  recurrence4QuotientConstant_coeff_339
  recurrence4QuotientConstant_coeff_340
  recurrence4QuotientConstant_coeff_341
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346

private theorem recurrence4Scalar0Main_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (512 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 336,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (512 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_512 :
    recurrence4Scalar0Main.coeff 512 =
      -((272870285242846573844689094523227413929712329041366102 * 10 ^ 70 +
        3706581450290326396071898507175122772262932519386691223790249849287260) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (512 - x)) = _
  rw [show 513 = 166 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 11 +
      336 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (513 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 337,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (513 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_513 :
    recurrence4Scalar0Main.coeff 513 =
      -((1656368155925571364160618348503806282777669671972 * 10 ^ 70 +
        1228794447102078726865276420873486050131989973210228441447860540688066) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (513 - x)) = _
  rw [show 514 = 167 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 10 +
      337 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (514 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 338,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (514 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_514 :
    recurrence4Scalar0Main.coeff 514 =
      ((42777978226840903363257184839114619849407552 * 10 ^ 70 +
        8968282412500065901348078213109645423890658613181966942924904238829005) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (514 - x)) = _
  rw [show 515 = 168 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 9 +
      338 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_515_prefix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (515 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (515 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_515_suffix_zero :
    (∑ x ∈ Finset.range 339,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (515 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_515 :
    recurrence4Scalar0Main.coeff 515 =
      -((105222414391490665018640179474158753479 * 10 ^ 70 +
        5865755855541296073024386146992382926379159463265470417214970095978096) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 516,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (515 - x)) = _
  rw [show 516 = 169 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 8 +
      339 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_515_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_515_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_516_prefix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (516 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (516 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_516_suffix_zero :
    (∑ x ∈ Finset.range 340,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (516 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_516 :
    recurrence4Scalar0Main.coeff 516 =
      -((113253420079295099416483649035862 * 10 ^ 70 +
        6010151964650554098326582594999020340406213871665051991381558997730568) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 517,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (516 - x)) = _
  rw [show 517 = 170 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 7 +
      340 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_516_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_516_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_517_prefix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (517 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (517 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_517_suffix_zero :
    (∑ x ∈ Finset.range 341,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (517 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_517 :
    recurrence4Scalar0Main.coeff 517 =
      ((322498711243117733693096516 * 10 ^ 70 +
        5278512855201717466858273509381549039361889768198579624933474636589002) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 518,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (517 - x)) = _
  rw [show 518 = 171 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 6 +
      341 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_517_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_517_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_518_prefix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (518 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (518 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_518_suffix_zero :
    (∑ x ∈ Finset.range 342,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (518 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_518 :
    recurrence4Scalar0Main.coeff 518 =
      -((69579341767222684219 * 10 ^ 70 +
        7256486167860790193561335929050107246101325259766288059630420309120945) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 519,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (518 - x)) = _
  rw [show 519 = 172 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 5 +
      342 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_518_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_518_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_519_prefix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (519 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (519 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_519_suffix_zero :
    (∑ x ∈ Finset.range 343,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (519 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_519 :
    recurrence4Scalar0Main.coeff 519 =
      -((3416495458766 * 10 ^ 70 +
        1824081894441817845239970023550396299494868350744626298312640391871414) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 520,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (519 - x)) = _
  rw [show 520 = 173 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 4 +
      343 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_519_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_519_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_520_prefix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (520 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (520 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_520_suffix_zero :
    (∑ x ∈ Finset.range 344,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (520 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_520 :
    recurrence4Scalar0Main.coeff 520 =
      ((773073 * 10 ^ 70 +
        6470348435176347572186476475552296515323759312986055159692690014152445) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 521,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (520 - x)) = _
  rw [show 521 = 174 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 3 +
      344 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_520_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_520_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_521_prefix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (521 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (521 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_521_suffix_zero :
    (∑ x ∈ Finset.range 345,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (521 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_521 :
    recurrence4Scalar0Main.coeff 521 =
      (-50476495666406024100974089931471746382920239141719789727674908114023 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 522,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (521 - x)) = _
  rw [show 522 = 175 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 2 +
      345 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_521_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_521_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_522_prefix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (522 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (522 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_522_suffix_zero :
    (∑ x ∈ Finset.range 346,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (522 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_522 :
    recurrence4Scalar0Main.coeff 522 =
      (13037144440966727697426939597995422712568075067206346450041 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 523,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (522 - x)) = _
  rw [show 523 = 176 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 1 +
      346 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_522_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_522_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
