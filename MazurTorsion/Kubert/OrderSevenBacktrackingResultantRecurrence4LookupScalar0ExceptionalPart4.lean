/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0ExceptionalPart4Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C0_coeff_143
  recurrence4C0_coeff_144
  recurrence4C0_coeff_145
  recurrence4C0_coeff_146
  recurrence4C0_coeff_147
  recurrence4C0_coeff_148
  recurrence4C0_coeff_149
  recurrence4C0_coeff_150
  recurrence4C0_coeff_151
  recurrence4C0_coeff_152
  recurrence4C0_coeff_153
  recurrence4ExceptionalProduct_coeff_359
  recurrence4ExceptionalProduct_coeff_360
  recurrence4ExceptionalProduct_coeff_361
  recurrence4ExceptionalProduct_coeff_362
  recurrence4ExceptionalProduct_coeff_363
  recurrence4ExceptionalProduct_coeff_364
  recurrence4ExceptionalProduct_coeff_365
  recurrence4ExceptionalProduct_coeff_366
  recurrence4ExceptionalProduct_coeff_367
  recurrence4ExceptionalProduct_coeff_368
  recurrence4ExceptionalProduct_coeff_369

private theorem recurrence4Scalar0Exceptional_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (512 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (512 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_512 :
    recurrence4Scalar0Exceptional.coeff 512 =
      -((11517129517480417801414688036939255181790239768360014 * 10 ^ 70 +
        7862395820721645774726157517875536204023057097043560319575528256843940) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (512 - x)) = _
  rw [show 513 = 359 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 11 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (513 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (513 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_513 :
    recurrence4Scalar0Exceptional.coeff 513 =
      -((213423475091178243086164029875011357516819119646 * 10 ^ 70 +
        2103435211051950318960749272896641715084226993441354781191556243951307) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (513 - x)) = _
  rw [show 514 = 360 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 10 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (514 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (514 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (514 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_514 :
    recurrence4Scalar0Exceptional.coeff 514 =
      -((2200642527219955333940192111936282307983670 * 10 ^ 70 +
        7436673976576943696588490104321010213252874677484533286487160858233388) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (514 - x)) = _
  rw [show 515 = 361 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 9 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_515_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (515 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (515 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_515_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (515 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (515 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_515 :
    recurrence4Scalar0Exceptional.coeff 515 =
      -((11836356098843030629177067292715890952 * 10 ^ 70 +
        5390165156486361817867117263908749974763558974746916927355066261034562) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 516,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (515 - x)) = _
  rw [show 516 = 362 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 8 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_515_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_515_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_516_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (516 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (516 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_516_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (516 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (516 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_516 :
    recurrence4Scalar0Exceptional.coeff 516 =
      -((31363938704952387897563622882500 * 10 ^ 70 +
        4721679758257200103229679956934604392905390929697515871566468440637587) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 517,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (516 - x)) = _
  rw [show 517 = 363 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 7 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_516_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_516_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_517_prefix_zero :
    (∑ x ∈ Finset.range 364,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (517 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (517 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_517_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (517 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (517 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_517 :
    recurrence4Scalar0Exceptional.coeff 517 =
      -((37092707946107488258680198 * 10 ^ 70 +
        0066005208136182685107900662984020745937553279797194523277244458719897) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 518,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (517 - x)) = _
  rw [show 518 = 364 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 6 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_517_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_517_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_518_prefix_zero :
    (∑ x ∈ Finset.range 365,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (518 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (518 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_518_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (518 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (518 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_518 :
    recurrence4Scalar0Exceptional.coeff 518 =
      -((19516984907534701630 * 10 ^ 70 +
        7689924873783483102689907540723527423841298342201877161410833427460940) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 519,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (518 - x)) = _
  rw [show 519 = 365 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 5 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_518_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_518_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_519_prefix_zero :
    (∑ x ∈ Finset.range 366,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (519 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (519 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_519_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (519 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (519 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_519 :
    recurrence4Scalar0Exceptional.coeff 519 =
      -((4094697099372 * 10 ^ 70 +
        9158490740301160866359678254488764900587611266959019813993256830428207) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 520,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (519 - x)) = _
  rw [show 520 = 366 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 4 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_519_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_519_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_520_prefix_zero :
    (∑ x ∈ Finset.range 367,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (520 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (520 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_520_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (520 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (520 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_520 :
    recurrence4Scalar0Exceptional.coeff 520 =
      -((187689 * 10 ^ 70 +
        6782590235998921385100639808194584658846522760398060842328999737639737) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 521,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (520 - x)) = _
  rw [show 521 = 367 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 3 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_520_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_520_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_521_prefix_zero :
    (∑ x ∈ Finset.range 368,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (521 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (521 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_521_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (521 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (521 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_521 :
    recurrence4Scalar0Exceptional.coeff 521 =
      (-31039604684474103979698339168043885691520302472662404876184751208797 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 522,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (521 - x)) = _
  rw [show 522 = 368 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 2 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_521_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_521_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_522_prefix_zero :
    (∑ x ∈ Finset.range 369,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (522 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (522 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_522_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (522 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (522 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_522 :
    recurrence4Scalar0Exceptional.coeff 522 =
      (-171910651576204265134294769707019620352195984168302791988841 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 523,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (522 - x)) = _
  rw [show 523 = 369 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 1 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_522_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_522_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
