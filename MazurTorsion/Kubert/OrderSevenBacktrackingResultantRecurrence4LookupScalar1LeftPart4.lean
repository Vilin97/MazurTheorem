/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart4Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_179
  recurrence4A1_coeff_180
  recurrence4A1_coeff_181
  recurrence4A1_coeff_182
  recurrence4A1_coeff_183
  recurrence4A1_coeff_184
  recurrence4A1_coeff_185
  recurrence4A1_coeff_186
  recurrence4A1_coeff_187
  recurrence4A1_coeff_188
  recurrence4A1_coeff_189
  recurrence4A1_coeff_190
  recurrence4LeadingSquare_coeff_317
  recurrence4LeadingSquare_coeff_318
  recurrence4LeadingSquare_coeff_319
  recurrence4LeadingSquare_coeff_320
  recurrence4LeadingSquare_coeff_321
  recurrence4LeadingSquare_coeff_322
  recurrence4LeadingSquare_coeff_323
  recurrence4LeadingSquare_coeff_324
  recurrence4LeadingSquare_coeff_325
  recurrence4LeadingSquare_coeff_326
  recurrence4LeadingSquare_coeff_327
  recurrence4LeadingSquare_coeff_328

private theorem recurrence4Scalar1Left_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (507 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (507 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_507 :
    recurrence4Scalar1Left.coeff 507 =
      ((282418050029497846408161074263766864233027819293410625266258 * 10 ^ 70 +
        2279599935421952757550001018448753724534715851627960893298113808631111) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (507 - x)) = _
  rw [show 508 = 317 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 12 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (508 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (508 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_508 :
    recurrence4Scalar1Left.coeff 508 =
      -((4464700312163327014450802551041523337853579178887915996 * 10 ^ 70 +
        3048766636643252066726042150275630674665860124517202875594477147230077) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (508 - x)) = _
  rw [show 509 = 318 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 11 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (509 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (509 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_509 :
    recurrence4Scalar1Left.coeff 509 =
      -((53197206054541567642820630827558307358353983117700 * 10 ^ 70 +
        6325352178404354155511038352890892625536380443905876818651384651764999) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (509 - x)) = _
  rw [show 510 = 319 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 10 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_509_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (510 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (510 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_510 :
    recurrence4Scalar1Left.coeff 510 =
      ((853922260578295821264700576035370066227750258 * 10 ^ 70 +
        9569614440693689882548358205912974348429555942481613141276928872996296) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (510 - x)) = _
  rw [show 511 = 320 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 9 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_510_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (511 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (511 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_511 :
    recurrence4Scalar1Left.coeff 511 =
      -((1996454667743144854026069862507209358671 * 10 ^ 70 +
        0776571697563843844700502687989659754173453070123268601207258248461365) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (511 - x)) = _
  rw [show 512 = 321 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 8 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_511_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (512 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (512 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_512 :
    recurrence4Scalar1Left.coeff 512 =
      -((4741800665475652951534851095641980 * 10 ^ 70 +
        4051208260735686490724437346575174313559863184666227513531833190533302) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (512 - x)) = _
  rw [show 513 = 322 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 7 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (513 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (513 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_513 :
    recurrence4Scalar1Left.coeff 513 =
      ((7296889776352632347808253140 * 10 ^ 70 +
        8521904392099234680384834434145104407652236391383600390476693578297617) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (513 - x)) = _
  rw [show 514 = 323 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 6 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (514 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (514 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (514 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_514 :
    recurrence4Scalar1Left.coeff 514 =
      -((1867661148314463135041 * 10 ^ 70 +
        5534006381165931989624797475560302904509541100683181489719839367135185) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (514 - x)) = _
  rw [show 515 = 324 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 5 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_515_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (515 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (515 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_515_suffix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (515 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (515 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_515 :
    recurrence4Scalar1Left.coeff 515 =
      -((338068141793463 * 10 ^ 70 +
        0873026389098247449799006523184800147209602376762417909059470251924135) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 516,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (515 - x)) = _
  rw [show 516 = 325 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 4 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_515_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_515_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_516_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (516 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (516 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_516_suffix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (516 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (516 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_516 :
    recurrence4Scalar1Left.coeff 516 =
      ((21498246 * 10 ^ 70 +
        3637121555508487754702623968909536557562407109244665710400458262238609) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 517,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (516 - x)) = _
  rw [show 517 = 326 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 3 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_516_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_516_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_517_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (517 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (517 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_517_suffix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (517 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (517 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_517 :
    recurrence4Scalar1Left.coeff 517 =
      (-2666287900015295305458274149235472678958732330604976322992876224204960 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 518,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (517 - x)) = _
  rw [show 518 = 327 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 2 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_517_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_517_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_518_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (518 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (518 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_518_suffix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (518 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (518 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_518 :
    recurrence4Scalar1Left.coeff 518 =
      (-9430486515507006953907938380010713558764573967437259715591900 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 519,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (518 - x)) = _
  rw [show 519 = 328 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 1 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_518_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_518_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
