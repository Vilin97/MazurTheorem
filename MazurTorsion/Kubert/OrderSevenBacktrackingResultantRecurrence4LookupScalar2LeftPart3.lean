/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A2_coeff_162
  recurrence4A2_coeff_163
  recurrence4A2_coeff_164
  recurrence4A2_coeff_165
  recurrence4A2_coeff_166
  recurrence4A2_coeff_167
  recurrence4A2_coeff_168
  recurrence4A2_coeff_169
  recurrence4A2_coeff_170
  recurrence4A2_coeff_171
  recurrence4A2_coeff_172
  recurrence4A2_coeff_173
  recurrence4A2_coeff_174
  recurrence4A2_coeff_175
  recurrence4A2_coeff_176
  recurrence4A2_coeff_177
  recurrence4A2_coeff_178
  recurrence4A2_coeff_179
  recurrence4A2_coeff_180
  recurrence4A2_coeff_181
  recurrence4A2_coeff_182
  recurrence4A2_coeff_183
  recurrence4A2_coeff_184
  recurrence4A2_coeff_185
  recurrence4A2_coeff_186
  recurrence4LeadingSquare_coeff_304
  recurrence4LeadingSquare_coeff_305
  recurrence4LeadingSquare_coeff_306
  recurrence4LeadingSquare_coeff_307
  recurrence4LeadingSquare_coeff_308
  recurrence4LeadingSquare_coeff_309
  recurrence4LeadingSquare_coeff_310
  recurrence4LeadingSquare_coeff_311
  recurrence4LeadingSquare_coeff_312
  recurrence4LeadingSquare_coeff_313
  recurrence4LeadingSquare_coeff_314
  recurrence4LeadingSquare_coeff_315
  recurrence4LeadingSquare_coeff_316
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

private theorem recurrence4Scalar2Left_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (490 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_490 :
    recurrence4Scalar2Left.coeff 490 =
      (((10086085793544872178092537782816748 * 10 ^ 70 +
        2356364797178367250931830117296935941093510966813637154767829814549800) * 10 ^ 70 +
        9828960556108024253464550091860472521023943835113297731109963273283912) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (490 - x)) = _
  rw [show 491 = 304 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 25 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (491 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_491 :
    recurrence4Scalar2Left.coeff 491 =
      -(((20636611583284377179909484746894 * 10 ^ 70 +
        9899704500990427913802633685327731514168512580199440909219047502234103) * 10 ^ 70 +
        3391309456926756430166871487595420561399289665823829146853779742342696) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (491 - x)) = _
  rw [show 492 = 305 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 24 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (492 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_492 :
    recurrence4Scalar2Left.coeff 492 =
      -(((29954564087151440519109559406 * 10 ^ 70 +
        5271290073429196763429732761322163822706756520998595590551336496003480) * 10 ^ 70 +
        3736152349646125266770340993474183127212845647682233892076000185776608) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (492 - x)) = _
  rw [show 493 = 306 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 23 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (493 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_493 :
    recurrence4Scalar2Left.coeff 493 =
      (((62428858359421962825789863 * 10 ^ 70 +
        9032693001561234273907348165115057053449123409737873642149464466205517) * 10 ^ 70 +
        3989194820188470353105060412041368529709893393863572634739509471017389) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (493 - x)) = _
  rw [show 494 = 307 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 22 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (494 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_494 :
    recurrence4Scalar2Left.coeff 494 =
      (((27865369450143366609178 * 10 ^ 70 +
        9062083505743764002479916945051821343731331368192947156168738839626462) * 10 ^ 70 +
        6679638873366622894828973383556234280722698391879555740809976492797293) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (494 - x)) = _
  rw [show 495 = 308 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 21 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (495 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_495 :
    recurrence4Scalar2Left.coeff 495 =
      -(((85977017939994032722 * 10 ^ 70 +
        4909601978457381317255171245137808010663808931442325607374311509345254) * 10 ^ 70 +
        1751380313047745856267247207340461649132797726592016438167479327417008) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (495 - x)) = _
  rw [show 496 = 309 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 20 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (496 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_496 :
    recurrence4Scalar2Left.coeff 496 =
      (((16055809465629630 * 10 ^ 70 +
        4631786937115965259611310789602171619095686845805682432032701725317861) * 10 ^ 70 +
        8368932467304731962042496740695898463736612209061188767639733767005271) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (496 - x)) = _
  rw [show 497 = 310 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 19 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (497 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_497 :
    recurrence4Scalar2Left.coeff 497 =
      (((28049099999243 * 10 ^ 70 +
        9304680003657247684643580304909122668726309550549775121662322232365948) * 10 ^ 70 +
        3609616013566279386756193720736789675200891645048509639009985701558712) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (497 - x)) = _
  rw [show 498 = 311 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 18 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (498 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_498 :
    recurrence4Scalar2Left.coeff 498 =
      -(((11088659327 * 10 ^ 70 +
        3526459849175142272353791283182826251328868787150665561244403151445278) * 10 ^ 70 +
        7180607677479652700520436008428295241141841759209729625227682099808083) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (498 - x)) = _
  rw [show 499 = 312 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 17 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (499 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_499 :
    recurrence4Scalar2Left.coeff 499 =
      -(((642191 * 10 ^ 70 +
        9692659753519721028232738752061745520072508418767083511230187820102647) * 10 ^ 70 +
        0192783151434293189764109288053293062898479957026913973772920949955410) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (499 - x)) = _
  rw [show 500 = 313 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 16 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (500 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_500 :
    recurrence4Scalar2Left.coeff 500 =
      (((575 * 10 ^ 70 +
        8609534845188867472877076377398414046056127778412572534189915584183058) * 10 ^ 70 +
        3962888990751294287209694595028544739981881681687848379238625461940315) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (500 - x)) = _
  rw [show 501 = 314 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 15 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (501 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_501 :
    recurrence4Scalar2Left.coeff 501 =
      -((421613022016667585553824962207221254526644125720800712440485696012206 * 10 ^ 70 +
        4115861837027915881462426677475483108565003686348214186382376001498899) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (501 - x)) = _
  rw [show 502 = 315 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 14 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (502 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_502 :
    recurrence4Scalar2Left.coeff 502 =
      -((23364199964238631853978882054582358993483250929237019892504347195 * 10 ^ 70 +
        3846888889662252427707872567526631810651299215622795744264631664286311) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (502 - x)) = _
  rw [show 503 = 316 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 13 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (503 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_503 :
    recurrence4Scalar2Left.coeff 503 =
      ((2152663238414283800708013876322806183781885692170644355872438 * 10 ^ 70 +
        9230416053645822977074367033584639118278764768533908913030962402260234) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (503 - x)) = _
  rw [show 504 = 317 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 12 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (504 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_504 :
    recurrence4Scalar2Left.coeff 504 =
      -((25371424140789062144724731741762708151348153637434800028 * 10 ^ 70 +
        4309714477650490845039821272051795741145218094135525331368156876154640) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (504 - x)) = _
  rw [show 505 = 318 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 11 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (505 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_505 :
    recurrence4Scalar2Left.coeff 505 =
      -((601387377168416021302808221299571003623129179569589 * 10 ^ 70 +
        8613017420620932842486124087634935248597320330762939209671691138676621) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (505 - x)) = _
  rw [show 506 = 319 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 10 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (506 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_506 :
    recurrence4Scalar2Left.coeff 506 =
      ((7454903641464048669138376038697191921298745643 * 10 ^ 70 +
        0888458509010974661085337334828199659617483063704662803080511708623001) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (506 - x)) = _
  rw [show 507 = 320 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 9 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (507 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_507 :
    recurrence4Scalar2Left.coeff 507 =
      -((11690585713525214872054166167062528025983 * 10 ^ 70 +
        9553829935874121101619871705629256231727173836846964816169875038845336) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (507 - x)) = _
  rw [show 508 = 321 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 8 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (508 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_508 :
    recurrence4Scalar2Left.coeff 508 =
      -((63960374164064485528005958685386661 * 10 ^ 70 +
        4731315063889014606488854517755818852546047180472561808453028699015738) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (508 - x)) = _
  rw [show 509 = 322 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 7 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (509 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_509 :
    recurrence4Scalar2Left.coeff 509 =
      ((79457755080214002597672235407 * 10 ^ 70 +
        7741835386018443619894973858497644687594832324813425521245761705591572) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (509 - x)) = _
  rw [show 510 = 323 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 6 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_509_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (510 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_510 :
    recurrence4Scalar2Left.coeff 510 =
      -((13785476235435732278541 * 10 ^ 70 +
        7835039624219256148339519625031867360161120267078522114836630899063200) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (510 - x)) = _
  rw [show 511 = 324 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_510_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (511 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_511 :
    recurrence4Scalar2Left.coeff 511 =
      -((6306531890487896 * 10 ^ 70 +
        4632044751987589918822418319866860646445142272698168702463147937675705) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (511 - x)) = _
  rw [show 512 = 325 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 4 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_511_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (512 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_512 :
    recurrence4Scalar2Left.coeff 512 =
      ((346844210 * 10 ^ 70 +
        5988711382364874152722113147308548297132202427674896398484298424746359) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (512 - x)) = _
  rw [show 513 = 326 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 3 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (513 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_513 :
    recurrence4Scalar2Left.coeff 513 =
      -((3 * 10 ^ 70 +
        6162422877326748712570162065258747737037805459129053360086100494870960) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (513 - x)) = _
  rw [show 514 = 327 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 2 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (514 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (514 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_514 :
    recurrence4Scalar2Left.coeff 514 =
      (-250932851299646582581316892643481901891865211206656305812286900 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (514 - x)) = _
  rw [show 515 = 328 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 1 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
