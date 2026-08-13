/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart4Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_168
  recurrence4A0_coeff_169
  recurrence4A0_coeff_170
  recurrence4A0_coeff_171
  recurrence4A0_coeff_172
  recurrence4A0_coeff_173
  recurrence4A0_coeff_174
  recurrence4A0_coeff_175
  recurrence4A0_coeff_176
  recurrence4A0_coeff_177
  recurrence4A0_coeff_178
  recurrence4A0_coeff_179
  recurrence4A0_coeff_180
  recurrence4A0_coeff_181
  recurrence4A0_coeff_182
  recurrence4A0_coeff_183
  recurrence4A0_coeff_184
  recurrence4A0_coeff_185
  recurrence4A0_coeff_186
  recurrence4A0_coeff_187
  recurrence4A0_coeff_188
  recurrence4A0_coeff_189
  recurrence4A0_coeff_190
  recurrence4A0_coeff_191
  recurrence4A0_coeff_192
  recurrence4A0_coeff_193
  recurrence4A0_coeff_194
  recurrence4LeadingSquare_coeff_302
  recurrence4LeadingSquare_coeff_303
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

private theorem recurrence4Scalar0Left_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (496 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (496 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_496 :
    recurrence4Scalar0Left.coeff 496 =
      -(((17194628923078338216482012941360978640 * 10 ^ 70 +
        8077942827825416994497884333047505402552860089512128177195362799672867) * 10 ^ 70 +
        3790021770485323784141057960822897121204109090389188522033422948639125) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (496 - x)) = _
  rw [show 497 = 302 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 27 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (497 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (497 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_497 :
    recurrence4Scalar0Left.coeff 497 =
      (((64898980128470285322684512847061944 * 10 ^ 70 +
        2029714920977651972751652479675477088194392542466577144819478588218966) * 10 ^ 70 +
        2835475842709117178530699841572494959589698257996901788115711949376899) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (497 - x)) = _
  rw [show 498 = 303 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 26 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (498 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (498 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_498 :
    recurrence4Scalar0Left.coeff 498 =
      (((103412736403270864618271398596283 * 10 ^ 70 +
        5821918914596566248487503256853032271492078069424194670907396270042579) * 10 ^ 70 +
        2403612440064571042279932286646398613230523871118859870652311328719684) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (498 - x)) = _
  rw [show 499 = 304 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 25 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (499 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (499 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_499 :
    recurrence4Scalar0Left.coeff 499 =
      -(((300409011938060936162371893546 * 10 ^ 70 +
        7847216462240226214067915472400365670963368970543996193177058019796785) * 10 ^ 70 +
        3255982052627163650327907328909174386182863869104460140558280525190958) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (499 - x)) = _
  rw [show 500 = 305 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 24 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (500 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (500 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_500 :
    recurrence4Scalar0Left.coeff 500 =
      -(((270816300771126678559609075 * 10 ^ 70 +
        0054993052715219767102072428580826977571059180887939701451554379658140) * 10 ^ 70 +
        8234964976368953475237210735577780054296584797262323845642271717331309) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (500 - x)) = _
  rw [show 501 = 306 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 23 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (501 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (501 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_501 :
    recurrence4Scalar0Left.coeff 501 =
      (((832326372258369483580547 * 10 ^ 70 +
        2037956963185033506604595696001396340634265858297372418187744499216826) * 10 ^ 70 +
        7754148320266043079542490923133718549920735926026535877877875011079316) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (501 - x)) = _
  rw [show 502 = 307 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 22 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (502 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (502 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_502 :
    recurrence4Scalar0Left.coeff 502 =
      (((111304922663486676374 * 10 ^ 70 +
        1304783481598742448116031959747260308896858439250155681279077175976939) * 10 ^ 70 +
        5811622849318131306045436347101569223315393292448562489257910902164418) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (502 - x)) = _
  rw [show 503 = 308 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 21 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (503 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (503 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_503 :
    recurrence4Scalar0Left.coeff 503 =
      -(((983946775558682740 * 10 ^ 70 +
        0823007377920299130447582577154803277715308226940433320479783857785860) * 10 ^ 70 +
        4131438190625363982735638988001348801372063410998588351366468840578273) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (503 - x)) = _
  rw [show 504 = 309 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 20 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (504 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (504 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_504 :
    recurrence4Scalar0Left.coeff 504 =
      (((338894620985486 * 10 ^ 70 +
        5672459484653749580014208965282406503856592237504643789471434361062811) * 10 ^ 70 +
        5907961969789661825385264915699569915891176706303701158968435248304590) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (504 - x)) = _
  rw [show 505 = 310 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 19 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (505 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (505 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_505 :
    recurrence4Scalar0Left.coeff 505 =
      (((238273672037 * 10 ^ 70 +
        6402799826089812938789385847951532224794866017979643764638314210183582) * 10 ^ 70 +
        1233298751122938091280700514806699932724943360300402201962412842810315) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (505 - x)) = _
  rw [show 506 = 311 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 18 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (506 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (506 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_506 :
    recurrence4Scalar0Left.coeff 506 =
      -(((128982158 * 10 ^ 70 +
        6979712963547970498856672296186823659600043784766903495357562544503700) * 10 ^ 70 +
        7936632629780385783217259282934934700147517179058200991084296973850887) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (506 - x)) = _
  rw [show 507 = 312 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 17 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (507 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (507 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_507 :
    recurrence4Scalar0Left.coeff 507 =
      (((3016 * 10 ^ 70 +
        3386927914482305352832856418848078386655616945486500733907578912727979) * 10 ^ 70 +
        4364164121571558810620833032252486433244291199791035594099092852322321) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (507 - x)) = _
  rw [show 508 = 313 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 16 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (508 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (508 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_508 :
    recurrence4Scalar0Left.coeff 508 =
      (((4 * 10 ^ 70 +
        6804232079217104883661277209564679872381192514104620286154238120133095) * 10 ^ 70 +
        2821829787095018634466430302487842900470959145736635286013774436689251) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (508 - x)) = _
  rw [show 509 = 314 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 15 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (509 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (509 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_509 :
    recurrence4Scalar0Left.coeff 509 =
      -((4836349906475179186009410704778480316288878637990027942476409854067 * 10 ^ 70 +
        3797795379194362415422599103881002150879444452092152091866575066762839) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (509 - x)) = _
  rw [show 510 = 315 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 14 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_509_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (510 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (510 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_510 :
    recurrence4Scalar0Left.coeff 510 =
      -((67529669495413945857900963867347452277360442594027968546539825 * 10 ^ 70 +
        0220965935474545952580485243177804353042978703793154407785020540437460) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (510 - x)) = _
  rw [show 511 = 316 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 13 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_510_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (511 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (511 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_511 :
    recurrence4Scalar0Left.coeff 511 =
      ((15081470913390353603952311934346307644398112514122273948227 * 10 ^ 70 +
        3906568790575118678705504618530731732378523163037578377524617840268797) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (511 - x)) = _
  rw [show 512 = 317 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 12 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_511_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (512 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (512 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_512 :
    recurrence4Scalar0Left.coeff 512 =
      -((284387414760326991646103782560166669111502568809726117 * 10 ^ 70 +
        1568977271011972170798056025050658976285989616430251543365778106131200) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (512 - x)) = _
  rw [show 513 = 318 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 11 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (513 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (513 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_513 :
    recurrence4Scalar0Left.coeff 513 =
      -((1869791631016749607246782378378817640294488791618 * 10 ^ 70 +
        3332229658154029045826025693770127765216216966651583222639416784639373) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (513 - x)) = _
  rw [show 514 = 319 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 10 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (514 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (514 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (514 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_514 :
    recurrence4Scalar0Left.coeff 514 =
      ((40577335699620948029316992727178337541423882 * 10 ^ 70 +
        1531608435923122204759588108788635210637783935697433656437743380595617) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (514 - x)) = _
  rw [show 515 = 320 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 9 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_515_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (515 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (515 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_515_suffix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (515 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (515 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_515 :
    recurrence4Scalar0Left.coeff 515 =
      -((117058770490333695647817246766874644432 * 10 ^ 70 +
        1255921012027657890891503410901132901142718438012387344570036357012658) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 516,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (515 - x)) = _
  rw [show 516 = 321 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 8 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_515_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_515_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_516_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (516 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (516 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_516_suffix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (516 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (516 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_516 :
    recurrence4Scalar0Left.coeff 516 =
      -((144617358784247487314047271918363 * 10 ^ 70 +
        0731831722907754201556262551933624733311604801362567862948027438368155) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 517,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (516 - x)) = _
  rw [show 517 = 322 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 7 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_516_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_516_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_517_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (517 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (517 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_517_suffix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (517 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (517 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_517 :
    recurrence4Scalar0Left.coeff 517 =
      ((285406003297010245434416318 * 10 ^ 70 +
        5212507647065534781750372846397528293424336488401385101656230177869105) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 518,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (517 - x)) = _
  rw [show 518 = 323 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 6 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_517_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_517_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_518_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (518 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (518 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_518_suffix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (518 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (518 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_518 :
    recurrence4Scalar0Left.coeff 518 =
      -((89096326674757385850 * 10 ^ 70 +
        4946411041644273296251243469773634669942623601968165221041253736581885) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 519,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (518 - x)) = _
  rw [show 519 = 324 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 5 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_518_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_518_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_519_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (519 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (519 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_519_suffix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (519 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (519 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_519 :
    recurrence4Scalar0Left.coeff 519 =
      -((7511192558139 * 10 ^ 70 +
        0982572634742978711599648278039161200082479617703646112305897222299621) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 520,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (519 - x)) = _
  rw [show 520 = 325 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 4 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_519_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_519_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_520_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (520 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (520 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_520_suffix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (520 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (520 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_520 :
    recurrence4Scalar0Left.coeff 520 =
      ((585383 * 10 ^ 70 +
        9687758199177426187085836667357711856477236552587994317363690276512708) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 521,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (520 - x)) = _
  rw [show 521 = 326 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 3 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_520_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_520_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_521_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (521 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (521 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_521_suffix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (521 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (521 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_521 :
    recurrence4Scalar0Left.coeff 521 =
      (-81516100350880128080672429099515632074440541614382194603859659322820 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 522,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (521 - x)) = _
  rw [show 522 = 327 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 2 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_521_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_521_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_522_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (522 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (522 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_522_suffix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (522 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (522 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_522 :
    recurrence4Scalar0Left.coeff 522 =
      (-158873507135237537436867830109024197639627909101096445538800 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 523,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (522 - x)) = _
  rw [show 523 = 328 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 1 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_522_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_522_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
