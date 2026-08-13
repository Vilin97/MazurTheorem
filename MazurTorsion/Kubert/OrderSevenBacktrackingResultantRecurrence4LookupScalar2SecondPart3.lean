/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B2_coeff_133
  recurrence4B2_coeff_134
  recurrence4B2_coeff_135
  recurrence4B2_coeff_136
  recurrence4B2_coeff_137
  recurrence4B2_coeff_138
  recurrence4B2_coeff_139
  recurrence4B2_coeff_140
  recurrence4B2_coeff_141
  recurrence4B2_coeff_142
  recurrence4B2_coeff_143
  recurrence4B2_coeff_144
  recurrence4B2_coeff_145
  recurrence4B2_coeff_146
  recurrence4B2_coeff_147
  recurrence4B2_coeff_148
  recurrence4B2_coeff_149
  recurrence4B2_coeff_150
  recurrence4B2_coeff_151
  recurrence4B2_coeff_152
  recurrence4B2_coeff_153
  recurrence4B2_coeff_154
  recurrence4B2_coeff_155
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157
  recurrence4B2_coeff_158
  recurrence4B2_coeff_159
  recurrence4B2_coeff_160
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167
  recurrence4B2_coeff_168
  recurrence4QuotientConstant_coeff_311
  recurrence4QuotientConstant_coeff_312
  recurrence4QuotientConstant_coeff_313
  recurrence4QuotientConstant_coeff_314
  recurrence4QuotientConstant_coeff_315
  recurrence4QuotientConstant_coeff_316
  recurrence4QuotientConstant_coeff_317
  recurrence4QuotientConstant_coeff_318
  recurrence4QuotientConstant_coeff_319
  recurrence4QuotientConstant_coeff_320
  recurrence4QuotientConstant_coeff_321
  recurrence4QuotientConstant_coeff_322
  recurrence4QuotientConstant_coeff_323
  recurrence4QuotientConstant_coeff_324
  recurrence4QuotientConstant_coeff_325
  recurrence4QuotientConstant_coeff_326
  recurrence4QuotientConstant_coeff_327
  recurrence4QuotientConstant_coeff_328
  recurrence4QuotientConstant_coeff_329
  recurrence4QuotientConstant_coeff_330
  recurrence4QuotientConstant_coeff_331
  recurrence4QuotientConstant_coeff_332
  recurrence4QuotientConstant_coeff_333
  recurrence4QuotientConstant_coeff_334
  recurrence4QuotientConstant_coeff_335
  recurrence4QuotientConstant_coeff_336
  recurrence4QuotientConstant_coeff_337
  recurrence4QuotientConstant_coeff_338

attribute [local simp]
  recurrence4QuotientConstant_coeff_339
  recurrence4QuotientConstant_coeff_340
  recurrence4QuotientConstant_coeff_341
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346

private theorem recurrence4Scalar2Second_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (479 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_479 :
    recurrence4Scalar2Second.coeff 479 =
      -(((353733031247106479630356788093613482751910870179256176879008 * 10 ^ 70 +
        1649254008061647421051108614049255826885163101305931186516833715452519) * 10 ^ 70 +
        8652175512116257891078733155401111831884538143467266274829509202089360) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (479 - x)) = _
  rw [show 480 = 133 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 4 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (480 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_480 :
    recurrence4Scalar2Second.coeff 480 =
      (((2015202915221174499612266669695133213667787404826653276836 * 10 ^ 70 +
        2317752083450044873602709502963541054073270898951876598535474907258749) * 10 ^ 70 +
        5266859175739262723753818701048570583832048152590720280179825868989763) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (480 - x)) = _
  rw [show 481 = 134 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 3 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (481 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_481 :
    recurrence4Scalar2Second.coeff 481 =
      (((34003483978655048223368427363173312062748506488740908071 * 10 ^ 70 +
        9452501419159790708516537838665755368880362023396293746242665327632510) * 10 ^ 70 +
        1790298048145889331731179737283712786476316325665176133156630804170332) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (481 - x)) = _
  rw [show 482 = 135 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 2 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 314,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (482 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_482 :
    recurrence4Scalar2Second.coeff 482 =
      -(((72292529447907044003878789563483386526912521421904021 * 10 ^ 70 +
        4698251658201632232799827274790552795252062239774829058595071611291474) * 10 ^ 70 +
        9987386498080211950486853465343475423902196242206392492216903002335876) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (482 - x)) = _
  rw [show 483 = 136 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 1 +
      314 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 315,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (483 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_483 :
    recurrence4Scalar2Second.coeff 483 =
      -(((1637668530795005387127065445974718885382163688282687 * 10 ^ 70 +
        2919212761854040818961910469258328892219871082464991451962304037591799) * 10 ^ 70 +
        8237236079311997938183801881068851898940719420247348178308426536768238) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (483 - x)) = _
  rw [show 484 = 137 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 316,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (484 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_484 :
    recurrence4Scalar2Second.coeff 484 =
      -(((168369034536447202423148196017694838334323366001 * 10 ^ 70 +
        2365957226321887934380999261648460742543313935104824687231458780968350) * 10 ^ 70 +
        9424037636330060708470915256245268874377934291456894191324434603768551) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (484 - x)) = _
  rw [show 485 = 138 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 31 +
      316 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 317,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (485 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_485 :
    recurrence4Scalar2Second.coeff 485 =
      (((38854043587349226120666431324938742400840286489 * 10 ^ 70 +
        9442456745950320471500869514669986724241776380836222970377290975121937) * 10 ^ 70 +
        2334109120762371989391302257523219160373473269580894391157053242547027) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (485 - x)) = _
  rw [show 486 = 139 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 30 +
      317 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 318,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (486 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_486 :
    recurrence4Scalar2Second.coeff 486 =
      (((43712356604366107406477154614520992065369454 * 10 ^ 70 +
        9934601297370444733869538644651106040659819756250414904462567900571048) * 10 ^ 70 +
        2362537183495935147646378083282970325032341674646049147761587801851372) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (486 - x)) = _
  rw [show 487 = 140 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 29 +
      318 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 319,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (487 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_487 :
    recurrence4Scalar2Second.coeff 487 =
      -(((483699474658866019642214479757066180091999 * 10 ^ 70 +
        3571333231496383539320921232081234991779712040964503570184428900163672) * 10 ^ 70 +
        5132671862624450060660716909293928603998005624617715441170201087815454) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (487 - x)) = _
  rw [show 488 = 141 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 28 +
      319 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 320,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (488 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_488 :
    recurrence4Scalar2Second.coeff 488 =
      -(((670995769317569655360643557778612512704 * 10 ^ 70 +
        6054609382140276179475562713979245635279623045141166716654825333694398) * 10 ^ 70 +
        7225964776062004801464783644583740754391086538855869784122802508583945) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (488 - x)) = _
  rw [show 489 = 142 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 27 +
      320 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 321,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (489 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_489 :
    recurrence4Scalar2Second.coeff 489 =
      (((3624479245939078674575004575387854946 * 10 ^ 70 +
        8931249623646201703147289497717593373278319026448499377587384487984608) * 10 ^ 70 +
        0664528773335221356617081371138411378149050246437962221188356611483271) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (489 - x)) = _
  rw [show 490 = 143 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 26 +
      321 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 322,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (490 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_490 :
    recurrence4Scalar2Second.coeff 490 =
      (((4175843000250261577583485187707315 * 10 ^ 70 +
        3890995107184590002716515410710756062049185630709475672188477808794056) * 10 ^ 70 +
        8519610385372815948531292030295733477289157927657806296907038456170607) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (490 - x)) = _
  rw [show 491 = 144 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 25 +
      322 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 323,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (491 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_491 :
    recurrence4Scalar2Second.coeff 491 =
      -(((17242814282733225822308092561192 * 10 ^ 70 +
        0193992968723818122380751181604221947213253532319416124511077659597678) * 10 ^ 70 +
        1240257105662804077898108808211189518112391569337367891364743106043911) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (491 - x)) = _
  rw [show 492 = 145 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 24 +
      323 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 324,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (492 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_492 :
    recurrence4Scalar2Second.coeff 492 =
      -(((10010267669914903266445747377 * 10 ^ 70 +
        4556653436163793616688422451583791523864933229391399559813486185402025) * 10 ^ 70 +
        5236256752169598566174808554040600094286723418239042697871947590071323) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (492 - x)) = _
  rw [show 493 = 146 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 23 +
      324 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 325,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (493 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_493 :
    recurrence4Scalar2Second.coeff 493 =
      (((47735666275717958374431810 * 10 ^ 70 +
        6355694000823590604257289272786206223175719330614325956280721809335534) * 10 ^ 70 +
        4771459598174019554198091278364451394563363025594795227018095243580368) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (493 - x)) = _
  rw [show 494 = 147 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 22 +
      325 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 326,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (494 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_494 :
    recurrence4Scalar2Second.coeff 494 =
      -(((2889234114224447985588 * 10 ^ 70 +
        5027780204918186454960743752105356919589260090044610176432776148069201) * 10 ^ 70 +
        1873842726592750124378104683028620552076183232907243815011528599582101) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (494 - x)) = _
  rw [show 495 = 148 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 21 +
      326 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 327,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (495 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_495 :
    recurrence4Scalar2Second.coeff 495 =
      -(((55454675886263960971 * 10 ^ 70 +
        2158830624743054654167232811686666650893152469440178649946445839404132) * 10 ^ 70 +
        9304345067036361389774504556800810116085990468495206604679269358952978) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (495 - x)) = _
  rw [show 496 = 149 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 20 +
      327 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 328,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (496 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_496 :
    recurrence4Scalar2Second.coeff 496 =
      (((26577365035348395 * 10 ^ 70 +
        8741933860107924313841477773357114092869617705291684957631530739563236) * 10 ^ 70 +
        5942797755658846946043254455374169073314590946991277930061310875483099) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (496 - x)) = _
  rw [show 497 = 150 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 19 +
      328 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 329,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (497 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_497 :
    recurrence4Scalar2Second.coeff 497 =
      (((12180529795001 * 10 ^ 70 +
        2666224381798465850821587174901860934390708524974693757324123171147826) * 10 ^ 70 +
        2247251623400923703632718015111713010358487362804853898879261205070552) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (497 - x)) = _
  rw [show 498 = 151 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 18 +
      329 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 330,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (498 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_498 :
    recurrence4Scalar2Second.coeff 498 =
      -(((9017389182 * 10 ^ 70 +
        7897337075990179490066100041678260512517940685012316293260044157052797) * 10 ^ 70 +
        2086208796860540674903086738679214122502434294783855132364207382081470) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (498 - x)) = _
  rw [show 499 = 152 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 17 +
      330 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 331,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (499 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_499 :
    recurrence4Scalar2Second.coeff 499 =
      (((634301 * 10 ^ 70 +
        4986959757231993035612431404330096506145454134540113984208230766883320) * 10 ^ 70 +
        9875601047755915602285991758638748992857628696862920360001929935250453) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (499 - x)) = _
  rw [show 500 = 153 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 16 +
      331 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 332,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (500 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_500 :
    recurrence4Scalar2Second.coeff 500 =
      (((317 * 10 ^ 70 +
        1108679509775633731941547484131238097927017627763168779045443370489752) * 10 ^ 70 +
        4923946830319279410610718587545169435031883366772457177521672062792271) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (500 - x)) = _
  rw [show 501 = 154 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 15 +
      332 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 333,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (501 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_501 :
    recurrence4Scalar2Second.coeff 501 =
      -((437200125348509872909362613006970914045352907267942664536892293818840 * 10 ^ 70 +
        7144977925149459467131746782569556523978628622531041556403663001708572) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (501 - x)) = _
  rw [show 502 = 155 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 14 +
      333 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 334,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (502 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_502 :
    recurrence4Scalar2Second.coeff 502 =
      ((944010417163729175905148501046034054109845626740127985789602154 * 10 ^ 70 +
        5512766047447590596295272190374229603685020928458440745054494863059394) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (502 - x)) = _
  rw [show 503 = 156 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 13 +
      334 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 335,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (503 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_503 :
    recurrence4Scalar2Second.coeff 503 =
      ((1364854150883667007088643622218049881775197025490828737116723 * 10 ^ 70 +
        5183845546378096642475405626053413550439166260628826907588695137246956) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (503 - x)) = _
  rw [show 504 = 157 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 12 +
      335 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 336,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (504 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_504 :
    recurrence4Scalar2Second.coeff 504 =
      -((35142088989746646112129009204965402597315375812469609243 * 10 ^ 70 +
        2378926503787518583284845125844366350565281602986993937856106210415830) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (504 - x)) = _
  rw [show 505 = 158 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 11 +
      336 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 337,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (505 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_505 :
    recurrence4Scalar2Second.coeff 505 =
      -((74479958616327973954258061729276413847720411628052 * 10 ^ 70 +
        7315167106764478907563962955403981593041975238420992948015918739919958) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (505 - x)) = _
  rw [show 506 = 159 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 10 +
      337 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 338,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (506 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_506 :
    recurrence4Scalar2Second.coeff 506 =
      ((5278188159266104828692774628474604389418062603 * 10 ^ 70 +
        1883241543745103720691624128562936870410516570955621904925414812292280) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (506 - x)) = _
  rw [show 507 = 160 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 9 +
      338 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 339,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (507 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_507 :
    recurrence4Scalar2Second.coeff 507 =
      -((20989194249703967237553122979278067534289 * 10 ^ 70 +
        9088808049629890643227350118847065593637141714434960497777560703963531) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (507 - x)) = _
  rw [show 508 = 161 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 8 +
      339 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 340,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (508 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_508 :
    recurrence4Scalar2Second.coeff 508 =
      -((9455513721031085369081296427656954 * 10 ^ 70 +
        7547658778044950554157766523318091157873725542647202015543705381121735) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (508 - x)) = _
  rw [show 509 = 162 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 7 +
      340 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 341,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (509 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_509 :
    recurrence4Scalar2Second.coeff 509 =
      ((61478833047931952695502959092 * 10 ^ 70 +
        2215167591001751950457090208303232392772430739751155949814336127272578) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (509 - x)) = _
  rw [show 510 = 163 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 6 +
      341 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_509_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 342,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (510 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_510 :
    recurrence4Scalar2Second.coeff 510 =
      -((25028457005463903609033 * 10 ^ 70 +
        0392658619717535778214278452994554174949643287788568440850691407172734) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (510 - x)) = _
  rw [show 511 = 164 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 5 +
      342 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_510_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 343,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (511 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_511 :
    recurrence4Scalar2Second.coeff 511 =
      -((418465745244810 * 10 ^ 70 +
        4021138257162163214944540056246830926172469261974007999785805391953898) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (511 - x)) = _
  rw [show 512 = 165 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 4 +
      343 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_511_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 344,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (512 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_512 :
    recurrence4Scalar2Second.coeff 512 =
      ((272215716 * 10 ^ 70 +
        4768046535320773445155153178807157250972134303141630745581461393720316) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (512 - x)) = _
  rw [show 513 = 166 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 3 +
      344 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 345,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (513 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_513 :
    recurrence4Scalar2Second.coeff 513 =
      -((4 * 10 ^ 70 +
        2424700758820261395924300578952097900397848621631505830768407090338181) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (513 - x)) = _
  rw [show 514 = 167 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 2 +
      345 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (514 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 346,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (514 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_514 :
    recurrence4Scalar2Second.coeff 514 =
      (11231002459417880704909299761270836144720659591828868792082713 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (514 - x)) = _
  rw [show 515 = 168 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 1 +
      346 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
