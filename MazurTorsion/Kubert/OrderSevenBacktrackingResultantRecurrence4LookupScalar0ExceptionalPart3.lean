/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C0_coeff_100
  recurrence4C0_coeff_101
  recurrence4C0_coeff_102
  recurrence4C0_coeff_103
  recurrence4C0_coeff_104
  recurrence4C0_coeff_105
  recurrence4C0_coeff_106
  recurrence4C0_coeff_107
  recurrence4C0_coeff_108
  recurrence4C0_coeff_109
  recurrence4C0_coeff_110
  recurrence4C0_coeff_111
  recurrence4C0_coeff_112
  recurrence4C0_coeff_113
  recurrence4C0_coeff_114
  recurrence4C0_coeff_115
  recurrence4C0_coeff_116
  recurrence4C0_coeff_117
  recurrence4C0_coeff_118
  recurrence4C0_coeff_119
  recurrence4C0_coeff_120
  recurrence4C0_coeff_121
  recurrence4C0_coeff_122
  recurrence4C0_coeff_123
  recurrence4C0_coeff_124
  recurrence4C0_coeff_125
  recurrence4C0_coeff_126
  recurrence4C0_coeff_127
  recurrence4C0_coeff_128
  recurrence4C0_coeff_129
  recurrence4C0_coeff_130
  recurrence4C0_coeff_131
  recurrence4C0_coeff_132
  recurrence4C0_coeff_133
  recurrence4C0_coeff_134
  recurrence4C0_coeff_135
  recurrence4C0_coeff_136
  recurrence4C0_coeff_137
  recurrence4C0_coeff_138
  recurrence4C0_coeff_139
  recurrence4C0_coeff_14
  recurrence4C0_coeff_140
  recurrence4C0_coeff_141
  recurrence4C0_coeff_142
  recurrence4C0_coeff_143
  recurrence4C0_coeff_144
  recurrence4C0_coeff_145
  recurrence4C0_coeff_146
  recurrence4C0_coeff_147
  recurrence4C0_coeff_148
  recurrence4C0_coeff_149
  recurrence4C0_coeff_15
  recurrence4C0_coeff_150
  recurrence4C0_coeff_151
  recurrence4C0_coeff_152
  recurrence4C0_coeff_153
  recurrence4C0_coeff_16
  recurrence4C0_coeff_17
  recurrence4C0_coeff_18
  recurrence4C0_coeff_19
  recurrence4C0_coeff_20
  recurrence4C0_coeff_21
  recurrence4C0_coeff_22
  recurrence4C0_coeff_23

attribute [local simp]
  recurrence4C0_coeff_24
  recurrence4C0_coeff_25
  recurrence4C0_coeff_26
  recurrence4C0_coeff_27
  recurrence4C0_coeff_28
  recurrence4C0_coeff_29
  recurrence4C0_coeff_30
  recurrence4C0_coeff_31
  recurrence4C0_coeff_32
  recurrence4C0_coeff_33
  recurrence4C0_coeff_34
  recurrence4C0_coeff_35
  recurrence4C0_coeff_36
  recurrence4C0_coeff_37
  recurrence4C0_coeff_38
  recurrence4C0_coeff_39
  recurrence4C0_coeff_40
  recurrence4C0_coeff_41
  recurrence4C0_coeff_42
  recurrence4C0_coeff_43
  recurrence4C0_coeff_44
  recurrence4C0_coeff_45
  recurrence4C0_coeff_46
  recurrence4C0_coeff_47
  recurrence4C0_coeff_48
  recurrence4C0_coeff_49
  recurrence4C0_coeff_50
  recurrence4C0_coeff_51
  recurrence4C0_coeff_52
  recurrence4C0_coeff_53
  recurrence4C0_coeff_54
  recurrence4C0_coeff_55
  recurrence4C0_coeff_56
  recurrence4C0_coeff_57
  recurrence4C0_coeff_58
  recurrence4C0_coeff_59
  recurrence4C0_coeff_60
  recurrence4C0_coeff_61
  recurrence4C0_coeff_62
  recurrence4C0_coeff_63
  recurrence4C0_coeff_64
  recurrence4C0_coeff_65
  recurrence4C0_coeff_66
  recurrence4C0_coeff_67
  recurrence4C0_coeff_68
  recurrence4C0_coeff_69
  recurrence4C0_coeff_70
  recurrence4C0_coeff_71
  recurrence4C0_coeff_72
  recurrence4C0_coeff_73
  recurrence4C0_coeff_74
  recurrence4C0_coeff_75
  recurrence4C0_coeff_76
  recurrence4C0_coeff_77
  recurrence4C0_coeff_78
  recurrence4C0_coeff_79
  recurrence4C0_coeff_80
  recurrence4C0_coeff_81
  recurrence4C0_coeff_82
  recurrence4C0_coeff_83
  recurrence4C0_coeff_84
  recurrence4C0_coeff_85
  recurrence4C0_coeff_86
  recurrence4C0_coeff_87

attribute [local simp]
  recurrence4C0_coeff_88
  recurrence4C0_coeff_89
  recurrence4C0_coeff_90
  recurrence4C0_coeff_91
  recurrence4C0_coeff_92
  recurrence4C0_coeff_93
  recurrence4C0_coeff_94
  recurrence4C0_coeff_95
  recurrence4C0_coeff_96
  recurrence4C0_coeff_97
  recurrence4C0_coeff_98
  recurrence4C0_coeff_99
  recurrence4ExceptionalProduct_coeff_230
  recurrence4ExceptionalProduct_coeff_231
  recurrence4ExceptionalProduct_coeff_232
  recurrence4ExceptionalProduct_coeff_233
  recurrence4ExceptionalProduct_coeff_234
  recurrence4ExceptionalProduct_coeff_235
  recurrence4ExceptionalProduct_coeff_236
  recurrence4ExceptionalProduct_coeff_237
  recurrence4ExceptionalProduct_coeff_238
  recurrence4ExceptionalProduct_coeff_239
  recurrence4ExceptionalProduct_coeff_240
  recurrence4ExceptionalProduct_coeff_241
  recurrence4ExceptionalProduct_coeff_242
  recurrence4ExceptionalProduct_coeff_243
  recurrence4ExceptionalProduct_coeff_244
  recurrence4ExceptionalProduct_coeff_245
  recurrence4ExceptionalProduct_coeff_246
  recurrence4ExceptionalProduct_coeff_247
  recurrence4ExceptionalProduct_coeff_248
  recurrence4ExceptionalProduct_coeff_249
  recurrence4ExceptionalProduct_coeff_250
  recurrence4ExceptionalProduct_coeff_251
  recurrence4ExceptionalProduct_coeff_252
  recurrence4ExceptionalProduct_coeff_253
  recurrence4ExceptionalProduct_coeff_254
  recurrence4ExceptionalProduct_coeff_255
  recurrence4ExceptionalProduct_coeff_256
  recurrence4ExceptionalProduct_coeff_257
  recurrence4ExceptionalProduct_coeff_258
  recurrence4ExceptionalProduct_coeff_259
  recurrence4ExceptionalProduct_coeff_260
  recurrence4ExceptionalProduct_coeff_261
  recurrence4ExceptionalProduct_coeff_262
  recurrence4ExceptionalProduct_coeff_263
  recurrence4ExceptionalProduct_coeff_264
  recurrence4ExceptionalProduct_coeff_265
  recurrence4ExceptionalProduct_coeff_266
  recurrence4ExceptionalProduct_coeff_267
  recurrence4ExceptionalProduct_coeff_268
  recurrence4ExceptionalProduct_coeff_269
  recurrence4ExceptionalProduct_coeff_270
  recurrence4ExceptionalProduct_coeff_271
  recurrence4ExceptionalProduct_coeff_272
  recurrence4ExceptionalProduct_coeff_273
  recurrence4ExceptionalProduct_coeff_274
  recurrence4ExceptionalProduct_coeff_275
  recurrence4ExceptionalProduct_coeff_276
  recurrence4ExceptionalProduct_coeff_277
  recurrence4ExceptionalProduct_coeff_278
  recurrence4ExceptionalProduct_coeff_279
  recurrence4ExceptionalProduct_coeff_280
  recurrence4ExceptionalProduct_coeff_281

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_282
  recurrence4ExceptionalProduct_coeff_283
  recurrence4ExceptionalProduct_coeff_284
  recurrence4ExceptionalProduct_coeff_285
  recurrence4ExceptionalProduct_coeff_286
  recurrence4ExceptionalProduct_coeff_287
  recurrence4ExceptionalProduct_coeff_288
  recurrence4ExceptionalProduct_coeff_289
  recurrence4ExceptionalProduct_coeff_290
  recurrence4ExceptionalProduct_coeff_291
  recurrence4ExceptionalProduct_coeff_292
  recurrence4ExceptionalProduct_coeff_293
  recurrence4ExceptionalProduct_coeff_294
  recurrence4ExceptionalProduct_coeff_295
  recurrence4ExceptionalProduct_coeff_296
  recurrence4ExceptionalProduct_coeff_297
  recurrence4ExceptionalProduct_coeff_298
  recurrence4ExceptionalProduct_coeff_299
  recurrence4ExceptionalProduct_coeff_300
  recurrence4ExceptionalProduct_coeff_301
  recurrence4ExceptionalProduct_coeff_302
  recurrence4ExceptionalProduct_coeff_303
  recurrence4ExceptionalProduct_coeff_304
  recurrence4ExceptionalProduct_coeff_305
  recurrence4ExceptionalProduct_coeff_306
  recurrence4ExceptionalProduct_coeff_307
  recurrence4ExceptionalProduct_coeff_308
  recurrence4ExceptionalProduct_coeff_309
  recurrence4ExceptionalProduct_coeff_310
  recurrence4ExceptionalProduct_coeff_311
  recurrence4ExceptionalProduct_coeff_312
  recurrence4ExceptionalProduct_coeff_313
  recurrence4ExceptionalProduct_coeff_314
  recurrence4ExceptionalProduct_coeff_315
  recurrence4ExceptionalProduct_coeff_316
  recurrence4ExceptionalProduct_coeff_317
  recurrence4ExceptionalProduct_coeff_318
  recurrence4ExceptionalProduct_coeff_319
  recurrence4ExceptionalProduct_coeff_320
  recurrence4ExceptionalProduct_coeff_321
  recurrence4ExceptionalProduct_coeff_322
  recurrence4ExceptionalProduct_coeff_323
  recurrence4ExceptionalProduct_coeff_324
  recurrence4ExceptionalProduct_coeff_325
  recurrence4ExceptionalProduct_coeff_326
  recurrence4ExceptionalProduct_coeff_327
  recurrence4ExceptionalProduct_coeff_328
  recurrence4ExceptionalProduct_coeff_329
  recurrence4ExceptionalProduct_coeff_330
  recurrence4ExceptionalProduct_coeff_331
  recurrence4ExceptionalProduct_coeff_332
  recurrence4ExceptionalProduct_coeff_333
  recurrence4ExceptionalProduct_coeff_334
  recurrence4ExceptionalProduct_coeff_335
  recurrence4ExceptionalProduct_coeff_336
  recurrence4ExceptionalProduct_coeff_337
  recurrence4ExceptionalProduct_coeff_338
  recurrence4ExceptionalProduct_coeff_339
  recurrence4ExceptionalProduct_coeff_340
  recurrence4ExceptionalProduct_coeff_341
  recurrence4ExceptionalProduct_coeff_342
  recurrence4ExceptionalProduct_coeff_343
  recurrence4ExceptionalProduct_coeff_344
  recurrence4ExceptionalProduct_coeff_345

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_346
  recurrence4ExceptionalProduct_coeff_347
  recurrence4ExceptionalProduct_coeff_348
  recurrence4ExceptionalProduct_coeff_349
  recurrence4ExceptionalProduct_coeff_350
  recurrence4ExceptionalProduct_coeff_351
  recurrence4ExceptionalProduct_coeff_352
  recurrence4ExceptionalProduct_coeff_353
  recurrence4ExceptionalProduct_coeff_354
  recurrence4ExceptionalProduct_coeff_355
  recurrence4ExceptionalProduct_coeff_356
  recurrence4ExceptionalProduct_coeff_357
  recurrence4ExceptionalProduct_coeff_358
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

private theorem recurrence4Scalar0Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (383 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (383 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_383 :
    recurrence4Scalar0Exceptional.coeff 383 =
      ((((2919565769158562813058025795282273593010842801655141831373196635653 * 10 ^ 70 +
        6781042312348921644263684375109326191629131205799810161202505883747314) * 10 ^ 70 +
        5242182512604009853018421152756166817491159004575942267231841490841318) * 10 ^ 70 +
        4601303656930032057286025043220942708285334398323036083906149371696184) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (383 - x)) = _
  rw [show 384 = 230 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 12 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (384 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (384 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_384 :
    recurrence4Scalar0Exceptional.coeff 384 =
      -((((913370038555173607291592776420133527380361862449176569574295862813 * 10 ^ 70 +
        9026440678182052568168088732946512513838914165575504016297137715120858) * 10 ^ 70 +
        4300258203429420260957054453827844879922529409135742064525925430547750) * 10 ^ 70 +
        4907057157737819915680697076032523877005718154890255463940621032458307) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (384 - x)) = _
  rw [show 385 = 231 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 11 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (385 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (385 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_385 :
    recurrence4Scalar0Exceptional.coeff 385 =
      ((((264675978510108061945619102098425634702557566582666797965092612053 * 10 ^ 70 +
        1701809027695076227612377435888357350112449694067057189315334156655434) * 10 ^ 70 +
        1330298123737394942288750789444952682616799619062641817536097690375116) * 10 ^ 70 +
        6324546274097283103035316328728673874598050247806058129199559222760090) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (385 - x)) = _
  rw [show 386 = 232 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 10 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (386 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (386 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_386 :
    recurrence4Scalar0Exceptional.coeff 386 =
      -((((67161255084639831352654709474242085600100521076191232688025677609 * 10 ^ 70 +
        2150408919662318078005286794028297361508534778775450751651791585527689) * 10 ^ 70 +
        3712508634535624249118325635046179397784083738133242108867377808912344) * 10 ^ 70 +
        4300659847609106584732727082966713179263786965152623660287706573332822) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (386 - x)) = _
  rw [show 387 = 233 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 9 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (387 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (387 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_387 :
    recurrence4Scalar0Exceptional.coeff 387 =
      ((((12318067720325663217717192384298010743203417509339973308707180728 * 10 ^ 70 +
        1809003984699393489096165558963131832991895133988989530118019772587555) * 10 ^ 70 +
        0987086760838507699384975566642261492987469321195772636003054394543164) * 10 ^ 70 +
        7386193477757194606959344540236525030714846401186957618905428599978100) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (387 - x)) = _
  rw [show 388 = 234 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 8 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (388 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (388 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_388 :
    recurrence4Scalar0Exceptional.coeff 388 =
      ((((439450911622108481163168638789224874957658493364663506404642412 * 10 ^ 70 +
        8291159864489283917987078597583920363868726489304659434268317157821413) * 10 ^ 70 +
        6134109076174107213201731673938472463074828758885565648554230424140614) * 10 ^ 70 +
        1591571630154338629065950882781147133425346232851575062268470861217301) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (388 - x)) = _
  rw [show 389 = 235 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 7 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (389 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (389 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_389 :
    recurrence4Scalar0Exceptional.coeff 389 =
      -((((2125061311278028056007634144219208412120591339726278909211531235 * 10 ^ 70 +
        0993497641190071606012565591467039417969784004052258485291816497126619) * 10 ^ 70 +
        1749518360221104617707929514663554495419303591949136352531696124881964) * 10 ^ 70 +
        0377147497971061791046048415912102110291607437594905826373125469409977) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (389 - x)) = _
  rw [show 390 = 236 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 6 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (390 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (390 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_390 :
    recurrence4Scalar0Exceptional.coeff 390 =
      ((((1547023521898412124987622246629109326664102912309121044604812375 * 10 ^ 70 +
        6439688718851077328904686880974684817660375906917888168140650813468953) * 10 ^ 70 +
        1165862781636538620906779169791072732140213227025145310674863037362742) * 10 ^ 70 +
        7565327504228419763021468057022267182340148412751315754518094526267994) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (390 - x)) = _
  rw [show 391 = 237 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 5 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (391 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (391 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_391 :
    recurrence4Scalar0Exceptional.coeff 391 =
      -((((863084717939008600617460282297558685211272669000345261694009073 * 10 ^ 70 +
        8543724367320939185540323604298506944123635615194069928441502867520825) * 10 ^ 70 +
        6613914450570770085980696278805531739975817379508233783738621884900545) * 10 ^ 70 +
        6884404395310645925404233308092606611894652106827093303960652213164759) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (391 - x)) = _
  rw [show 392 = 238 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 4 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (392 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (392 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_392 :
    recurrence4Scalar0Exceptional.coeff 392 =
      ((((428268428430636607221713386100727984115867684304687225873840778 * 10 ^ 70 +
        7217158120476847536499039378426969857468303760273710894541085466312735) * 10 ^ 70 +
        6739312527415422200526188589016909995917209626562141991720042747135765) * 10 ^ 70 +
        5263338391809783269167824508555182701271701303492633914940484770211549) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (392 - x)) = _
  rw [show 393 = 239 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 3 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (393 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (393 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_393 :
    recurrence4Scalar0Exceptional.coeff 393 =
      -((((198144106803240498493910231916807951143894185355742487486729687 * 10 ^ 70 +
        6307576873969791272157149739119835250392743418916912507793892987120867) * 10 ^ 70 +
        9235710054964509124904289496481553137319642978874245164426671760606226) * 10 ^ 70 +
        6016951656228732031167993303366172216368846899047640076613486469333764) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (393 - x)) = _
  rw [show 394 = 240 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 2 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (394 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (394 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_394 :
    recurrence4Scalar0Exceptional.coeff 394 =
      ((((87194189753242267344778127737400194185512149840341846759122242 * 10 ^ 70 +
        7666770027797713515713990268979101456940188652654950568247965660630987) * 10 ^ 70 +
        0123284878106581886966804116119981473161877277625904967607466668666980) * 10 ^ 70 +
        2029602286463685398116709329844054932598313056793060917132101557565171) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (394 - x)) = _
  rw [show 395 = 241 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 1 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (395 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (395 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_395 :
    recurrence4Scalar0Exceptional.coeff 395 =
      -((((36836939858499763031492268402575909562417717070092242019331304 * 10 ^ 70 +
        6601371933361982830979236378720283576337325614519225826863308424597453) * 10 ^ 70 +
        1548640633596147625476289510253805725590617213291720008637035278281295) * 10 ^ 70 +
        2648107340378630138632965773150273689702242259675045416066283377189966) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (395 - x)) = _
  rw [show 396 = 242 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (396 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (396 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_396 :
    recurrence4Scalar0Exceptional.coeff 396 =
      ((((15006198071976899846264206847904360125664204484849982446184079 * 10 ^ 70 +
        7554813952905870777877540390490463655201421178152560560602974449243298) * 10 ^ 70 +
        0609344586134426207315745812838701520891222222391445334278448110134323) * 10 ^ 70 +
        6868205813264710695743786763775935388991272776948822610946571375145259) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (396 - x)) = _
  rw [show 397 = 243 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 31 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (397 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (397 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_397 :
    recurrence4Scalar0Exceptional.coeff 397 =
      -((((5905024101016281589885655714649369824332039437584014308473540 * 10 ^ 70 +
        0322412465620490837005312777937592772375131669094312015341234679672508) * 10 ^ 70 +
        2500519279196940825790148142936093403368452322525078311104350709567107) * 10 ^ 70 +
        6426389985025487949205113974310943638825895004792396452866864303628617) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (397 - x)) = _
  rw [show 398 = 244 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 30 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (398 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (398 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_398 :
    recurrence4Scalar0Exceptional.coeff 398 =
      ((((2245190846666701396880516264608477357443643852488110305527395 * 10 ^ 70 +
        1988026638200221967447848112009497068827928648880189547426724691039406) * 10 ^ 70 +
        7403654926824099440042327511479258633274820371780553832763559264176193) * 10 ^ 70 +
        3792023890827648999911993225464730923951772426841109207414581682784747) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (398 - x)) = _
  rw [show 399 = 245 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 29 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (399 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (399 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_399 :
    recurrence4Scalar0Exceptional.coeff 399 =
      -((((824224341784308549150839624778418360342764172586214636381911 * 10 ^ 70 +
        5179904009111190423679925119067735251326354361178012819871738415224678) * 10 ^ 70 +
        8919196221214386780638517950365839954346306396763503415015452468698674) * 10 ^ 70 +
        7830086282971854364036460723415753542632777103236501783683257766288327) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (399 - x)) = _
  rw [show 400 = 246 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 28 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (400 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (400 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_400 :
    recurrence4Scalar0Exceptional.coeff 400 =
      ((((291688056471747539365504019307918408632507601770146061695958 * 10 ^ 70 +
        1641694399562226279499067221447318040303997124319947327651964712195312) * 10 ^ 70 +
        6260632585784917494787138197523938267804359113408004270482115060907281) * 10 ^ 70 +
        6641171563958209557922589395717043947271527955390350730551136622773811) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (400 - x)) = _
  rw [show 401 = 247 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 27 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (401 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (401 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_401 :
    recurrence4Scalar0Exceptional.coeff 401 =
      -((((99267862433742878256314488153424967108461221681865263371543 * 10 ^ 70 +
        7789319832613701900033194163087448004092466562884988969625251803018253) * 10 ^ 70 +
        6507926002446329229420600514142964158595110945800117629805832676052608) * 10 ^ 70 +
        7122269864396937570101882629375774232546783335260992106980325094347931) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (401 - x)) = _
  rw [show 402 = 248 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 26 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (402 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (402 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_402 :
    recurrence4Scalar0Exceptional.coeff 402 =
      ((((32369517259994684267100203166578665870605181006507846417215 * 10 ^ 70 +
        5726648651336674389933793660985007420347795380668830526463105006919048) * 10 ^ 70 +
        7539979525080036118094297314911851084509966154798481401821515746652483) * 10 ^ 70 +
        4475117514801611267314410391855836305187295798990728540706241978502985) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (402 - x)) = _
  rw [show 403 = 249 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 25 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (403 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (403 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_403 :
    recurrence4Scalar0Exceptional.coeff 403 =
      -((((10058181286183665705929499482678015471464989009489148380436 * 10 ^ 70 +
        1482992689889331876585373012457056067618139513112082779947379877197207) * 10 ^ 70 +
        8130234326871854785262711768016043604709880439124525856476978276137717) * 10 ^ 70 +
        8433626844911275607638585678063143507082848791798511547928709998577154) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (403 - x)) = _
  rw [show 404 = 250 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 24 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (404 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (404 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_404 :
    recurrence4Scalar0Exceptional.coeff 404 =
      ((((2952425382095459376634911087538508073355704431144642245831 * 10 ^ 70 +
        5814492228497546278037539691326375130562507303596389796924494553896945) * 10 ^ 70 +
        9823783795153560062028293866474487929203427314161973648922032806004942) * 10 ^ 70 +
        9059609609510594079668862890612457112257260623662319188542196669416197) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (404 - x)) = _
  rw [show 405 = 251 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 23 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (405 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (405 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_405 :
    recurrence4Scalar0Exceptional.coeff 405 =
      -((((806512980834959615071994046837369641344707270362128071325 * 10 ^ 70 +
        6039255677105156956081846172686318975829621257303193755726961974681354) * 10 ^ 70 +
        5096643903451295883664500516844518426521128752079825744589983538347752) * 10 ^ 70 +
        6079321096498433162676609184897686468691909392477527396546843235202239) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (405 - x)) = _
  rw [show 406 = 252 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 22 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (406 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (406 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_406 :
    recurrence4Scalar0Exceptional.coeff 406 =
      ((((199133213144971282295259157492176301610433857504525026140 * 10 ^ 70 +
        3561735705411140645028417636246099325447667115814619114764501871136335) * 10 ^ 70 +
        2678757448993217814463159895569453023912718728377033501590556000414173) * 10 ^ 70 +
        7261975360774606870534222768364646868759993756904368760475333573509835) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (406 - x)) = _
  rw [show 407 = 253 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 21 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (407 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (407 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_407 :
    recurrence4Scalar0Exceptional.coeff 407 =
      -((((41429665483284133119883178900372317275373715484395926429 * 10 ^ 70 +
        9421479310685325998446173566687875027823583093233371806417193396048930) * 10 ^ 70 +
        6934077770353185629751081477415028792055451747964782068450497335477102) * 10 ^ 70 +
        9757437858560708385517113653265451742806394080770797456069760687243650) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (407 - x)) = _
  rw [show 408 = 254 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 20 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (408 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (408 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_408 :
    recurrence4Scalar0Exceptional.coeff 408 =
      ((((5570818648312750018458961660687588901035895037739170012 * 10 ^ 70 +
        5126991629709365386932491809791559440653447064814159802912656484512703) * 10 ^ 70 +
        6492571794757620805482613045628208156930938989060866939403659617163574) * 10 ^ 70 +
        8046489731820993393229120583758340065509710452198451162381950165042668) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (408 - x)) = _
  rw [show 409 = 255 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 19 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (409 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (409 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_409 :
    recurrence4Scalar0Exceptional.coeff 409 =
      ((((656198430228002373569556812568487875463660042793028543 * 10 ^ 70 +
        6255650352572697402019466843092386174165199272240953229261836854365522) * 10 ^ 70 +
        8696847175709958525900278294900806344211099699352932460113053276835787) * 10 ^ 70 +
        9160221672656448443219589221561580634061062563506672432879750745403801) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (409 - x)) = _
  rw [show 410 = 256 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 18 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (410 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (410 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_410 :
    recurrence4Scalar0Exceptional.coeff 410 =
      -((((920412901916014344735514882385318097971281866304218893 * 10 ^ 70 +
        6831532111748675930033065461814484310289495392364135668691152455473770) * 10 ^ 70 +
        8343576772979484962407494896401077468230752029214903084871907991764688) * 10 ^ 70 +
        9644085069745485369089688349220118824971013304171522501491250291526415) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (410 - x)) = _
  rw [show 411 = 257 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 17 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (411 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (411 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_411 :
    recurrence4Scalar0Exceptional.coeff 411 =
      ((((481626565510826243437136507015861400876143291265071720 * 10 ^ 70 +
        0346708003136313074087808423272625374780688478561525722826885881789293) * 10 ^ 70 +
        7819956941910602410185351878123275551957630321702237653097954840263161) * 10 ^ 70 +
        2227673681588745378709213631153257108714082701176172047870386415002801) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (411 - x)) = _
  rw [show 412 = 258 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 16 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (412 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (412 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_412 :
    recurrence4Scalar0Exceptional.coeff 412 =
      -((((196844067355451967594237813437211097047049094708952165 * 10 ^ 70 +
        3800467965765641857007129482758913520294823142562750007047836232875069) * 10 ^ 70 +
        2331402134834873408682893193446367843013800571948503904642629371482062) * 10 ^ 70 +
        2009087110570157638538693495744529438797896444097621363774401597436931) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (412 - x)) = _
  rw [show 413 = 259 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 15 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (413 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (413 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_413 :
    recurrence4Scalar0Exceptional.coeff 413 =
      ((((70416065270452779031360162147099246613669611745336996 * 10 ^ 70 +
        4806655454352131369748185511681581809346994395308530948192421162630843) * 10 ^ 70 +
        4403409843523730429261675259518874961047255718734802290403224334271522) * 10 ^ 70 +
        1602751773831387682423437367406420158039946579058811153106519086904875) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (413 - x)) = _
  rw [show 414 = 260 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 14 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (414 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (414 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_414 :
    recurrence4Scalar0Exceptional.coeff 414 =
      -((((22882663212835547539760969905907958477731880753765399 * 10 ^ 70 +
        7731937788477214060073565930835669283669005803303311440411150643415437) * 10 ^ 70 +
        9623058175666250892307896304744170376258906648565659152081628835946356) * 10 ^ 70 +
        2992925851290132766159593812739012569226313369377240209540503800346272) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (414 - x)) = _
  rw [show 415 = 261 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 13 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (415 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (415 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_415 :
    recurrence4Scalar0Exceptional.coeff 415 =
      ((((6842969743337162984347365024704063438395062133598285 * 10 ^ 70 +
        3555099811925814528899414480806368937321970126843105042564536700264320) * 10 ^ 70 +
        2157742881314618357293187388873322300979507552821514253669909685402078) * 10 ^ 70 +
        2297161876252166866620324229978404290542322486716278843148540632068923) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (415 - x)) = _
  rw [show 416 = 262 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 12 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (416 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (416 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_416 :
    recurrence4Scalar0Exceptional.coeff 416 =
      -((((1883310982253723322013751752735123087257282253893691 * 10 ^ 70 +
        6429824986455187860855692567247654821766521874255010214494387599110549) * 10 ^ 70 +
        2856774598220067989281715131021966860527507146751789176010731176393312) * 10 ^ 70 +
        1181825394646277073236996012884043868847142728256098352720946717862751) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (416 - x)) = _
  rw [show 417 = 263 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 11 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (417 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (417 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_417 :
    recurrence4Scalar0Exceptional.coeff 417 =
      ((((471274012538713354102135600094835885829092677639626 * 10 ^ 70 +
        7436481551164849540198118226563912557426405828683602698367284859835158) * 10 ^ 70 +
        3283791375774518870576371971253229466188124070868925409521587342502543) * 10 ^ 70 +
        2499827325859187781990262389105704434610653793143246305672020672733578) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (417 - x)) = _
  rw [show 418 = 264 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 10 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (418 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (418 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_418 :
    recurrence4Scalar0Exceptional.coeff 418 =
      -((((103734961226911323312116733402754124705453469536777 * 10 ^ 70 +
        6108700789822735320626836629391117084035052541625196636171860518606268) * 10 ^ 70 +
        7291085881022976911002055202551750438937725688839872213773660039707939) * 10 ^ 70 +
        8346739798745264951344390991498744890696161586546014587349337761339184) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (418 - x)) = _
  rw [show 419 = 265 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 9 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (419 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (419 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_419 :
    recurrence4Scalar0Exceptional.coeff 419 =
      ((((18301088759530512064729082291467574535748184723812 * 10 ^ 70 +
        9923047804580879732717707982531658564793659965189790577212376095835568) * 10 ^ 70 +
        5198269222561570333666738270366289194835122860408949297222459850989312) * 10 ^ 70 +
        0978614847517419472592950227277679600854716864241755856348736553738965) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (419 - x)) = _
  rw [show 420 = 266 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 8 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (420 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (420 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_420 :
    recurrence4Scalar0Exceptional.coeff 420 =
      -((((1637354131430140398887350379809136991373190747273 * 10 ^ 70 +
        8762705199013912656953826272267511316953270315932375412937698891732662) * 10 ^ 70 +
        9383169643224079599202758827539989065835783658435729888437438072394141) * 10 ^ 70 +
        1740527598866340552281751199245313947802631597120642366706788132745106) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (420 - x)) = _
  rw [show 421 = 267 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 7 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (421 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (421 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_421 :
    recurrence4Scalar0Exceptional.coeff 421 =
      -((((535485875323484300947655259622546054319308928443 * 10 ^ 70 +
        4090070299270281697880688073096793669678494487611498860149026797124336) * 10 ^ 70 +
        8397923316177580768736321832708339249226857706470957115054217884112909) * 10 ^ 70 +
        6590842792380761868950378561408742535399056518280531750462736521576243) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (421 - x)) = _
  rw [show 422 = 268 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 6 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (422 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (422 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_422 :
    recurrence4Scalar0Exceptional.coeff 422 =
      ((((397508508587053891968141298940056925314501292738 * 10 ^ 70 +
        4426546224465833593361885876890075427038724477407659248397992059767704) * 10 ^ 70 +
        8277727215119221743931447189117916180723240555645357060257486448182358) * 10 ^ 70 +
        9776800975892061655496778691158607942024724971822007443040246834376616) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (422 - x)) = _
  rw [show 423 = 269 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 5 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (423 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (423 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_423 :
    recurrence4Scalar0Exceptional.coeff 423 =
      -((((162875151590448166703946490715910022688746465282 * 10 ^ 70 +
        6535266197349472151186628149963982751451698870336768320806493886155003) * 10 ^ 70 +
        5360890909640986999147531015528581973743772638615966497089072894857526) * 10 ^ 70 +
        9492712511245176120151970048441429118305390604648933414373101317617298) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (423 - x)) = _
  rw [show 424 = 270 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 4 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (424 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (424 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_424 :
    recurrence4Scalar0Exceptional.coeff 424 =
      ((((53256622987433692444109651195683865563041406181 * 10 ^ 70 +
        9144407404826328184877415441710343503702221260819108216258119549746408) * 10 ^ 70 +
        0775630509416636548392451149184534013393854826522331158829176980094425) * 10 ^ 70 +
        8778847097086824412771351030981005824927523133798318845801204046183473) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (424 - x)) = _
  rw [show 425 = 271 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 3 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (425 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (425 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_425 :
    recurrence4Scalar0Exceptional.coeff 425 =
      -((((14965913629277865714870306320860172757008850739 * 10 ^ 70 +
        9395594928932996545281727467423156288950059252144451917795536130036335) * 10 ^ 70 +
        4506362930620074673427208201215419172457475131565427716054088710458622) * 10 ^ 70 +
        2082277279723911008850412018867936042846801193477414295269335439210047) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (425 - x)) = _
  rw [show 426 = 272 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 2 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (426 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (426 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_426 :
    recurrence4Scalar0Exceptional.coeff 426 =
      ((((3673244043569341370924820009832470482605622193 * 10 ^ 70 +
        9803462817324321489632278051094322723543830560772841957510968899879390) * 10 ^ 70 +
        2136065454691215159054888259398151625574019960372294483890102557939194) * 10 ^ 70 +
        3631080143479163801981393271947156973206054172190983180199587272567972) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (426 - x)) = _
  rw [show 427 = 273 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 1 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (427 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (427 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_427 :
    recurrence4Scalar0Exceptional.coeff 427 =
      -((((776097125264819482813350231528279377140991987 * 10 ^ 70 +
        6586723604897731600290426680946272981776371568741565160999604778531759) * 10 ^ 70 +
        7915996452840599533010343920998828863485811009123330678385937068109246) * 10 ^ 70 +
        1057062924404154129858350504024311187405473152033728568579232358861328) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (427 - x)) = _
  rw [show 428 = 274 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (428 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (428 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_428 :
    recurrence4Scalar0Exceptional.coeff 428 =
      ((((133000544790021722063332278525478325710513668 * 10 ^ 70 +
        5593262191613228684079513817934259525885171886377457166833218491848748) * 10 ^ 70 +
        9743966918310207453978760665393537438088275375064794721105338909012252) * 10 ^ 70 +
        3205534715314874002899574437921692515572754698797869350417701151023729) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (428 - x)) = _
  rw [show 429 = 275 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 31 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (429 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (429 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_429 :
    recurrence4Scalar0Exceptional.coeff 429 =
      -((((14706203468423096805955946506553615136190732 * 10 ^ 70 +
        0153496140208521648027543045211812647265804525830163557222842098757403) * 10 ^ 70 +
        4032764845083546816560337831642226141914135809325416748079149317334821) * 10 ^ 70 +
        3086277370989275484679957091741401629123006037314831207519678371572436) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (429 - x)) = _
  rw [show 430 = 276 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 30 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (430 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (430 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_430 :
    recurrence4Scalar0Exceptional.coeff 430 =
      -((((770962222664864907458159557301240792706016 * 10 ^ 70 +
        1666032534922060397938834161590290432587330176491392721922249036520235) * 10 ^ 70 +
        2674810942798397486304790451921898723711354059366011680472433236138783) * 10 ^ 70 +
        3604988030707298716843966524768604970123515269314192103018613592639777) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (430 - x)) = _
  rw [show 431 = 277 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 29 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (431 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (431 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_431 :
    recurrence4Scalar0Exceptional.coeff 431 =
      ((((1010896728865668191979546892499962542504482 * 10 ^ 70 +
        3735850537170494337350446598611342198052282179943191118299247713610462) * 10 ^ 70 +
        6804081925447386553013921449326053493557207375020268018233171533758874) * 10 ^ 70 +
        4351327340339493723580493781402150965043689449115204274955116662740637) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (431 - x)) = _
  rw [show 432 = 278 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 28 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (432 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (432 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_432 :
    recurrence4Scalar0Exceptional.coeff 432 =
      -((((341473744337158437367946794527974772208814 * 10 ^ 70 +
        2651104280617289418171515694223740664139859318285804561594454324553307) * 10 ^ 70 +
        8623202943592106874154509545149547568708328212601806031655820197392819) * 10 ^ 70 +
        1137171995776457336990896506292105804374462420136132161451049813068375) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (432 - x)) = _
  rw [show 433 = 279 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 27 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (433 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (433 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_433 :
    recurrence4Scalar0Exceptional.coeff 433 =
      ((((76040621674297571714011341063741366988449 * 10 ^ 70 +
        2432700909966596535159298189332276481449388898185516054127743692176746) * 10 ^ 70 +
        2125027964302946153596980763878381317398180672197686918124280321800420) * 10 ^ 70 +
        9045902879858398559355970019605952541460812509072503675739971176882660) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (433 - x)) = _
  rw [show 434 = 280 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 26 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (434 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (434 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_434 :
    recurrence4Scalar0Exceptional.coeff 434 =
      -((((10334621263128917168373270903825324738060 * 10 ^ 70 +
        0626394402478028609294184881949568079399309317522624773879861478484686) * 10 ^ 70 +
        6722410223132649687482033164201199036363367530043820081223350734152870) * 10 ^ 70 +
        8961242513725903166799591384926978581175819667078898290895198010405411) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (434 - x)) = _
  rw [show 435 = 281 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 25 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (435 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (435 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_435 :
    recurrence4Scalar0Exceptional.coeff 435 =
      -((((380576595200404339169099367472476598682 * 10 ^ 70 +
        7264781448711213782213113085220257360292890901951727730866190108158274) * 10 ^ 70 +
        2029386984325533873665498570689395120506633446540254658888708624177015) * 10 ^ 70 +
        9212009137892315400233811313883414660975581319147231518683797472966854) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (435 - x)) = _
  rw [show 436 = 282 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 24 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (436 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (436 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_436 :
    recurrence4Scalar0Exceptional.coeff 436 =
      ((((803307473787058504660627045104409358132 * 10 ^ 70 +
        3372891065337004547090636509066761923909199363679856038663210745466138) * 10 ^ 70 +
        6945111480520393784453392703923843249507149949995605695941735732094875) * 10 ^ 70 +
        9301524299771822887950423248820393859845140078628385246765661557943425) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (436 - x)) = _
  rw [show 437 = 283 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 23 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (437 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (437 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_437 :
    recurrence4Scalar0Exceptional.coeff 437 =
      -((((321990930105059303121527959021152242442 * 10 ^ 70 +
        6471886577675099764565183117935476460043938648751016286090902185331926) * 10 ^ 70 +
        7660755369749955497984015921313751199054427505782555261237679907942426) * 10 ^ 70 +
        9040555878594965859395204701101831022982816315523513474615376418977003) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (437 - x)) = _
  rw [show 438 = 284 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 22 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (438 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (438 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_438 :
    recurrence4Scalar0Exceptional.coeff 438 =
      ((((90879991361692918823411900265092268101 * 10 ^ 70 +
        4695294349615868527029121919247214451976981759340502166702722943428991) * 10 ^ 70 +
        0034889839085139498103760094851773403819272520837882271071966792082061) * 10 ^ 70 +
        7045071118127124302470741446595939053470676233379508541641365884277573) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (438 - x)) = _
  rw [show 439 = 285 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 21 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (439 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (439 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_439 :
    recurrence4Scalar0Exceptional.coeff 439 =
      -((((20581679753009221524671363547728245848 * 10 ^ 70 +
        4529635916391907629828913193733769916415926372819012272277301778330690) * 10 ^ 70 +
        5285137458549522659509323049501044408312532024228648276847565517527804) * 10 ^ 70 +
        2568281275203679899150670463748760786581827544557598246111240222611019) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (439 - x)) = _
  rw [show 440 = 286 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 20 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (440 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (440 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_440 :
    recurrence4Scalar0Exceptional.coeff 440 =
      ((((3820399604410282246951866410884743359 * 10 ^ 70 +
        1351654698466901918785924346804202549108764919777357690870988058430494) * 10 ^ 70 +
        1571357540896864528446426547875544866135926151493925433322484657455065) * 10 ^ 70 +
        1407738802877950761481523647972370821235114896147712005004796550392274) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (440 - x)) = _
  rw [show 441 = 287 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 19 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (441 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (441 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_441 :
    recurrence4Scalar0Exceptional.coeff 441 =
      -((((558170838316779481597228461029394928 * 10 ^ 70 +
        6019365562369104634352303388938556650425885878783315051771913230223656) * 10 ^ 70 +
        2874745751419333142248437137743573863000444601957489664028378062521660) * 10 ^ 70 +
        9457408767066838297212841489518339688782789700383636803085221070995219) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (441 - x)) = _
  rw [show 442 = 288 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 18 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (442 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (442 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_442 :
    recurrence4Scalar0Exceptional.coeff 442 =
      ((((52624100406827810439617102082628524 * 10 ^ 70 +
        8533015929326885706186267055583624498167585487630800798182964391949737) * 10 ^ 70 +
        7161302478571228395334523997960618385127454106922517522887067115676610) * 10 ^ 70 +
        8798807967547002194679878349673822855772614013696347010163400394268194) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (442 - x)) = _
  rw [show 443 = 289 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 17 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (443 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (443 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_443 :
    recurrence4Scalar0Exceptional.coeff 443 =
      ((((1397854953052244560805083389283093 * 10 ^ 70 +
        5090444291089623819888921580206830419047866480463849309395372458468586) * 10 ^ 70 +
        4576813403118823977300964082847649706883203716757051438484269460523680) * 10 ^ 70 +
        8961682655105526657144183605276130932979761647233288070230163619440169) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (443 - x)) = _
  rw [show 444 = 290 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 16 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (444 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (444 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_444 :
    recurrence4Scalar0Exceptional.coeff 444 =
      -((((2034843840858973847393315494404879 * 10 ^ 70 +
        3672163697034191254370787682983602337260282870118725101976457157962831) * 10 ^ 70 +
        4165691263963072569673050755710961150455168777911140608859152982796890) * 10 ^ 70 +
        1919465634937879163150233936589621658835924731452855593719435879825174) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (444 - x)) = _
  rw [show 445 = 291 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 15 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (445 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (445 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_445 :
    recurrence4Scalar0Exceptional.coeff 445 =
      ((((557540146467924491974920148450663 * 10 ^ 70 +
        8885607317896464958903879236920144798721932707085736854207577526084882) * 10 ^ 70 +
        3485634239374716619563865417579960905684952360807566676321182188067671) * 10 ^ 70 +
        7856386644153769093516198406446661340356629955323273726370560152636810) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (445 - x)) = _
  rw [show 446 = 292 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 14 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (446 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (446 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_446 :
    recurrence4Scalar0Exceptional.coeff 446 =
      -((((102277649736512387754128157444960 * 10 ^ 70 +
        0044095232143655021009106713486199716222183367742239237140692655021118) * 10 ^ 70 +
        1653494257008526222021763486641840053105585641182143706075308391688174) * 10 ^ 70 +
        3310076933273464743891968654798449475008095441485442563757776565197148) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (446 - x)) = _
  rw [show 447 = 293 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 13 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (447 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (447 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_447 :
    recurrence4Scalar0Exceptional.coeff 447 =
      ((((13502304898627498700159721009157 * 10 ^ 70 +
        2201359234691220594094792037603982722150444867086288834554440147748708) * 10 ^ 70 +
        9565340892561059853545219933218774872129304330619178386516693537180864) * 10 ^ 70 +
        2203426212164510907226411634639558140241750690589501795887541673197053) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (447 - x)) = _
  rw [show 448 = 294 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 12 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (448 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (448 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_448 :
    recurrence4Scalar0Exceptional.coeff 448 =
      -((((1051364143135405274273902591280 * 10 ^ 70 +
        3269834057908922418572492465607976389342331374624084842221050854016232) * 10 ^ 70 +
        4644141832483459512844142871739928412051694582781163250927409514825289) * 10 ^ 70 +
        9975997571114576910891379674822582052085853074089721929051109640932285) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (448 - x)) = _
  rw [show 449 = 295 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 11 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (449 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (449 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_449 :
    recurrence4Scalar0Exceptional.coeff 449 =
      -((((45381142458481345995929124815 * 10 ^ 70 +
        1748612041227966269029858997067072841776027851272769665588269623307714) * 10 ^ 70 +
        3511370111374712001927789478033445786073586835233814753374971187099996) * 10 ^ 70 +
        0837692887441067069465985724717360988014299687405216803502754105732783) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (449 - x)) = _
  rw [show 450 = 296 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 10 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (450 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (450 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_450 :
    recurrence4Scalar0Exceptional.coeff 450 =
      ((((33946465908752928989406183249 * 10 ^ 70 +
        8574296862983650133849991330372123201318205147033895306640103118536444) * 10 ^ 70 +
        9942347967561418079262704407051377484728427103690173384114308562341803) * 10 ^ 70 +
        2608401267222652086571799025242497958450811134357243556209078611865884) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (450 - x)) = _
  rw [show 451 = 297 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 9 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (451 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (451 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_451 :
    recurrence4Scalar0Exceptional.coeff 451 =
      -((((7020827267861757350875499727 * 10 ^ 70 +
        8245475794583468439879913666298947614546346439629221128108737558579823) * 10 ^ 70 +
        4644229292361418890637384417803261287018589621253358188862858724252298) * 10 ^ 70 +
        0670608235486718257117847968696054284845338458264279115075641232797672) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (451 - x)) = _
  rw [show 452 = 298 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 8 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (452 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (452 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_452 :
    recurrence4Scalar0Exceptional.coeff 452 =
      ((((924367277206443412180772129 * 10 ^ 70 +
        9184826182483272729158847778786671472340208460146172096038192723631075) * 10 ^ 70 +
        1730065706036669414278638757374371125776522394936642171501275606584534) * 10 ^ 70 +
        8557136171086853941206798486399143704550664578878572120462525813797234) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (452 - x)) = _
  rw [show 453 = 299 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 7 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (453 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (453 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_453 :
    recurrence4Scalar0Exceptional.coeff 453 =
      -((((72236987402328521620601099 * 10 ^ 70 +
        1529175397291532714984529665745570725473569992228378574237048061828341) * 10 ^ 70 +
        3172855074777222534382011215011798935385835973738156862392589759392775) * 10 ^ 70 +
        4549444738507353338973305197280665993310911112410329358120585596594425) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (453 - x)) = _
  rw [show 454 = 300 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 6 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (454 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (454 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_454 :
    recurrence4Scalar0Exceptional.coeff 454 =
      -((((767770970765138619500418 * 10 ^ 70 +
        8119599096761271076563932497624438652676536127071341973071520547929808) * 10 ^ 70 +
        4375836024435825898969722581061622913340978825307485761131963908335075) * 10 ^ 70 +
        3601670622062676519008125492533039949288198234090011331751489193964782) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (454 - x)) = _
  rw [show 455 = 301 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 5 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (455 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (455 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_455 :
    recurrence4Scalar0Exceptional.coeff 455 =
      ((((1298178259779020306066745 * 10 ^ 70 +
        3792450777933830724202614158602830969847405517851863529550901145772053) * 10 ^ 70 +
        4022955929648018621460825973385990672360989286195781051171920535837164) * 10 ^ 70 +
        0657952087937337029916980340545130495807845725783578362801530839605475) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (455 - x)) = _
  rw [show 456 = 302 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 4 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (456 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (456 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_456 :
    recurrence4Scalar0Exceptional.coeff 456 =
      -((((233200877200673259376907 * 10 ^ 70 +
        3486604966594828766687276902523546527992602268885470690704644640702075) * 10 ^ 70 +
        3669353940071224402050360244019489710968393933872586004114010296597961) * 10 ^ 70 +
        6548011405952318659677627490052415474321136188467418506715248272216979) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (456 - x)) = _
  rw [show 457 = 303 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 3 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (457 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (457 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_457 :
    recurrence4Scalar0Exceptional.coeff 457 =
      ((((23928898092908558488039 * 10 ^ 70 +
        5276064653661205851069338012338299691417668417958739283627879021022879) * 10 ^ 70 +
        8305266760362853962470219303954359586065252180911978175681172722829713) * 10 ^ 70 +
        6935527360972411638850093972953864552941826747591302653376907568338553) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (457 - x)) = _
  rw [show 458 = 304 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 2 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (458 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (458 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_458 :
    recurrence4Scalar0Exceptional.coeff 458 =
      -((((1091016563074535658570 * 10 ^ 70 +
        1194569302197290634073598385918046781745109837790481230308258895615641) * 10 ^ 70 +
        5956035358662514764289688618993465289903129138942415600015325747070388) * 10 ^ 70 +
        4818006857635475079905043682859277373542146868772078141738400092913527) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (458 - x)) = _
  rw [show 459 = 305 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 1 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (459 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (459 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_459 :
    recurrence4Scalar0Exceptional.coeff 459 =
      -((((107380896837613466739 * 10 ^ 70 +
        7882668514567539274472130635719604130714683637153837216731987921468373) * 10 ^ 70 +
        3273697752603384740234056094303614549651240932045252337908356485825470) * 10 ^ 70 +
        7876000763780861946897071368860676515508490701456714871666787030283540) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (459 - x)) = _
  rw [show 460 = 306 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (460 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (460 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_460 :
    recurrence4Scalar0Exceptional.coeff 460 =
      ((((28182719081739819026 * 10 ^ 70 +
        7726572179240716598330415013642707853503296076513986307738341016530028) * 10 ^ 70 +
        7676174015972353547262878501941370211784695833777599472814869671318764) * 10 ^ 70 +
        4172253474219983454646295242113501680805960063613676909211225811052151) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (460 - x)) = _
  rw [show 461 = 307 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 31 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (461 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (461 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_461 :
    recurrence4Scalar0Exceptional.coeff 461 =
      -((((2925036819263739367 * 10 ^ 70 +
        8091655640076324439389928070122155971313730906319498272110631896149121) * 10 ^ 70 +
        6654643196281554868540356508053547384968548543184996498969171719904523) * 10 ^ 70 +
        2978570431915826751297490161584802137733454057005547106083883097225356) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (461 - x)) = _
  rw [show 462 = 308 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 30 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (462 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (462 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_462 :
    recurrence4Scalar0Exceptional.coeff 462 =
      ((((126072719556696241 * 10 ^ 70 +
        5775675693415950579823048695931102880487920071453695398028352593464005) * 10 ^ 70 +
        3566316525469205138640257691454012761237930963749886181755067166014520) * 10 ^ 70 +
        5210379132688362400950155410798799500432260498032218347116246495960757) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (462 - x)) = _
  rw [show 463 = 309 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 29 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (463 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (463 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_463 :
    recurrence4Scalar0Exceptional.coeff 463 =
      ((((9789757490892559 * 10 ^ 70 +
        7541955830962332243128219797807235634544352711762554237647618112167371) * 10 ^ 70 +
        1642821750294917721995689787759518386776854112099580794478499689931707) * 10 ^ 70 +
        8096916596547525949406017120833970377376523702448844501343563555136875) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (463 - x)) = _
  rw [show 464 = 310 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 28 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (464 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (464 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_464 :
    recurrence4Scalar0Exceptional.coeff 464 =
      -((((2185530664460353 * 10 ^ 70 +
        3445053451457734186666014467753942810698352314724818792751461841132610) * 10 ^ 70 +
        9065668624715337520601049093715934345157807194183951935868909521116817) * 10 ^ 70 +
        0913665176275139061080214158876051501745343366616585437173786657805913) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (464 - x)) = _
  rw [show 465 = 311 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 27 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (465 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (465 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_465 :
    recurrence4Scalar0Exceptional.coeff 465 =
      ((((167946123440084 * 10 ^ 70 +
        3431642225185015355717015844349336766100071456493915573610795249953299) * 10 ^ 70 +
        0074774344784214742418852625624610806689246583186983289285244743870734) * 10 ^ 70 +
        9636758438148653690141950809207089210800736876999866523385453210338390) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (465 - x)) = _
  rw [show 466 = 312 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 26 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (466 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (466 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_466 :
    recurrence4Scalar0Exceptional.coeff 466 =
      -((((2086274748761 * 10 ^ 70 +
        4783282960938082687644683021380440279980451850400463988188421366410850) * 10 ^ 70 +
        6064247517421501729750774478172797199521007625255320872076117229560598) * 10 ^ 70 +
        7423869105688534418333931722195993547702789749711299312100782587700037) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (466 - x)) = _
  rw [show 467 = 313 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 25 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (467 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (467 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_467 :
    recurrence4Scalar0Exceptional.coeff 467 =
      -((((878334476039 * 10 ^ 70 +
        8368115961676240986496179832831152789410587640335988369695436177593700) * 10 ^ 70 +
        1950687907315001298759422905659740223913126557129714105006771893834364) * 10 ^ 70 +
        9247683008860408674651314888432493645489611966860109092466175175999875) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (467 - x)) = _
  rw [show 468 = 314 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 24 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (468 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (468 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_468 :
    recurrence4Scalar0Exceptional.coeff 468 =
      ((((89849517449 * 10 ^ 70 +
        8159165791590109436108560707460202708605297338609921025415391354403582) * 10 ^ 70 +
        6178950036135024886539730930971219529790324820521750203059952671318819) * 10 ^ 70 +
        7542087431697521401587905978668020740399096229169458660982139994804498) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (468 - x)) = _
  rw [show 469 = 315 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 23 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (469 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (469 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_469 :
    recurrence4Scalar0Exceptional.coeff 469 =
      -((((2534972463 * 10 ^ 70 +
        6217359423015600984915209091440974402489999187455590410617238267752920) * 10 ^ 70 +
        5043534191248888425895525815226104539761025053076607606818802003415829) * 10 ^ 70 +
        4078603209044187464965439134475470307604807193466209529547870174780160) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (469 - x)) = _
  rw [show 470 = 316 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 22 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (470 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (470 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_470 :
    recurrence4Scalar0Exceptional.coeff 470 =
      -((((256415814 * 10 ^ 70 +
        3861364316962176433783697588153224172855691707225439129775141475359619) * 10 ^ 70 +
        5395533657053614442039067326781088019498253250336483953854862916108516) * 10 ^ 70 +
        8431184402938852129692087120552381500019742633981106218291418740544416) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (470 - x)) = _
  rw [show 471 = 317 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 21 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (471 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (471 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_471 :
    recurrence4Scalar0Exceptional.coeff 471 =
      ((((28552367 * 10 ^ 70 +
        6168416211630622739333387552283251566811496358575246298599915214845954) * 10 ^ 70 +
        5514663052523696320032972373101868526518221415055179232423715285879645) * 10 ^ 70 +
        1348856498245856454881303601422106108307047171810270633612842595774996) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (471 - x)) = _
  rw [show 472 = 318 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 20 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (472 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (472 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_472 :
    recurrence4Scalar0Exceptional.coeff 472 =
      -((((663060 * 10 ^ 70 +
        7966003511025815563570103583173219337493009804941981285865617400799945) * 10 ^ 70 +
        8805859409188140534880718349476799821893032458910439255518014598451270) * 10 ^ 70 +
        1955070633425741723510306224141324352631381308754512551768096778894488) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (472 - x)) = _
  rw [show 473 = 319 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 19 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (473 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (473 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_473 :
    recurrence4Scalar0Exceptional.coeff 473 =
      -((((70370 * 10 ^ 70 +
        4675945737897540268594071417570684498074788796542836261162593160286638) * 10 ^ 70 +
        7779707867842865843865187418273697469428892954765141220940784502601332) * 10 ^ 70 +
        9478040983560835312335643143762411045145491997395877995874216179598774) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (473 - x)) = _
  rw [show 474 = 320 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 18 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (474 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (474 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_474 :
    recurrence4Scalar0Exceptional.coeff 474 =
      ((((5460 * 10 ^ 70 +
        8716942346683647656873926504960573034919271449781352670026109259247898) * 10 ^ 70 +
        7905084872195422813883891012961137846021111046894134085386136931177253) * 10 ^ 70 +
        4277668761432531597404181844151493951194009908270609884154068529831116) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (474 - x)) = _
  rw [show 475 = 321 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 17 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (475 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (475 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_475 :
    recurrence4Scalar0Exceptional.coeff 475 =
      -((((4 * 10 ^ 70 +
        6742626416339030508725292742302329990878276696789623280336385513432301) * 10 ^ 70 +
        6529668237500540474101639441061524827618571713132944300000813505236100) * 10 ^ 70 +
        8858150111031954582466669255020413884289928072964149584271227771981482) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (475 - x)) = _
  rw [show 476 = 322 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 16 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (476 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (476 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_476 :
    recurrence4Scalar0Exceptional.coeff 476 =
      -((((14 * 10 ^ 70 +
        5188847402902634194915129380739731957748115544021802332256534736355035) * 10 ^ 70 +
        9093960248108033096286730550564504285192631547031326245555300110373608) * 10 ^ 70 +
        0982853909765676979861185971238940364997946715598160822137895844673669) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (476 - x)) = _
  rw [show 477 = 323 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 15 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (477 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (477 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_477 :
    recurrence4Scalar0Exceptional.coeff 477 =
      (((3940594030923596849083134635246755799430329879156517607153460383260056 * 10 ^ 70 +
        3875494645906063923507100889030517703644927445515590946066496255005740) * 10 ^ 70 +
        8448615048852098711033079890690297905297808517800681723027059567324605) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (477 - x)) = _
  rw [show 478 = 324 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 14 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (478 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (478 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_478 :
    recurrence4Scalar0Exceptional.coeff 478 =
      (((231928301375223469951224932644657305708855454389963491423836445589309 * 10 ^ 70 +
        7692603975812027547628973560031720793354645271787012646284164126800587) * 10 ^ 70 +
        5887992200395886320031295425483400284189085262970780113381922825142270) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (478 - x)) = _
  rw [show 479 = 325 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 13 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (479 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (479 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_479 :
    recurrence4Scalar0Exceptional.coeff 479 =
      -(((10675728104722091657643652491330164684320277795369760146394400763048 * 10 ^ 70 +
        0846719910688413439532708382941066873014148281802976420966486794547727) * 10 ^ 70 +
        3564514157761383543246047468285388122432043865600213436892913827125685) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (479 - x)) = _
  rw [show 480 = 326 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 12 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_479_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (480 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (480 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_480 :
    recurrence4Scalar0Exceptional.coeff 480 =
      -(((309861118206281667262443652045650593918428786526157804338132941684 * 10 ^ 70 +
        9961711815781381275821758322490661611931640976674669551767020502578851) * 10 ^ 70 +
        4882911758656472092113092867647792476704161181363076196864077206831980) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (480 - x)) = _
  rw [show 481 = 327 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 11 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_480_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (481 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (481 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_481 :
    recurrence4Scalar0Exceptional.coeff 481 =
      (((16418137254648915627635830316823652806158574078380200596167163672 * 10 ^ 70 +
        6660520336860952205351234502209372387376972747998501429425458788204608) * 10 ^ 70 +
        0456887231944712145241964975963212137968370684776562452680969299129213) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (481 - x)) = _
  rw [show 482 = 328 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 10 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_481_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (482 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (482 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_482 :
    recurrence4Scalar0Exceptional.coeff 482 =
      (((476191923252963494969215275226904797352527463354142365921461427 * 10 ^ 70 +
        1061590265814927261965803044663420198738625646225534670336821178586962) * 10 ^ 70 +
        8037206993378307037546781671147181056632003648962213594027408044569371) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (482 - x)) = _
  rw [show 483 = 329 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 9 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_482_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (483 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (483 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_483 :
    recurrence4Scalar0Exceptional.coeff 483 =
      -(((14298872675626567034070466175550466674398478073437674475559655 * 10 ^ 70 +
        1695497638791954125375098575819274328579198246134964077922857757968046) * 10 ^ 70 +
        9940928091169514887293518075376650161966294700254424951882483374378625) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (483 - x)) = _
  rw [show 484 = 330 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 8 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_483_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (484 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (484 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_484 :
    recurrence4Scalar0Exceptional.coeff 484 =
      -(((702927924897485792710765988972345207397622071170361917005248 * 10 ^ 70 +
        2644413027574075102186442561243581114149657171652098634205261452485940) * 10 ^ 70 +
        2798486369548455472722597744691075170178043747113958429599233129681771) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (484 - x)) = _
  rw [show 485 = 331 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 7 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_484_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (485 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (485 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_485 :
    recurrence4Scalar0Exceptional.coeff 485 =
      -(((1820178933304006765632785303205061758489537760010444343073 * 10 ^ 70 +
        5424955370400467527345246292444317937265326523369868672397259309583893) * 10 ^ 70 +
        1859129399232396939557598811935347607469187785874582419616116550916822) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (485 - x)) = _
  rw [show 486 = 332 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 6 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_485_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (486 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (486 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_486 :
    recurrence4Scalar0Exceptional.coeff 486 =
      (((498577916506960421889880774848928869419302896656776918822 * 10 ^ 70 +
        1380804391243487158909407784530714912389126252042362907169855442425140) * 10 ^ 70 +
        5805524473315710914077059913764169590767699881611841658498367297599645) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (486 - x)) = _
  rw [show 487 = 333 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 5 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_486_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (487 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (487 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_487 :
    recurrence4Scalar0Exceptional.coeff 487 =
      (((16567097677934630083080060409803202716961738859595017485 * 10 ^ 70 +
        0625431883924665692038217613819276303160871126119942904071788060588693) * 10 ^ 70 +
        5506290252595504882830359744116239754146768168743695459855285720716353) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (487 - x)) = _
  rw [show 488 = 334 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 4 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_487_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (488 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (488 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_488 :
    recurrence4Scalar0Exceptional.coeff 488 =
      (((296804508021520242856116467294620611087189013243866486 * 10 ^ 70 +
        6149222710414392257091840713706061534965834092118802571655667237091238) * 10 ^ 70 +
        6523440474231424860362111578198779069129014821090362217514024036156390) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (488 - x)) = _
  rw [show 489 = 335 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 3 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_488_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (489 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (489 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_489 :
    recurrence4Scalar0Exceptional.coeff 489 =
      (((3552351254040855815854274790990883454339494940364118 * 10 ^ 70 +
        1753605500098706910701026170235674783982594472215425659351479331659314) * 10 ^ 70 +
        6665153357057558399963087960996331419815186476593489164841250984319639) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (489 - x)) = _
  rw [show 490 = 336 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 2 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_489_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (490 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (490 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_490 :
    recurrence4Scalar0Exceptional.coeff 490 =
      (((30314968081967686666231803524385956079702668433021 * 10 ^ 70 +
        8291486824340005969132431861039523665597052979357004699611216055501912) * 10 ^ 70 +
        4570269643005485324042561666334777092500002861035334815802971391036669) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (490 - x)) = _
  rw [show 491 = 337 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 1 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_490_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (491 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (491 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_491 :
    recurrence4Scalar0Exceptional.coeff 491 =
      (((187828524247471685916255385625784868173971166658 * 10 ^ 70 +
        9201853050864360918777217165896369444855029195164776795178036799311719) * 10 ^ 70 +
        8572355633836728939112325939725273143282965020944252776039202179179295) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (491 - x)) = _
  rw [show 492 = 338 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_491_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (492 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (492 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_492 :
    recurrence4Scalar0Exceptional.coeff 492 =
      (((831446871364505395863153940892421869474548479 * 10 ^ 70 +
        8867892909027045702161880047978474463447560753400001272210946648427680) * 10 ^ 70 +
        3485786126566976031867588592233298487392785167726804501028636733973358) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (492 - x)) = _
  rw [show 493 = 339 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 31 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_492_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (493 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (493 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_493 :
    recurrence4Scalar0Exceptional.coeff 493 =
      (((2434033337279625493346609129562491959126838 * 10 ^ 70 +
        6172473309420902917990117472725803966151175601677635393780248481741943) * 10 ^ 70 +
        1914014567079392643005505193627360883739060317566477528749966848664097) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (493 - x)) = _
  rw [show 494 = 340 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 30 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_493_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (494 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (494 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_494 :
    recurrence4Scalar0Exceptional.coeff 494 =
      (((3281546116119408109543529437824047100387 * 10 ^ 70 +
        0931261817819028202642829314990847472471697742998189027499920802454752) * 10 ^ 70 +
        2364278723388690708436322405365203562122118451910721473365694229469431) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (494 - x)) = _
  rw [show 495 = 341 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 29 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_494_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (495 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (495 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_495 :
    recurrence4Scalar0Exceptional.coeff 495 =
      -(((7050752144496660859232209090654253568 * 10 ^ 70 +
        8857848249586823173257142301544913611344207398776367860758426298936018) * 10 ^ 70 +
        5965909051805285785402629592117303444468824592883371175434543242452445) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (495 - x)) = _
  rw [show 496 = 342 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 28 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_495_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (496 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (496 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_496 :
    recurrence4Scalar0Exceptional.coeff 496 =
      -(((48384695404963728068003295673854046 * 10 ^ 70 +
        7110122738691361286903915159095082116156164795234264753795820415795173) * 10 ^ 70 +
        3316116341809034983188056605077240030200685362430450447239384891707494) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (496 - x)) = _
  rw [show 497 = 343 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 27 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_496_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (497 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (497 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_497 :
    recurrence4Scalar0Exceptional.coeff 497 =
      -(((110248639811137431699946060101742 * 10 ^ 70 +
        8639414564210900062804237003334452450908641283466359197130648957990504) * 10 ^ 70 +
        5628783524623460353196434869139445603719470641482827133489321531526440) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (497 - x)) = _
  rw [show 498 = 344 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 26 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_497_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (498 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (498 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_498 :
    recurrence4Scalar0Exceptional.coeff 498 =
      -(((71287272851575010908619170212 * 10 ^ 70 +
        1727268054337013658971003850930458602363881921884204152773741487716021) * 10 ^ 70 +
        2393528558810003409671479264251288981186216332066205489307235355187653) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (498 - x)) = _
  rw [show 499 = 345 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 25 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_498_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (499 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (499 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_499 :
    recurrence4Scalar0Exceptional.coeff 499 =
      (((256824016551972476232998496 * 10 ^ 70 +
        9878528161488561045003440293060315678675418135193124980082027678188559) * 10 ^ 70 +
        2105657968825841203473911995221436099385102066512123784956300818839280) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (499 - x)) = _
  rw [show 500 = 346 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 24 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_499_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (500 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (500 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_500 :
    recurrence4Scalar0Exceptional.coeff 500 =
      (((777424943864960482327017 * 10 ^ 70 +
        0533972914151150634987567430320015071437848140331271625219512644720224) * 10 ^ 70 +
        6753550121230660815420413399734877206463199548805817331890403075807062) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (500 - x)) = _
  rw [show 501 = 347 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 23 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_500_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (501 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (501 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_501 :
    recurrence4Scalar0Exceptional.coeff 501 =
      (((850022610231611701765 * 10 ^ 70 +
        1509985286514929337469302067542126843950295481085582179341755962002458) * 10 ^ 70 +
        7018794648607823560811636040950416696829544675302094558818373211659452) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (501 - x)) = _
  rw [show 502 = 348 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 22 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_501_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (502 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (502 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_502 :
    recurrence4Scalar0Exceptional.coeff 502 =
      -(((78948191040595522 * 10 ^ 70 +
        1793587031040301661941405694251083906718244312948862789722477756952386) * 10 ^ 70 +
        7856469091837378853800486035312613508792486641820711497823606628034614) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (502 - x)) = _
  rw [show 503 = 349 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 21 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_502_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (503 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (503 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_503 :
    recurrence4Scalar0Exceptional.coeff 503 =
      -(((1478905795024394 * 10 ^ 70 +
        6015324338346126653006800226068378770277049270232273444598252911398000) * 10 ^ 70 +
        2001786037693027128703654669532069863422111923735902936042286292765965) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (503 - x)) = _
  rw [show 504 = 350 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 20 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_503_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (504 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (504 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_504 :
    recurrence4Scalar0Exceptional.coeff 504 =
      -(((2139703211890 * 10 ^ 70 +
        7808504092964537131708214860821993946555024056374459447242567424873677) * 10 ^ 70 +
        3564889156918355362902571879005781578213048506529759422996586430456998) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (504 - x)) = _
  rw [show 505 = 351 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 19 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_504_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (505 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (505 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_505 :
    recurrence4Scalar0Exceptional.coeff 505 =
      -(((1686622926 * 10 ^ 70 +
        6985556898007609979058343581968762277892310974709768806307811408875162) * 10 ^ 70 +
        5310615087521940988861115008485420109869094447407971007099487898091272) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (505 - x)) = _
  rw [show 506 = 352 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 18 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_505_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (506 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (506 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_506 :
    recurrence4Scalar0Exceptional.coeff 506 =
      -(((837304 * 10 ^ 70 +
        2435150622825201250585750734732385486751692862339135210225083072427791) * 10 ^ 70 +
        9006270472361628789501376976451901212500636046307050557263918510527995) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (506 - x)) = _
  rw [show 507 = 353 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 17 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_506_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (507 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (507 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_507 :
    recurrence4Scalar0Exceptional.coeff 507 =
      -(((270 * 10 ^ 70 +
        7168505025681173241535425202696638607463500831103899803920025983808468) * 10 ^ 70 +
        4147120035657768556488644458533428393963812241733057604814377564193219) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (507 - x)) = _
  rw [show 508 = 354 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 16 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_507_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (508 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (508 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_508 :
    recurrence4Scalar0Exceptional.coeff 508 =
      -((571510890788333141681898249869711605340839919739387693251189029028217 * 10 ^ 70 +
        5260585547983821109238505912164661181817098475361788924598477343383300) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (508 - x)) = _
  rw [show 509 = 355 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 15 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_508_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (509 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (509 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_509 :
    recurrence4Scalar0Exceptional.coeff 509 =
      -((77952753563820855005863900463487910766704327755987424334851468613 * 10 ^ 70 +
        7964330532477854512196385152644997980812375955610815298800331903117160) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (509 - x)) = _
  rw [show 510 = 356 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 14 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_509_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (510 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (510 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_510 :
    recurrence4Scalar0Exceptional.coeff 510 =
      -((6746670007910060273459004301607818686829002754440784498254728 * 10 ^ 70 +
        7317680955183227704413451001413615371320563684865689240154230605796603) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (510 - x)) = _
  rw [show 511 = 357 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 13 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_510_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (511 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (511 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_511 :
    recurrence4Scalar0Exceptional.coeff 511 =
      -((360707140470861118647986809372183922576515143726412761503 * 10 ^ 70 +
        3234518807000671799409086415059765763784573409813623398357234307711470) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (511 - x)) = _
  rw [show 512 = 358 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 12 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_511_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
