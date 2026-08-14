/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0ExceptionalPart3Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
