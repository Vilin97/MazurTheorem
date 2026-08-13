/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C2_coeff_10
  recurrence4C2_coeff_100
  recurrence4C2_coeff_101
  recurrence4C2_coeff_102
  recurrence4C2_coeff_103
  recurrence4C2_coeff_104
  recurrence4C2_coeff_105
  recurrence4C2_coeff_106
  recurrence4C2_coeff_107
  recurrence4C2_coeff_108
  recurrence4C2_coeff_109
  recurrence4C2_coeff_11
  recurrence4C2_coeff_110
  recurrence4C2_coeff_111
  recurrence4C2_coeff_112
  recurrence4C2_coeff_113
  recurrence4C2_coeff_114
  recurrence4C2_coeff_115
  recurrence4C2_coeff_116
  recurrence4C2_coeff_117
  recurrence4C2_coeff_118
  recurrence4C2_coeff_119
  recurrence4C2_coeff_12
  recurrence4C2_coeff_120
  recurrence4C2_coeff_121
  recurrence4C2_coeff_122
  recurrence4C2_coeff_123
  recurrence4C2_coeff_124
  recurrence4C2_coeff_125
  recurrence4C2_coeff_126
  recurrence4C2_coeff_127
  recurrence4C2_coeff_128
  recurrence4C2_coeff_129
  recurrence4C2_coeff_13
  recurrence4C2_coeff_130
  recurrence4C2_coeff_131
  recurrence4C2_coeff_132
  recurrence4C2_coeff_133
  recurrence4C2_coeff_134
  recurrence4C2_coeff_135
  recurrence4C2_coeff_136
  recurrence4C2_coeff_137
  recurrence4C2_coeff_138
  recurrence4C2_coeff_139
  recurrence4C2_coeff_14
  recurrence4C2_coeff_140
  recurrence4C2_coeff_141
  recurrence4C2_coeff_142
  recurrence4C2_coeff_143
  recurrence4C2_coeff_144
  recurrence4C2_coeff_145
  recurrence4C2_coeff_15
  recurrence4C2_coeff_16
  recurrence4C2_coeff_17
  recurrence4C2_coeff_18
  recurrence4C2_coeff_19
  recurrence4C2_coeff_20
  recurrence4C2_coeff_21
  recurrence4C2_coeff_22
  recurrence4C2_coeff_23
  recurrence4C2_coeff_24
  recurrence4C2_coeff_25
  recurrence4C2_coeff_26
  recurrence4C2_coeff_27

attribute [local simp]
  recurrence4C2_coeff_28
  recurrence4C2_coeff_29
  recurrence4C2_coeff_3
  recurrence4C2_coeff_30
  recurrence4C2_coeff_31
  recurrence4C2_coeff_32
  recurrence4C2_coeff_33
  recurrence4C2_coeff_34
  recurrence4C2_coeff_35
  recurrence4C2_coeff_36
  recurrence4C2_coeff_37
  recurrence4C2_coeff_38
  recurrence4C2_coeff_39
  recurrence4C2_coeff_4
  recurrence4C2_coeff_40
  recurrence4C2_coeff_41
  recurrence4C2_coeff_42
  recurrence4C2_coeff_43
  recurrence4C2_coeff_44
  recurrence4C2_coeff_45
  recurrence4C2_coeff_46
  recurrence4C2_coeff_47
  recurrence4C2_coeff_48
  recurrence4C2_coeff_49
  recurrence4C2_coeff_5
  recurrence4C2_coeff_50
  recurrence4C2_coeff_51
  recurrence4C2_coeff_52
  recurrence4C2_coeff_53
  recurrence4C2_coeff_54
  recurrence4C2_coeff_55
  recurrence4C2_coeff_56
  recurrence4C2_coeff_57
  recurrence4C2_coeff_58
  recurrence4C2_coeff_59
  recurrence4C2_coeff_6
  recurrence4C2_coeff_60
  recurrence4C2_coeff_61
  recurrence4C2_coeff_62
  recurrence4C2_coeff_63
  recurrence4C2_coeff_64
  recurrence4C2_coeff_65
  recurrence4C2_coeff_66
  recurrence4C2_coeff_67
  recurrence4C2_coeff_68
  recurrence4C2_coeff_69
  recurrence4C2_coeff_7
  recurrence4C2_coeff_70
  recurrence4C2_coeff_71
  recurrence4C2_coeff_72
  recurrence4C2_coeff_73
  recurrence4C2_coeff_74
  recurrence4C2_coeff_75
  recurrence4C2_coeff_76
  recurrence4C2_coeff_77
  recurrence4C2_coeff_78
  recurrence4C2_coeff_79
  recurrence4C2_coeff_8
  recurrence4C2_coeff_80
  recurrence4C2_coeff_81
  recurrence4C2_coeff_82
  recurrence4C2_coeff_83
  recurrence4C2_coeff_84
  recurrence4C2_coeff_85

attribute [local simp]
  recurrence4C2_coeff_86
  recurrence4C2_coeff_87
  recurrence4C2_coeff_88
  recurrence4C2_coeff_89
  recurrence4C2_coeff_9
  recurrence4C2_coeff_90
  recurrence4C2_coeff_91
  recurrence4C2_coeff_92
  recurrence4C2_coeff_93
  recurrence4C2_coeff_94
  recurrence4C2_coeff_95
  recurrence4C2_coeff_96
  recurrence4C2_coeff_97
  recurrence4C2_coeff_98
  recurrence4C2_coeff_99
  recurrence4ExceptionalProduct_coeff_227
  recurrence4ExceptionalProduct_coeff_228
  recurrence4ExceptionalProduct_coeff_229
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_276
  recurrence4ExceptionalProduct_coeff_277
  recurrence4ExceptionalProduct_coeff_278
  recurrence4ExceptionalProduct_coeff_279
  recurrence4ExceptionalProduct_coeff_280
  recurrence4ExceptionalProduct_coeff_281
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_340
  recurrence4ExceptionalProduct_coeff_341
  recurrence4ExceptionalProduct_coeff_342
  recurrence4ExceptionalProduct_coeff_343
  recurrence4ExceptionalProduct_coeff_344
  recurrence4ExceptionalProduct_coeff_345
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

private theorem recurrence4Scalar2Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (423 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_423 :
    recurrence4Scalar2Exceptional.coeff 423 =
      -((((17108642796812232101131162594878865739552414 * 10 ^ 70 +
        9588755504171675162481548799658251996283523915641316786683297337445410) * 10 ^ 70 +
        8042084131477520662461887144417311839548536339829177229240964249754930) * 10 ^ 70 +
        9335339415861802338235110000103177919184614154929812368738491358127382) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (423 - x)) = _
  rw [show 424 = 278 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 28 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (424 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_424 :
    recurrence4Scalar2Exceptional.coeff 424 =
      ((((3591237517204011367018348660196944873049642 * 10 ^ 70 +
        5251677789558296350801569569312280105628354982485350313243056840836579) * 10 ^ 70 +
        0826961313374605803623779464684297426708827597898921921148499794956751) * 10 ^ 70 +
        1471292308949818080037309875501891925718904423920107111210090363430468) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (424 - x)) = _
  rw [show 425 = 279 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 27 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (425 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_425 :
    recurrence4Scalar2Exceptional.coeff 425 =
      -((((662008746318349524721839996686746058214504 * 10 ^ 70 +
        4556001665930618165211649798293198218643613222788881938434437419227756) * 10 ^ 70 +
        3721297680068514317933998735958203490202559655057276626573584763599568) * 10 ^ 70 +
        3889642650035528259432651359795685591568580797475581137834043137444300) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (425 - x)) = _
  rw [show 426 = 280 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (426 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_426 :
    recurrence4Scalar2Exceptional.coeff 426 =
      ((((99328148671512139554690490193738153117911 * 10 ^ 70 +
        0351979042338030636704728090835708039573827018450991051147644497213857) * 10 ^ 70 +
        6883550806069390387382793953457739561508270654662798962377221288851446) * 10 ^ 70 +
        3538247905406271786889467256343824813918300556249069309603379576363998) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (426 - x)) = _
  rw [show 427 = 281 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 25 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (427 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_427 :
    recurrence4Scalar2Exceptional.coeff 427 =
      -((((9019519518329607964770625204178863398550 * 10 ^ 70 +
        9743216616891496684318149706631072894225738177685711085189912975564698) * 10 ^ 70 +
        8391663326147321158745293659503886770772865006912312348729442425053532) * 10 ^ 70 +
        7841402853407462487258481700791074707044994923689252688932683371251842) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (427 - x)) = _
  rw [show 428 = 282 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 24 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (428 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_428 :
    recurrence4Scalar2Exceptional.coeff 428 =
      -((((939802673612669250765222156356687736153 * 10 ^ 70 +
        6305516929469715277031221135769078812628074730600689625717032733320819) * 10 ^ 70 +
        5066015041208365818470998227483691436436556722806952298055815891844010) * 10 ^ 70 +
        3500997750473571926016842424180278440844117577218236949822903106049056) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (428 - x)) = _
  rw [show 429 = 283 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (429 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_429 :
    recurrence4Scalar2Exceptional.coeff 429 =
      ((((748311048135036272421885064183746624400 * 10 ^ 70 +
        3016866740267970936502737671081480836333810211101418774506647250443979) * 10 ^ 70 +
        7971599386649503071546627074531485692840182605106855037415644376825685) * 10 ^ 70 +
        7292501980564599495690095049160795561153584476070059902631966448319310) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (429 - x)) = _
  rw [show 430 = 284 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 22 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (430 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_430 :
    recurrence4Scalar2Exceptional.coeff 430 =
      -((((237480025100723823788169302909421755529 * 10 ^ 70 +
        4125307435730475610883829151012001279456098845193993634602012695801409) * 10 ^ 70 +
        3613176443562163932990621418451250160410283978949430699233441016151108) * 10 ^ 70 +
        4646109268305436178210527866262047323787234252075749902492096006811558) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (430 - x)) = _
  rw [show 431 = 285 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 21 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (431 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_431 :
    recurrence4Scalar2Exceptional.coeff 431 =
      ((((55211147494965513039912065815104724817 * 10 ^ 70 +
        6735058553919496172027429407396293930098768190846941178221601114536677) * 10 ^ 70 +
        8014234611612716746921513778192879960318668089051432551197619342073192) * 10 ^ 70 +
        4756622117558228376143256933388959291143080014327264680308082617995071) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (431 - x)) = _
  rw [show 432 = 286 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 20 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (432 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_432 :
    recurrence4Scalar2Exceptional.coeff 432 =
      -((((10039927181505957620531235068635171818 * 10 ^ 70 +
        7454697471860650916156588286226150998175758585526956926306331136577535) * 10 ^ 70 +
        5661102649829089140810802645083617342543710585110350893224915012724858) * 10 ^ 70 +
        9184907998927155818009350664392992882888864336738813633623938733092709) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (432 - x)) = _
  rw [show 433 = 287 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 19 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (433 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_433 :
    recurrence4Scalar2Exceptional.coeff 433 =
      ((((1323658145261286223150180281568177645 * 10 ^ 70 +
        6475338865525184579836761835775805951569761249480814889449019044940983) * 10 ^ 70 +
        0901937366301815545689509580793914451604012188648521280539452755520679) * 10 ^ 70 +
        6685171815800409853837036639899306067143908713695963939495802297806817) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (433 - x)) = _
  rw [show 434 = 288 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 18 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (434 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_434 :
    recurrence4Scalar2Exceptional.coeff 434 =
      -((((66240619180047646000208785949538412 * 10 ^ 70 +
        3163803322894716333349818289956788973729447955997028739556136221123127) * 10 ^ 70 +
        5853538515109988732553639056757984186547125430206185805148382492883946) * 10 ^ 70 +
        2167264075970143773853977599312397078429699256687771472341753242314933) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (434 - x)) = _
  rw [show 435 = 289 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 17 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (435 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_435 :
    recurrence4Scalar2Exceptional.coeff 435 =
      -((((27661201289622204659511700536266523 * 10 ^ 70 +
        6289231482831465773667534001432615087626457494611279164675194483667021) * 10 ^ 70 +
        3471403838742016105748350953687959873962642327659190550459993049957782) * 10 ^ 70 +
        8618911864006520323204038661222730363050689539114540778191728294187332) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (435 - x)) = _
  rw [show 436 = 290 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 16 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (436 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_436 :
    recurrence4Scalar2Exceptional.coeff 436 =
      ((((11669650679969726875015556778005833 * 10 ^ 70 +
        9763754673371056134751828423773502871410202415566253551419973218127301) * 10 ^ 70 +
        6210146146120584115344666134023068415636591050414783628789608358882632) * 10 ^ 70 +
        3152366124513008041539749065602053379068821730185758134779372898368950) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (436 - x)) = _
  rw [show 437 = 291 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (437 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_437 :
    recurrence4Scalar2Exceptional.coeff 437 =
      -((((2846481246213139020116147263040332 * 10 ^ 70 +
        8964097770807154043018225478764009737295504039420878305119804001154110) * 10 ^ 70 +
        8285584534246816675525785449752111698734256693349157826740996228239588) * 10 ^ 70 +
        4853402136632183526046217453291935858709133297479092249970786092271630) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (437 - x)) = _
  rw [show 438 = 292 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 14 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (438 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_438 :
    recurrence4Scalar2Exceptional.coeff 438 =
      ((((518896115601312843514723480970962 * 10 ^ 70 +
        2319083510933624710361588184338063445194600260560138585899350980016941) * 10 ^ 70 +
        7544612143227655068759683761684088072245757092376006800452594312140483) * 10 ^ 70 +
        0718280753599521562802467559313506455143040173888582731891502054261431) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (438 - x)) = _
  rw [show 439 = 293 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 13 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (439 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_439 :
    recurrence4Scalar2Exceptional.coeff 439 =
      -((((71318285813326592014825082417068 * 10 ^ 70 +
        3843057952054983452250277012798965423499992459039017928299449051112978) * 10 ^ 70 +
        5513281954137805484606798206098890776615875592900771727877513544291462) * 10 ^ 70 +
        2075530485024433372407035698412639538455773471482604184854525825681060) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (439 - x)) = _
  rw [show 440 = 294 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 12 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (440 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_440 :
    recurrence4Scalar2Exceptional.coeff 440 =
      ((((6131268487203467831499603209850 * 10 ^ 70 +
        8791532637950186144005514706942551083243045886653460178762072047735958) * 10 ^ 70 +
        3734000190040303687458780169445358056306530035998657562514383675548604) * 10 ^ 70 +
        7495432025431717161656603755922959955178874646311869197541880308772999) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (440 - x)) = _
  rw [show 441 = 295 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 11 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (441 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_441 :
    recurrence4Scalar2Exceptional.coeff 441 =
      ((((169248700921809684812558998643 * 10 ^ 70 +
        7812907609986224171849898367455763621204599436505654420093134208720816) * 10 ^ 70 +
        4775020840144991109325198354923457443185909258195194912916747594251418) * 10 ^ 70 +
        9160409353222856764713756255943285901045460194432763539596675702665255) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (441 - x)) = _
  rw [show 442 = 296 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 10 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (442 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_442 :
    recurrence4Scalar2Exceptional.coeff 442 =
      -((((197930421971802113506766206942 * 10 ^ 70 +
        9549981364920782491507886224181166367715684019710288749459178181351578) * 10 ^ 70 +
        3733719809572368221691157538679325897837832330585934542376206693949099) * 10 ^ 70 +
        1268921663506192898503747159559097803379068649902639491967508416560444) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (442 - x)) = _
  rw [show 443 = 297 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 9 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (443 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_443 :
    recurrence4Scalar2Exceptional.coeff 443 =
      ((((47375862736804867864545459335 * 10 ^ 70 +
        0050393817623606611404583672518591429610095587292606375818748228737854) * 10 ^ 70 +
        4028296060224368695610426335786031341369127581257313835346107557326566) * 10 ^ 70 +
        4445678786162185941455498208564004663913235238027572441385760513012423) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (443 - x)) = _
  rw [show 444 = 298 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 8 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (444 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_444 :
    recurrence4Scalar2Exceptional.coeff 444 =
      -((((7480159186353506251803909938 * 10 ^ 70 +
        3801116315073014615289350490145340838386900495545441414804287611871993) * 10 ^ 70 +
        4843933600629037208072981563547771676855946339977603114346581338181414) * 10 ^ 70 +
        2178935633934781253023824141700343774030789829765474508587390929720576) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (444 - x)) = _
  rw [show 445 = 299 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 7 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (445 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_445 :
    recurrence4Scalar2Exceptional.coeff 445 =
      ((((820303733276522037035650670 * 10 ^ 70 +
        8214892119386217640936119127843410348758856972550892095678315756465327) * 10 ^ 70 +
        9402498093823920129063902834112060400696309838424428037325665377025500) * 10 ^ 70 +
        7934479616432387373622745908533230113957814353820103996738805067800479) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (445 - x)) = _
  rw [show 446 = 300 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 6 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (446 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_446 :
    recurrence4Scalar2Exceptional.coeff 446 =
      -((((45138559845705614874829795 * 10 ^ 70 +
        4566209459029576655294960337986110481921407261931453694996201290734613) * 10 ^ 70 +
        2020509772101868217507814660211927473977955107064101496218607264296519) * 10 ^ 70 +
        3065124303302217355564523568246316241216323103497938734807842989324610) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (446 - x)) = _
  rw [show 447 = 301 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 5 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (447 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_447 :
    recurrence4Scalar2Exceptional.coeff 447 =
      -((((4726264808572217054317550 * 10 ^ 70 +
        6507808748556783584910546621468110306381883660595001796601600050960808) * 10 ^ 70 +
        1766795141817151906259093452422273379271501992703956192574277725881950) * 10 ^ 70 +
        0309053713354793819020969808642803261122724558210331103804786135962291) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (447 - x)) = _
  rw [show 448 = 302 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 4 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (448 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_448 :
    recurrence4Scalar2Exceptional.coeff 448 =
      ((((1745658078472760416988151 * 10 ^ 70 +
        1580339921964880179321454693592760329893066142952752128595508763638642) * 10 ^ 70 +
        7448072645955786261318699944237720458540010841102541190098582671849192) * 10 ^ 70 +
        1518740982910287132674794816687256754885549634394941624313579182338070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (448 - x)) = _
  rw [show 449 = 303 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 3 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (449 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_449 :
    recurrence4Scalar2Exceptional.coeff 449 =
      -((((277927398161374379442868 * 10 ^ 70 +
        3824519569121388993614336525534427281626817006669683594794706637145869) * 10 ^ 70 +
        5610090072503033540093841930365750251807590183404255435128364821970300) * 10 ^ 70 +
        0629099340117392767206779709506025603790809954877103317535561174181860) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (449 - x)) = _
  rw [show 450 = 304 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 2 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
