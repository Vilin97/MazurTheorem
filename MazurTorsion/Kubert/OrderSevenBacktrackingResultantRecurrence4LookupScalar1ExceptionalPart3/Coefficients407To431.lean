/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27

attribute [local simp]
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91

attribute [local simp]
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
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
  recurrence4ExceptionalProduct_coeff_282
  recurrence4ExceptionalProduct_coeff_283
  recurrence4ExceptionalProduct_coeff_284
  recurrence4ExceptionalProduct_coeff_285
  recurrence4ExceptionalProduct_coeff_286
  recurrence4ExceptionalProduct_coeff_287
  recurrence4ExceptionalProduct_coeff_288
  recurrence4ExceptionalProduct_coeff_289

attribute [local simp]
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
  recurrence4ExceptionalProduct_coeff_346
  recurrence4ExceptionalProduct_coeff_347
  recurrence4ExceptionalProduct_coeff_348
  recurrence4ExceptionalProduct_coeff_349
  recurrence4ExceptionalProduct_coeff_350
  recurrence4ExceptionalProduct_coeff_351
  recurrence4ExceptionalProduct_coeff_352
  recurrence4ExceptionalProduct_coeff_353

attribute [local simp]
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

private theorem recurrence4Scalar1Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (407 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (407 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_407 :
    recurrence4Scalar1Exceptional.coeff 407 =
      -((((4179776903337181702899687736177177798966855152737254 * 10 ^ 70 +
        0638398796394668250399716755638319235774369502405503850132894116792351) * 10 ^ 70 +
        2039628452474701959103291629389184857854397907585447908433951720213124) * 10 ^ 70 +
        0702342889974024151077458534035498412730767417015969322097405240907841) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (407 - x)) = _
  rw [show 408 = 258 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 16 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (408 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (408 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_408 :
    recurrence4Scalar1Exceptional.coeff 408 =
      ((((37871499151891776977905094566426317137059541136776991 * 10 ^ 70 +
        4818968247920960946700007606613910537705260982827420906058664157979399) * 10 ^ 70 +
        6413115590385753201611668660741031689524972205850070457632561210925171) * 10 ^ 70 +
        3962133598938730895850357709324129190339460013746083679148175455858972) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (408 - x)) = _
  rw [show 409 = 259 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 15 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (409 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (409 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_409 :
    recurrence4Scalar1Exceptional.coeff 409 =
      -((((22058724044786003272289880707200707343801787412166213 * 10 ^ 70 +
        3600861783489982435501699375266951401391894598530287945837354318882780) * 10 ^ 70 +
        5654631029032371543325413404837870975233517797902947211066747596852127) * 10 ^ 70 +
        5713164609468596689496764159233327305762435846400731282112473899874128) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (409 - x)) = _
  rw [show 410 = 260 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 14 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (410 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (410 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_410 :
    recurrence4Scalar1Exceptional.coeff 410 =
      ((((9499481198093857512162872527717470594622239728687209 * 10 ^ 70 +
        8555217875176420480594139041210337841539285258989100125455201396555317) * 10 ^ 70 +
        2440002359365833603463033680637983698228559728010800450811210848500887) * 10 ^ 70 +
        3349235007369676042920837986812197941624153654978250425502983987294244) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (410 - x)) = _
  rw [show 411 = 261 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 13 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (411 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (411 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_411 :
    recurrence4Scalar1Exceptional.coeff 411 =
      -((((3555202290760719948121732477398667450923584532280199 * 10 ^ 70 +
        6879018505742760846404601204124100612166784534491344325282736625464211) * 10 ^ 70 +
        5439763641207606908428993835590115362943884267712189912398358691357771) * 10 ^ 70 +
        7693201676977849928896273262228747240298843273539974791287913529407755) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (411 - x)) = _
  rw [show 412 = 262 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 12 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (412 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (412 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_412 :
    recurrence4Scalar1Exceptional.coeff 412 =
      ((((1215362965045628626595877710052963455947711583489689 * 10 ^ 70 +
        4843867028536757921468504880171073127097041146901099030939763921623192) * 10 ^ 70 +
        0263269930117468657871018427623719586824275211491491209825618540712476) * 10 ^ 70 +
        0891456836488287669706494288098345912974513574946758999803616676502408) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (412 - x)) = _
  rw [show 413 = 263 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 11 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (413 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (413 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_413 :
    recurrence4Scalar1Exceptional.coeff 413 =
      -((((386588626477770282663688183652080768449740360399103 * 10 ^ 70 +
        4044561221180753097027865002424074047210327007762438778215775632720617) * 10 ^ 70 +
        1915759691505847582740839701049538534325801380075490869734056747992888) * 10 ^ 70 +
        7841361821798241375238126848307540644522395216460719167671896220411831) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (413 - x)) = _
  rw [show 414 = 264 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 10 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (414 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (414 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_414 :
    recurrence4Scalar1Exceptional.coeff 414 =
      ((((114788289795616172326411093604011614578172901459461 * 10 ^ 70 +
        9146792576820886232691674126681434599941758811378699611194236083782534) * 10 ^ 70 +
        1849695129147619717303282515378300831340841221562362551224783040927675) * 10 ^ 70 +
        6368225077532317216961075777952417925007579353122887266415124135524031) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (414 - x)) = _
  rw [show 415 = 265 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 9 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (415 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (415 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_415 :
    recurrence4Scalar1Exceptional.coeff 415 =
      -((((31528693946067047190696998021302818699176193223555 * 10 ^ 70 +
        5000354625947778970026392979273739818975396932442926318372443305241933) * 10 ^ 70 +
        6947160449213154548921728908937326508111728458272497658670786073530870) * 10 ^ 70 +
        6486758462119539999853097443911218799780759234651149194985182679235362) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (415 - x)) = _
  rw [show 416 = 266 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 8 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (416 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (416 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_416 :
    recurrence4Scalar1Exceptional.coeff 416 =
      ((((7805210377499584586390186137753569331036170224619 * 10 ^ 70 +
        3856383241385114889108912616496523418661248584637440208418013867080877) * 10 ^ 70 +
        0876878610463118713394659152581889653397201485806672698164206267951051) * 10 ^ 70 +
        2207036496325196306743510192458136430992000071902619242164017158552581) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (416 - x)) = _
  rw [show 417 = 267 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 7 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (417 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (417 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_417 :
    recurrence4Scalar1Exceptional.coeff 417 =
      -((((1632201825788427607824254270402302180829874554758 * 10 ^ 70 +
        0566901357288232783344295473301311298648675310342336543173914780644549) * 10 ^ 70 +
        4674429646473234301545034675877668825626140905346485783455632754397762) * 10 ^ 70 +
        0712239906903364960312593074644372744229601600374198795165582770832368) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (417 - x)) = _
  rw [show 418 = 268 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 6 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (418 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (418 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_418 :
    recurrence4Scalar1Exceptional.coeff 418 =
      ((((229646858464208855609991224993346665936907028626 * 10 ^ 70 +
        7546846129076486959879065860698537914063192304301318512132638644494638) * 10 ^ 70 +
        3050021171216691577596836312448333705503114305960115861365105161956043) * 10 ^ 70 +
        1613774138724940955514183121177709300397046378461052681464571543857108) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (418 - x)) = _
  rw [show 419 = 269 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 5 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (419 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (419 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_419 :
    recurrence4Scalar1Exceptional.coeff 419 =
      ((((14906166062752847575398375007883590548500056834 * 10 ^ 70 +
        8826859386858396717427816855048824391760874412104125686375367805783652) * 10 ^ 70 +
        5506454149001280341316102509756533649302122509089267669248613376164433) * 10 ^ 70 +
        8267869514286672553165543986196175649093912180204719222221352208411704) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (419 - x)) = _
  rw [show 420 = 270 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 4 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (420 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (420 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_420 :
    recurrence4Scalar1Exceptional.coeff 420 =
      -((((28107570704229070251893648358544559368987238029 * 10 ^ 70 +
        1076402479061813761727435849921310900778855375871550261222667076714482) * 10 ^ 70 +
        5924554104074179455624809299977167190428227915511858509233192546900631) * 10 ^ 70 +
        4368220485589245083056599440908834935182698247889122413074368917810110) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (420 - x)) = _
  rw [show 421 = 271 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 3 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (421 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (421 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_421 :
    recurrence4Scalar1Exceptional.coeff 421 =
      ((((14055267887484909216365329410843879903000708225 * 10 ^ 70 +
        0384916899455587674903016437100054536117711510201331677368560325005810) * 10 ^ 70 +
        6143810873541117935252601780806304069995098887988803116580468116026112) * 10 ^ 70 +
        2648032871868934476524818899177807139655029266107368506034887766117141) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (421 - x)) = _
  rw [show 422 = 272 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 2 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (422 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (422 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_422 :
    recurrence4Scalar1Exceptional.coeff 422 =
      -((((5215455011020100220672632992726546026742592391 * 10 ^ 70 +
        2902117155863427170870019169634361170508026603391503595385763058522267) * 10 ^ 70 +
        2860890760370183838739575221806796568273604127486665992058047566642860) * 10 ^ 70 +
        9728689015996283575842542812983654364491402835820138085397881421532797) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (422 - x)) = _
  rw [show 423 = 273 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 1 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (423 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (423 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_423 :
    recurrence4Scalar1Exceptional.coeff 423 =
      ((((1620487035659883952558393865969755804595405109 * 10 ^ 70 +
        2029955013248110016505174759634443352658090798721802300856187044862154) * 10 ^ 70 +
        4894309499872207544987048573903232917152729291734935823782887015128282) * 10 ^ 70 +
        5979078042043379548741514147410060918705378931373767592040533685075504) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (423 - x)) = _
  rw [show 424 = 274 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (424 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (424 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_424 :
    recurrence4Scalar1Exceptional.coeff 424 =
      -((((433000701326570192726873723914192079348548012 * 10 ^ 70 +
        5350937451420036566858083798349680262480266476982753003077593789846799) * 10 ^ 70 +
        3219273113246443600784676904675051823732086366155628337800856936917273) * 10 ^ 70 +
        6204429098690189123879115250918411157078574724803297521729794244292694) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (424 - x)) = _
  rw [show 425 = 275 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 31 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (425 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (425 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_425 :
    recurrence4Scalar1Exceptional.coeff 425 =
      ((((98130426631790425371349657990438266643500166 * 10 ^ 70 +
        7210874139996085115985762916617276156028475217020490607292848796944918) * 10 ^ 70 +
        3107838649581777583792446253737831228319215871517578074653817384640357) * 10 ^ 70 +
        8930272626975819239016132542850503208796442190271886980097916273573770) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (425 - x)) = _
  rw [show 426 = 276 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 30 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (426 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (426 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_426 :
    recurrence4Scalar1Exceptional.coeff 426 =
      -((((17544280522269874746959822564310548520646990 * 10 ^ 70 +
        2343732795418728105501824513982762773719542526922321004446901356679101) * 10 ^ 70 +
        3664425409505030006123740021893242929929522231388612587250162486852776) * 10 ^ 70 +
        3175857075796055973603061842823203447804106623976700543212643703155305) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (426 - x)) = _
  rw [show 427 = 277 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 29 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (427 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (427 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_427 :
    recurrence4Scalar1Exceptional.coeff 427 =
      ((((1760476512681980908293505311713157595739720 * 10 ^ 70 +
        2868988006355432930506852340916067643745077167282394925612844553623586) * 10 ^ 70 +
        6369948803113774121454766780443518629435269023072531397016317457729306) * 10 ^ 70 +
        6551849481130553706259791648932789144041460562239035802282274473541042) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (427 - x)) = _
  rw [show 428 = 278 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 28 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (428 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (428 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_428 :
    recurrence4Scalar1Exceptional.coeff 428 =
      ((((311998602660962835503679879038921544757811 * 10 ^ 70 +
        7512346708922026827807464230366377187478955961780880247626506705185660) * 10 ^ 70 +
        6142432817921943534430534334586289032775121171608373509438720612092155) * 10 ^ 70 +
        2648736066374528466364205153205740071808704199947561071118351764596562) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (428 - x)) = _
  rw [show 429 = 279 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 27 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (429 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (429 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_429 :
    recurrence4Scalar1Exceptional.coeff 429 =
      -((((250055658455685951887203719413842516817311 * 10 ^ 70 +
        1031550544501815631229484513135813590714215776340932849763075571802896) * 10 ^ 70 +
        2233773431770387207511727104379982108111607150772632620743043074190345) * 10 ^ 70 +
        4171107440598502280681865001319594685664410633332621066605118679663406) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (429 - x)) = _
  rw [show 430 = 280 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 26 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (430 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (430 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_430 :
    recurrence4Scalar1Exceptional.coeff 430 =
      ((((92149887619617942403256440563558603520164 * 10 ^ 70 +
        3908953291948387253960676938777134763285361457997750401447816234750425) * 10 ^ 70 +
        1494537025853793570481591050280878069069485194363905957428937221261920) * 10 ^ 70 +
        6351332549742689864185775993376137323801839026911935691386211704227386) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (430 - x)) = _
  rw [show 431 = 281 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 25 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (431 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (431 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_431 :
    recurrence4Scalar1Exceptional.coeff 431 =
      -((((25619076018575652042899269163330090715828 * 10 ^ 70 +
        8226019942446012644856702714957669068723016543213235982387533555950427) * 10 ^ 70 +
        6580544263557858886188131283426992198090605277561276493205740693196049) * 10 ^ 70 +
        4424441472051443059784493935872641349809268304659275089055278219046847) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (431 - x)) = _
  rw [show 432 = 282 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 24 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
