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

private theorem recurrence4Scalar1Exceptional_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (485 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (485 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_485 :
    recurrence4Scalar1Exceptional.coeff 485 =
      (((27187968953627444223152573569572420122568063980747766 * 10 ^ 70 +
        5905136508453575757490819927496318015208155636388796174017787747161477) * 10 ^ 70 +
        5225676051704165008285948876762313457716753854924554771617443502994044) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (485 - x)) = _
  rw [show 486 = 336 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 2 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (486 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (486 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_486 :
    recurrence4Scalar1Exceptional.coeff 486 =
      (((240755074531439446965310236854693306256644850626543 * 10 ^ 70 +
        5608290531719289992432533024835455012706907437626573342317944435588614) * 10 ^ 70 +
        6460736695831188149551570819552318599371015379198782848230547954378314) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (486 - x)) = _
  rw [show 487 = 337 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 1 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (487 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (487 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_487 :
    recurrence4Scalar1Exceptional.coeff 487 =
      (((1541351404048283121527118032443867301144779852343 * 10 ^ 70 +
        8166142141385985732267928472384396206089829621700018170417274187387658) * 10 ^ 70 +
        2467271307478840118530285207902734518002097769905287245651500313324309) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (487 - x)) = _
  rw [show 488 = 338 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (488 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (488 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_488 :
    recurrence4Scalar1Exceptional.coeff 488 =
      (((7052193786184947062440606805634473979258347742 * 10 ^ 70 +
        4937028591276762527160408556683390616041131415393051508069417352623368) * 10 ^ 70 +
        8821954031192548041518310112434569340001407881700490557577496040477408) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (488 - x)) = _
  rw [show 489 = 339 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 31 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (489 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (489 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_489 :
    recurrence4Scalar1Exceptional.coeff 489 =
      (((21527082623454426325753588628138865183415668 * 10 ^ 70 +
        7628310142049445199890245756986300926794126813917114769721237130907947) * 10 ^ 70 +
        0812923752057928296591707806027666706101121958565647990259982478381643) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (489 - x)) = _
  rw [show 490 = 340 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 30 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (490 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (490 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_490 :
    recurrence4Scalar1Exceptional.coeff 490 =
      (((32216482565032211172939792304105410073034 * 10 ^ 70 +
        1911619588559341222509442762896801468145970034055150388431410297218767) * 10 ^ 70 +
        1958365694451720576576371297877992185384053964269398291758904109457610) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (490 - x)) = _
  rw [show 491 = 341 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 29 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (491 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (491 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_491 :
    recurrence4Scalar1Exceptional.coeff 491 =
      -(((50494670848919734936943857332063033211 * 10 ^ 70 +
        3607165084757063449696303411523925357989688767054543019985655727820316) * 10 ^ 70 +
        5828247915353020129584730414162885347276064742066268125536382650443862) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (491 - x)) = _
  rw [show 492 = 342 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 28 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (492 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (492 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_492 :
    recurrence4Scalar1Exceptional.coeff 492 =
      -(((413086113675693471732150534407229610 * 10 ^ 70 +
        7274155265708701865095359345872731826350294673549693338723255664727918) * 10 ^ 70 +
        0757450187287597138897000407073667519447686502426017557825885810593168) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (492 - x)) = _
  rw [show 493 = 343 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 27 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (493 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (493 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_493 :
    recurrence4Scalar1Exceptional.coeff 493 =
      -(((1004977720854509949826324601814341 * 10 ^ 70 +
        9326090735770029768943336668354191613781423880685607317855051342352533) * 10 ^ 70 +
        7223504492271179404244209442784677859868904055830350768627935533077595) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (493 - x)) = _
  rw [show 494 = 344 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 26 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (494 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (494 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_494 :
    recurrence4Scalar1Exceptional.coeff 494 =
      -(((777005247554678474934625686294 * 10 ^ 70 +
        8302091229313092135295700943293423043379381454113005398976042265414048) * 10 ^ 70 +
        4883172309658176261921001848450028087267883865326161482288750689620533) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (494 - x)) = _
  rw [show 495 = 345 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 25 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (495 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (495 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_495 :
    recurrence4Scalar1Exceptional.coeff 495 =
      (((2077598761867885242197160992 * 10 ^ 70 +
        1530073683414790412457504308106874271336443067374594463988139282770027) * 10 ^ 70 +
        8744813183370935829032456866242316225992024191242220584228521984619298) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (495 - x)) = _
  rw [show 496 = 346 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 24 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (496 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (496 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_496 :
    recurrence4Scalar1Exceptional.coeff 496 =
      (((6990527602315234363812674 * 10 ^ 70 +
        9495825261890558850168608190476978128786755951929665927231806847444251) * 10 ^ 70 +
        6279901520097627933987810221753343164183654107639422242809311220835612) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (496 - x)) = _
  rw [show 497 = 347 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 23 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (497 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (497 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_497 :
    recurrence4Scalar1Exceptional.coeff 497 =
      (((8236069363469570462612 * 10 ^ 70 +
        2496838704996183382493989033229184623313254181489035492834396145079479) * 10 ^ 70 +
        0498760473909041829273851348344545267350155457397169022476582145368250) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (497 - x)) = _
  rw [show 498 = 348 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 22 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (498 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (498 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_498 :
    recurrence4Scalar1Exceptional.coeff 498 =
      (((182295829531068640 * 10 ^ 70 +
        1226613352072457971330335172722011220287528150662886758716073062417904) * 10 ^ 70 +
        4237282099589638849767835489938385707336970986331900650928528856197426) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (498 - x)) = _
  rw [show 499 = 349 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 21 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (499 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (499 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_499 :
    recurrence4Scalar1Exceptional.coeff 499 =
      -(((13022683892161728 * 10 ^ 70 +
        4221127560277218785709340217264950809575763065432801590926684640216559) * 10 ^ 70 +
        5810300660910590937049010074168646708336144383815102749213107198283803) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (499 - x)) = _
  rw [show 500 = 350 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 20 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (500 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (500 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_500 :
    recurrence4Scalar1Exceptional.coeff 500 =
      -(((20004262161907 * 10 ^ 70 +
        2900499548199670581410852817094641975346312818985216875359486484379858) * 10 ^ 70 +
        3763330316657124060609451897092832910287277496705520026202364855012637) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (500 - x)) = _
  rw [show 501 = 351 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 19 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (501 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (501 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_501 :
    recurrence4Scalar1Exceptional.coeff 501 =
      -(((16361716441 * 10 ^ 70 +
        4739234462527237199365301810525359155564791273510731011981589175604820) * 10 ^ 70 +
        8197368743682355547778479588435586800825253619785567922346752297622793) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (501 - x)) = _
  rw [show 502 = 352 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 18 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (502 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (502 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_502 :
    recurrence4Scalar1Exceptional.coeff 502 =
      -(((8388643 * 10 ^ 70 +
        2581234468965957586400792723397635868812389400440769936594706799057583) * 10 ^ 70 +
        0843863464504985145140145499226460320049879299584920519915439170480554) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (502 - x)) = _
  rw [show 503 = 353 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 17 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (503 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (503 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_503 :
    recurrence4Scalar1Exceptional.coeff 503 =
      -(((2799 * 10 ^ 70 +
        6079143778576366052722778304249361322256942719530062313826294782017586) * 10 ^ 70 +
        4468783802922050229408962859595161289218288401169693787775302570393003) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (503 - x)) = _
  rw [show 504 = 354 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 16 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (504 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (504 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_504 :
    recurrence4Scalar1Exceptional.coeff 504 =
      -((6109193959875492613217762191327105719816050549190561136871640373188092 * 10 ^ 70 +
        6106556521441313543609267624560287155663760534341735567316053918198285) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (504 - x)) = _
  rw [show 505 = 355 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 15 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (505 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (505 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_505 :
    recurrence4Scalar1Exceptional.coeff 505 =
      -((863338868337357292475927918374825849054006949194948128604447748018 * 10 ^ 70 +
        0521070065923223262512031336587193787063404809310199835794619890340794) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (505 - x)) = _
  rw [show 506 = 356 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 14 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (506 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (506 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_506 :
    recurrence4Scalar1Exceptional.coeff 506 =
      -((77602786403100490945174840057444589387398187416328328022261666 * 10 ^ 70 +
        7806704759803378703882722836285033022276501742672910874229310664333172) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (506 - x)) = _
  rw [show 507 = 357 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 13 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (507 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (507 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_507 :
    recurrence4Scalar1Exceptional.coeff 507 =
      -((4322518835459384159700204986761387825032459972649549810066 * 10 ^ 70 +
        6981359555666194155545769348363771676414813663242397996029795128510784) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (507 - x)) = _
  rw [show 508 = 358 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 12 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (508 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (508 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_508 :
    recurrence4Scalar1Exceptional.coeff 508 =
      -((144503823728056919378650079468546482732575531222641160 * 10 ^ 70 +
        4561032415874467445003105222849956155965997080022800352214250810875515) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (508 - x)) = _
  rw [show 509 = 359 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 11 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (509 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (509 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_509 :
    recurrence4Scalar1Exceptional.coeff 509 =
      -((2820709068956917334074195430984676809012815266731 * 10 ^ 70 +
        1948456508759938494618995930089800432157543577425249331192981165325925) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (509 - x)) = _
  rw [show 510 = 360 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 10 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_509_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (510 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (510 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_510 :
    recurrence4Scalar1Exceptional.coeff 510 =
      -((30800353397030362031170255000043524407004655 * 10 ^ 70 +
        2686827164956846414725643805630626682674296491979401404858709298222416) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (510 - x)) = _
  rw [show 511 = 361 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 9 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_510_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (511 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (511 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_511 :
    recurrence4Scalar1Exceptional.coeff 511 =
      -((175895633707345746905372989650870272753 * 10 ^ 70 +
        8376086258387496535536079165034235073800945558094680878147946099306650) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (511 - x)) = _
  rw [show 512 = 362 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 8 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_511_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (512 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (512 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_512 :
    recurrence4Scalar1Exceptional.coeff 512 =
      -((502328471793129300987077794232758 * 10 ^ 70 +
        7548221748685469362570094423716559747201199484216595596187644876685931) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (512 - x)) = _
  rw [show 513 = 363 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 7 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 364,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (513 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (513 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_513 :
    recurrence4Scalar1Exceptional.coeff 513 =
      -((662685707319367918171916930 * 10 ^ 70 +
        0119008155598713598057211780087610073542258076228772771250407486983938) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (513 - x)) = _
  rw [show 514 = 364 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 6 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
