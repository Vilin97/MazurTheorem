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

private theorem recurrence4Scalar2Exceptional_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (478 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_478 :
    recurrence4Scalar2Exceptional.coeff 478 =
      (((3700104007976587403162289332514175894414601199828615895649 * 10 ^ 70 +
        7664168226947464425104604683024126145448951992886451121442792079772025) * 10 ^ 70 +
        7980069573165569996536042781680063399307449247148179148248960622421524) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (478 - x)) = _
  rw [show 479 = 333 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 5 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (479 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_479 :
    recurrence4Scalar2Exceptional.coeff 479 =
      (((187795939698423271368133467800132167984175340348209797902 * 10 ^ 70 +
        8620208060561975298100660811225124238622971521671744320475539691836181) * 10 ^ 70 +
        5250933974722235598473510900110269418390521581264627128001507147811236) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (479 - x)) = _
  rw [show 480 = 334 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 4 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (480 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_480 :
    recurrence4Scalar2Exceptional.coeff 480 =
      (((3940952815331820245159083216226140733306885791246516143 * 10 ^ 70 +
        3920172913250871242919656934540610547201869283386463910377431983738256) * 10 ^ 70 +
        9945013056318272905930159399172943663545144672757476106921908978705947) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (480 - x)) = _
  rw [show 481 = 335 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 3 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (481 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_481 :
    recurrence4Scalar2Exceptional.coeff 481 =
      (((52205562230586854348993749165377108583621494053663439 * 10 ^ 70 +
        8156881604145512177727156516612444520313618010956273805489645427961470) * 10 ^ 70 +
        1038920531479687119255042922201359051560891166776925737254014860179042) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (481 - x)) = _
  rw [show 482 = 336 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 2 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (482 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_482 :
    recurrence4Scalar2Exceptional.coeff 482 =
      (((482274361289914300270959672796185300704893084172091 * 10 ^ 70 +
        8790288873594275456881593022708492145357734855070159185021090037817704) * 10 ^ 70 +
        1010175001583247430480998184148609869941029625212655593934253739997747) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (482 - x)) = _
  rw [show 483 = 337 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 1 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (483 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_483 :
    recurrence4Scalar2Exceptional.coeff 483 =
      (((3205502472787648406817642472868867605917416852513 * 10 ^ 70 +
        1255952950855199585764971697166836499346762039400909149779918812676117) * 10 ^ 70 +
        2999579360534726339004465339246118846240726367701827049914044220303316) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (483 - x)) = _
  rw [show 484 = 338 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (484 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_484 :
    recurrence4Scalar2Exceptional.coeff 484 =
      (((15229717517413733342166038789464879419730321887 * 10 ^ 70 +
        2303180700679467332005337112860903491484212730199164236149112465055462) * 10 ^ 70 +
        0783838847610022727753572176148874284983016523442584458136358515717279) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (484 - x)) = _
  rw [show 485 = 339 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 31 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (485 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_485 :
    recurrence4Scalar2Exceptional.coeff 485 =
      (((48717797521415440783411879190641751043170778 * 10 ^ 70 +
        9262849393540865772854067258252185716369404775625903617858043722138358) * 10 ^ 70 +
        0960342220793856481409364708410118452290314400351681843431318306393391) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (485 - x)) = _
  rw [show 486 = 340 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 30 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (486 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_486 :
    recurrence4Scalar2Exceptional.coeff 486 =
      (((81015681900430381409152198222791822300668 * 10 ^ 70 +
        1391125331924889528158734268832486652449775751937734217399803810819907) * 10 ^ 70 +
        7390289218057278706023592673066363776874933414380256387574905153324759) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (486 - x)) = _
  rw [show 487 = 341 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 29 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (487 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_487 :
    recurrence4Scalar2Exceptional.coeff 487 =
      -(((83486965873656452391848860488288239837 * 10 ^ 70 +
        7937243828257480572498676013340203485543183914091128780008101144994519) * 10 ^ 70 +
        2509266986387132742521634759822153308762305941886764952438475103873584) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (487 - x)) = _
  rw [show 488 = 342 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 28 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (488 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_488 :
    recurrence4Scalar2Exceptional.coeff 488 =
      -(((895234397739870999879757038425953777 * 10 ^ 70 +
        7909535175289065931360376386760481415837374401660317896520979948641188) * 10 ^ 70 +
        5901954198780199959409492139506000743361303289247719272827115040052681) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (488 - x)) = _
  rw [show 489 = 343 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 27 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (489 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_489 :
    recurrence4Scalar2Exceptional.coeff 489 =
      -(((2353375725216896066535339898822551 * 10 ^ 70 +
        5751173060130620272044950762126380422876020973394367532150033193468545) * 10 ^ 70 +
        5932182292946389625588615068959617067828243444875407916819788683132106) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (489 - x)) = _
  rw [show 490 = 344 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 26 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (490 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_490 :
    recurrence4Scalar2Exceptional.coeff 490 =
      -(((2158204655384406585968350924644 * 10 ^ 70 +
        5330166034663474191735012138751761526458091275132687999509221602330906) * 10 ^ 70 +
        7797283180350414201687258300385493052561839895138144613305853128701634) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (490 - x)) = _
  rw [show 491 = 345 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 25 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (491 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_491 :
    recurrence4Scalar2Exceptional.coeff 491 =
      (((4155988359667983651302624229 * 10 ^ 70 +
        9327801884298354641342784138451854695144295897426127699000315603485105) * 10 ^ 70 +
        8457411957122135617760269164201305206041483143210754271058517969458625) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (491 - x)) = _
  rw [show 492 = 346 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 24 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (492 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_492 :
    recurrence4Scalar2Exceptional.coeff 492 =
      (((16122313938381690012051114 * 10 ^ 70 +
        7799950801803917176293952061406721586666394660627223185821497973433434) * 10 ^ 70 +
        3302824501911069784986134074786493083845367389402222303422562721407767) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (492 - x)) = _
  rw [show 493 = 347 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 23 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (493 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_493 :
    recurrence4Scalar2Exceptional.coeff 493 =
      (((20679462089242362071853 * 10 ^ 70 +
        2237749373569195876203406275226677395447560495796236956925570837183743) * 10 ^ 70 +
        0658052944348515576683890959253518488619840070605046319167649944059436) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (493 - x)) = _
  rw [show 494 = 348 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 22 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (494 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_494 :
    recurrence4Scalar2Exceptional.coeff 494 =
      (((3003192581880532401 * 10 ^ 70 +
        4360647949462903116683503286030461690190245707552904434322994611528966) * 10 ^ 70 +
        9244577705606871405975678092096749009848719461448885337546534421662012) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (494 - x)) = _
  rw [show 495 = 349 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 21 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (495 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_495 :
    recurrence4Scalar2Exceptional.coeff 495 =
      -(((29219318098292994 * 10 ^ 70 +
        9179459753321804663727488103467728967089149247883586248553202708675855) * 10 ^ 70 +
        7685389136821775341892588196349268481131875646706339841860524557348227) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (495 - x)) = _
  rw [show 496 = 350 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 20 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (496 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_496 :
    recurrence4Scalar2Exceptional.coeff 496 =
      -(((48431306376437 * 10 ^ 70 +
        2283769290573312152668479785546733720000127347561927948426983843218091) * 10 ^ 70 +
        1092067608987915176577828771211707783839254153332594583940364926006716) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (496 - x)) = _
  rw [show 497 = 351 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 19 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (497 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_497 :
    recurrence4Scalar2Exceptional.coeff 497 =
      -(((41406852700 * 10 ^ 70 +
        7241017889814287103774173346528444627671859666299124785780666173538285) * 10 ^ 70 +
        3238736330354254586777545749954306947221995301507089641117893088935700) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (497 - x)) = _
  rw [show 498 = 352 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 18 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (498 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_498 :
    recurrence4Scalar2Exceptional.coeff 498 =
      -(((22049789 * 10 ^ 70 +
        7134523172812476720251767135305799904998334709268414952991047087384993) * 10 ^ 70 +
        4252205652643652074330086297922120741095783282180521970933866498755932) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (498 - x)) = _
  rw [show 499 = 353 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 17 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (499 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_499 :
    recurrence4Scalar2Exceptional.coeff 499 =
      -(((7635 * 10 ^ 70 +
        8516995789679819980715514692341580812293876142135128038364709210703216) * 10 ^ 70 +
        8625749437456804252331162242010824284765882892518849306421363516407942) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (499 - x)) = _
  rw [show 500 = 354 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 16 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (500 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_500 :
    recurrence4Scalar2Exceptional.coeff 500 =
      -(((1 * 10 ^ 70 +
        7311927657638091806818494925863663915155193099909672026660627333181818) * 10 ^ 70 +
        1730128324005727888879697912067281746217127654743920334127339565982672) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (500 - x)) = _
  rw [show 501 = 355 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 15 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (501 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_501 :
    recurrence4Scalar2Exceptional.coeff 501 =
      -((2547575562973483269854063268819670455043806199886436714623584221685 * 10 ^ 70 +
        5611960015918314511381012211893756178984962954872819148354700639196198) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (501 - x)) = _
  rw [show 502 = 356 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 14 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (502 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_502 :
    recurrence4Scalar2Exceptional.coeff 502 =
      -((239039636525752956814950955449619776703455351773247987839363784 * 10 ^ 70 +
        6577467902512553560227785583556241546857343224048882520706369841665656) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (502 - x)) = _
  rw [show 503 = 357 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 13 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (503 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_503 :
    recurrence4Scalar2Exceptional.coeff 503 =
      -((13948249938802240823789802690710724469862692616781879775832 * 10 ^ 70 +
        6315981040083865937379362546911224886707650459846415162353144480023696) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (503 - x)) = _
  rw [show 504 = 358 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 12 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (504 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_504 :
    recurrence4Scalar2Exceptional.coeff 504 =
      -((491205909133784099876717764838648659050237784973283512 * 10 ^ 70 +
        0951109060622897635564740062507891354582163252664740619823239343254640) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (504 - x)) = _
  rw [show 505 = 359 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 11 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (505 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_505 :
    recurrence4Scalar2Exceptional.coeff 505 =
      -((10156209983676335293191339120868784072970031295017 * 10 ^ 70 +
        1140303748912650417898970852008446531463567884939903995214317013351033) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (505 - x)) = _
  rw [show 506 = 360 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 10 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (506 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_506 :
    recurrence4Scalar2Exceptional.coeff 506 =
      -((117982370022623698058226463122888927663067836 * 10 ^ 70 +
        7810044808561737680640290000986836329418694648091502541776206329062003) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (506 - x)) = _
  rw [show 507 = 361 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 9 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (507 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_507 :
    recurrence4Scalar2Exceptional.coeff 507 =
      -((719840172583233609660549940119554138033 * 10 ^ 70 +
        5984716672167844580940126578627406442033105250780833449292717146451804) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (507 - x)) = _
  rw [show 508 = 362 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 8 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (508 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_508 :
    recurrence4Scalar2Exceptional.coeff 508 =
      -((2231533975049811042106771452679688 * 10 ^ 70 +
        8565927105164372549662364511961454959501078854358331065549703947397611) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (508 - x)) = _
  rw [show 509 = 363 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 7 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
