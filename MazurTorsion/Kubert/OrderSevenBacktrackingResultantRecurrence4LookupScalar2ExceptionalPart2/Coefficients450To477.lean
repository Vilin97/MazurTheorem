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

private theorem recurrence4Scalar2Exceptional_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (450 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_450 :
    recurrence4Scalar2Exceptional.coeff 450 =
      ((((28314147841209632009102 * 10 ^ 70 +
        1986520005985919458389779400292650625368168031705825365078808030466761) * 10 ^ 70 +
        4329173552996007995696733831313683421961149035851312305423497469938316) * 10 ^ 70 +
        1785724174495463489016217897543200654798357250465753920911266328187533) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (450 - x)) = _
  rw [show 451 = 305 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 1 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (451 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_451 :
    recurrence4Scalar2Exceptional.coeff 451 =
      -((((1503893266684341152797 * 10 ^ 70 +
        7756642597658637568331951676769236636916266656245237623634120124446719) * 10 ^ 70 +
        1385925518049440196763348721567357577226549263541121207325559971967828) * 10 ^ 70 +
        5449999450598550675043979451510049753939509168820184596410819263062984) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (451 - x)) = _
  rw [show 452 = 306 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (452 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_452 :
    recurrence4Scalar2Exceptional.coeff 452 =
      -((((79987386467794273986 * 10 ^ 70 +
        9228989459270151050969457563342986813705442859085166981030401824198803) * 10 ^ 70 +
        9281436895131984449616267086502000332097588192296009663519532178117390) * 10 ^ 70 +
        6240193243223786689631403354545705372892615224376977523126065756906672) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (452 - x)) = _
  rw [show 453 = 307 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 31 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (453 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_453 :
    recurrence4Scalar2Exceptional.coeff 453 =
      ((((28998575763742349467 * 10 ^ 70 +
        5454518338758035995498718878471001551319418157792680348359711224678874) * 10 ^ 70 +
        6481125331257749125574690671829708783173369471623710133274916078511901) * 10 ^ 70 +
        0525139626161116994131723766740686064471898930147774647451260459338134) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (453 - x)) = _
  rw [show 454 = 308 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 30 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (454 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_454 :
    recurrence4Scalar2Exceptional.coeff 454 =
      -((((3525556380850161672 * 10 ^ 70 +
        3290779860621765997623750397928250621854773181244206713421131757707371) * 10 ^ 70 +
        1941817723857909484720550562409128168396446779833541446959829523067669) * 10 ^ 70 +
        8860892041607004916061208460918513439500609824278389318287383921874420) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (454 - x)) = _
  rw [show 455 = 309 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 29 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (455 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_455 :
    recurrence4Scalar2Exceptional.coeff 455 =
      ((((226222901950331308 * 10 ^ 70 +
        0504881497110376623410675767711812283890645173099636298545552709132464) * 10 ^ 70 +
        8904711249472637312504075375594638064285107595101428431037842690676289) * 10 ^ 70 +
        6476493441207322881515230921112877710589762945924135217758162785579710) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (455 - x)) = _
  rw [show 456 = 310 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 28 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (456 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_456 :
    recurrence4Scalar2Exceptional.coeff 456 =
      ((((327850011368492 * 10 ^ 70 +
        3214708735166239439376688244869163620710259711080758292784688826775118) * 10 ^ 70 +
        6199632980959288119724807474323110142677660053645028296271154080086858) * 10 ^ 70 +
        0609133368500748539497271935097930542076442875364062520587565379470048) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (456 - x)) = _
  rw [show 457 = 311 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 27 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (457 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_457 :
    recurrence4Scalar2Exceptional.coeff 457 =
      -((((1822116922485952 * 10 ^ 70 +
        6094146544057355066154532704003051840911074380005966874188450712741766) * 10 ^ 70 +
        6629650549964847927725196610784524999779631542226795791422304667596397) * 10 ^ 70 +
        7136129290637353823569592093817491901585104899254697027685732218600296) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (457 - x)) = _
  rw [show 458 = 312 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 26 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (458 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_458 :
    recurrence4Scalar2Exceptional.coeff 458 =
      ((((207661258754602 * 10 ^ 70 +
        3608529380733579572353351288677095652189661186108686184047608645342812) * 10 ^ 70 +
        9280902972773687257767091446925049029382802357698370564778758687573457) * 10 ^ 70 +
        4406057820951617762829654712054090311183009357451591283135406223639786) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (458 - x)) = _
  rw [show 459 = 313 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 25 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (459 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_459 :
    recurrence4Scalar2Exceptional.coeff 459 =
      -((((10185856443297 * 10 ^ 70 +
        0540225376720431785209683061511245951459232267658810029812479507544505) * 10 ^ 70 +
        1418349735469317738412938385229805456158672998403974934371913443706241) * 10 ^ 70 +
        1545526449216713480187675666311387876524706313435594617139701148751933) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (459 - x)) = _
  rw [show 460 = 314 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 24 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (460 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_460 :
    recurrence4Scalar2Exceptional.coeff 460 =
      -((((245775244042 * 10 ^ 70 +
        4902866114629863100942581979297102883456811151242665213969797191540326) * 10 ^ 70 +
        6040003996272766685561394818981938962589082843582266336159444582075848) * 10 ^ 70 +
        1652793928701049734795569365449674211023736026438108523040476072313941) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (460 - x)) = _
  rw [show 461 = 315 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 23 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (461 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_461 :
    recurrence4Scalar2Exceptional.coeff 461 =
      ((((78525433744 * 10 ^ 70 +
        2797099274761919153299151141155902872508648430896470843413227382899186) * 10 ^ 70 +
        9672439299569614569293939951388841562073058704597999753373554391767861) * 10 ^ 70 +
        0036648544638008428373068087211533647219707379088789470926973100430166) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (461 - x)) = _
  rw [show 462 = 316 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 22 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (462 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_462 :
    recurrence4Scalar2Exceptional.coeff 462 =
      -((((5330232239 * 10 ^ 70 +
        8240958435327624862305384742522446656365637817047131462915095017833458) * 10 ^ 70 +
        9373673172258077690181126448874278677511520094854179179740342016567837) * 10 ^ 70 +
        1672564354387674900439825891495240226506784278887859221121016206063319) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (462 - x)) = _
  rw [show 463 = 317 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 21 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (463 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_463 :
    recurrence4Scalar2Exceptional.coeff 463 =
      ((((49465417 * 10 ^ 70 +
        6114300721682894662184382041551866257826833722719311756661340379729292) * 10 ^ 70 +
        5437563410286367575620154300868287770659172341167247742526069597210897) * 10 ^ 70 +
        4522237171169652887186820654662467009189447506440943323334293399606003) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (463 - x)) = _
  rw [show 464 = 318 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 20 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (464 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_464 :
    recurrence4Scalar2Exceptional.coeff 464 =
      ((((18292182 * 10 ^ 70 +
        8919533653261341416639736650222721516671488694380069982278068554461832) * 10 ^ 70 +
        4450657458795168175273153917305976543335563691797576985628007938323426) * 10 ^ 70 +
        5056336407327484932778054592278003187425751655838738866581171343918571) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (464 - x)) = _
  rw [show 465 = 319 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 19 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (465 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_465 :
    recurrence4Scalar2Exceptional.coeff 465 =
      -((((1284827 * 10 ^ 70 +
        0088772861625531441457826102792519203886745488665361363784890291384261) * 10 ^ 70 +
        0087254194874983680627998119824594871797809331273577014852666059913431) * 10 ^ 70 +
        8251248997287653936846132955542482106569864022389636391178734881038534) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (465 - x)) = _
  rw [show 466 = 320 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 18 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (466 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_466 :
    recurrence4Scalar2Exceptional.coeff 466 =
      ((((7909 * 10 ^ 70 +
        9414001053601790431797020415427813554521721457516702662787342633959628) * 10 ^ 70 +
        8134114592200292632826889872980318993609064330893730281081757128965023) * 10 ^ 70 +
        3895962680853947984442584354906302518862105894275138379896804222131392) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (466 - x)) = _
  rw [show 467 = 321 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 17 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (467 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_467 :
    recurrence4Scalar2Exceptional.coeff 467 =
      ((((3427 * 10 ^ 70 +
        8496199788387046442798404762091456827008439695433833419284758628214328) * 10 ^ 70 +
        4179919576367944796362070195640420687211277909544348263666898045768806) * 10 ^ 70 +
        7334494272130484971190832447158637595772180282191489963609971688878889) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (467 - x)) = _
  rw [show 468 = 322 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 16 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_467_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (468 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_468 :
    recurrence4Scalar2Exceptional.coeff 468 =
      -((((153 * 10 ^ 70 +
        6697955462629679405096121708933084344513101891826001628487963786950881) * 10 ^ 70 +
        4397825021281584344012809214819930114178285350252496752858117610699214) * 10 ^ 70 +
        5657518471831012692923803432445667527542213480132970995791060827976100) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (468 - x)) = _
  rw [show 469 = 323 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 15 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_468_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (469 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_469 :
    recurrence4Scalar2Exceptional.coeff 469 =
      -((((3 * 10 ^ 70 +
        1817512410528153078502826649983210257921354798107368213145092129804653) * 10 ^ 70 +
        7959628248044464937830383933846539387555534336350547512147267765574505) * 10 ^ 70 +
        9658262227577521273500513034707036518617304107007127004900904570197561) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (469 - x)) = _
  rw [show 470 = 324 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 14 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_469_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (470 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_470 :
    recurrence4Scalar2Exceptional.coeff 470 =
      (((4025489490301918115825219485964795218710608336363189039081378408022519 * 10 ^ 70 +
        2343449862917462361133992029523611392526999298063604751295398184448406) * 10 ^ 70 +
        0108499904340520308290004082084418811918856936002029163545666012092745) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (470 - x)) = _
  rw [show 471 = 325 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 13 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_470_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (471 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_471 :
    recurrence4Scalar2Exceptional.coeff 471 =
      -(((15508506311584031816191079042181862986175366934506812925375481825585 * 10 ^ 70 +
        9635969278717583036539664457089308120710538349574214770366493530676387) * 10 ^ 70 +
        1569399834575431786282044667228361022880963785572023404958492823062157) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (471 - x)) = _
  rw [show 472 = 326 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 12 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_471_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (472 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_472 :
    recurrence4Scalar2Exceptional.coeff 472 =
      -(((6468078761512087065022703221211071198252802778782862663179047758978 * 10 ^ 70 +
        7806525976422269827685840469607263436140601042113947669962043441713023) * 10 ^ 70 +
        3082106721074153554054756231613210967350081189783874414792878377205693) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (472 - x)) = _
  rw [show 473 = 327 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 11 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_472_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (473 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_473 :
    recurrence4Scalar2Exceptional.coeff 473 =
      (((61543466727160600901701403309587693721663329298797010745003277730 * 10 ^ 70 +
        3005625715002612524597531947030331661926773018648657879519638487832850) * 10 ^ 70 +
        4233569296699372158497447158824906997089473316386657273945677739029668) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (473 - x)) = _
  rw [show 474 = 328 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 10 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_473_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (474 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_474 :
    recurrence4Scalar2Exceptional.coeff 474 =
      (((8352686958553728343342389171256586309028268361675078991126803128 * 10 ^ 70 +
        9045713211187336021313591845919950631878867043706278440678882653422953) * 10 ^ 70 +
        0600164881665518167820744078185710382744262089219280063220706434718299) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (474 - x)) = _
  rw [show 475 = 329 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 9 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_474_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (475 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_475 :
    recurrence4Scalar2Exceptional.coeff 475 =
      -(((20678855757293616866852354390543791035133089625572757985362963 * 10 ^ 70 +
        2694387928780178629261375695153016019029603261394431761345281511539704) * 10 ^ 70 +
        7794334307692779518425839653097890166170886734297380408545833544993451) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (475 - x)) = _
  rw [show 476 = 330 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 8 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_475_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (476 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_476 :
    recurrence4Scalar2Exceptional.coeff 476 =
      -(((8585936751464978812380320992072260611611769023368963143438959 * 10 ^ 70 +
        9813776644095482575972050232074529057282160818637927638241677099044096) * 10 ^ 70 +
        2282567393300060135556309603251899527694833387771293238248175152925217) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (476 - x)) = _
  rw [show 477 = 331 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 7 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_476_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (477 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_477 :
    recurrence4Scalar2Exceptional.coeff 477 =
      -(((128639210343539312072766969737085673796948363831216762779096 * 10 ^ 70 +
        6134279271709917202498230347253483620618782710592044572432564069502635) * 10 ^ 70 +
        9110389749934442847372783702706390145506229465273522019409520873720939) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (477 - x)) = _
  rw [show 478 = 332 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 6 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_477_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
