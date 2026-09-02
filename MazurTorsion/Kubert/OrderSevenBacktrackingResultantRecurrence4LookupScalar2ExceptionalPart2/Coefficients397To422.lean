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

private theorem recurrence4Scalar2Exceptional_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (397 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_397 :
    recurrence4Scalar2Exceptional.coeff 397 =
      -((((3192885366813986313802598147336904453929979801765887174785 * 10 ^ 70 +
        5472793489728244499349093657184713169329913830436097756510950498795435) * 10 ^ 70 +
        0599969626298042599510638862083242584752714776398928789181576117276993) * 10 ^ 70 +
        7264228366881399842329798398787818490033845718286831012223158366608334) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (397 - x)) = _
  rw [show 398 = 252 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 22 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (398 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_398 :
    recurrence4Scalar2Exceptional.coeff 398 =
      ((((952473422660556608822935916166386149896691794169749514877 * 10 ^ 70 +
        2833986708027015410960042424460942690136835149042422744046820803668421) * 10 ^ 70 +
        5160297902154766818801526380072639849582355999917051869921620871940771) * 10 ^ 70 +
        9549526496497782913786140607107673466826436954116602758893443008169405) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (398 - x)) = _
  rw [show 399 = 253 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 21 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (399 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_399 :
    recurrence4Scalar2Exceptional.coeff 399 =
      -((((266425874167535484271074149507131908677538135181822128629 * 10 ^ 70 +
        5147207741670352574012193403057400121518453225364370934951162244362427) * 10 ^ 70 +
        0292454131711144301879912047552176986102639718801457113682532471363057) * 10 ^ 70 +
        5736554343035092224587764655477315152506030864736692499767922821687377) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (399 - x)) = _
  rw [show 400 = 254 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 20 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (400 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_400 :
    recurrence4Scalar2Exceptional.coeff 400 =
      ((((68304485842756418807805936206744458040574616161844523269 * 10 ^ 70 +
        8469825478797076775994357281791225273688081838080493343793929929111725) * 10 ^ 70 +
        8388271546226056198639028109460808737002269136642411454213575260476254) * 10 ^ 70 +
        7497795517771776871248538953021534445514826731677749877080042920886710) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (400 - x)) = _
  rw [show 401 = 255 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 19 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (401 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_401 :
    recurrence4Scalar2Exceptional.coeff 401 =
      -((((15273832741607102307051046569169622223096298540409684335 * 10 ^ 70 +
        0856055509646942856810779406367398494241692435981948568542118519625873) * 10 ^ 70 +
        3443163754285901035044282052134255918200614629849556438721308889354948) * 10 ^ 70 +
        9227701618401125055383288989335397870626968018777493334151148184766358) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (401 - x)) = _
  rw [show 402 = 256 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 18 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (402 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_402 :
    recurrence4Scalar2Exceptional.coeff 402 =
      ((((2565547937561171181632592247245124562307764111673707767 * 10 ^ 70 +
        3616288335164613266831273308377761803877932029787226430820442151013742) * 10 ^ 70 +
        1320795820053909749976141717380531611392999168463565629300398731554346) * 10 ^ 70 +
        6424579024885912906632154588711174245861795291064463351841405661707889) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (402 - x)) = _
  rw [show 403 = 257 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 17 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (403 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_403 :
    recurrence4Scalar2Exceptional.coeff 403 =
      -((((68857434420540586574852289423121079689352831616301903 * 10 ^ 70 +
        6413082533122974673482516505600858401716967456886791135364573154395252) * 10 ^ 70 +
        3863601851256389742057316736218285179144822558406154691049920425807517) * 10 ^ 70 +
        0732160810319293844226864227197488754519279081884807032281204324425703) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (403 - x)) = _
  rw [show 404 = 258 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 16 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (404 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_404 :
    recurrence4Scalar2Exceptional.coeff 404 =
      -((((201514313387523038187819383213568637280749493674180870 * 10 ^ 70 +
        7554678615335394404595679585101874597136993734619478987129640214354617) * 10 ^ 70 +
        2945595497220537250019232082971795940505835733970514578549333806264608) * 10 ^ 70 +
        7105358995541352667354776201236895870259305969705658839463431462103588) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (404 - x)) = _
  rw [show 405 = 259 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 15 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (405 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_405 :
    recurrence4Scalar2Exceptional.coeff 405 =
      ((((124702692647284355985315073831802748390642830218622337 * 10 ^ 70 +
        5621094580763171608939611905382046845143389243644233447834364568680139) * 10 ^ 70 +
        5150415104888602635354335600198655345502252220575934786821447044725659) * 10 ^ 70 +
        5984952699325720105711831391090963451755360432418779617766399211844134) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (405 - x)) = _
  rw [show 406 = 260 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 14 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (406 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_406 :
    recurrence4Scalar2Exceptional.coeff 406 =
      -((((54123837863119862991401682619652528169267297541983902 * 10 ^ 70 +
        9617086228957565578307313780011260739295443202372661938879081201939701) * 10 ^ 70 +
        7707089410021533540896693415287121689557583345948296388149621774841884) * 10 ^ 70 +
        8358333503859218491152045735009653200683901061596682221220383332569440) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (406 - x)) = _
  rw [show 407 = 261 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 13 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (407 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_407 :
    recurrence4Scalar2Exceptional.coeff 407 =
      ((((19996662371670540096277131897079738683439975418590520 * 10 ^ 70 +
        2541503488934302916562603999244989550916633495481149140158048672745297) * 10 ^ 70 +
        4764751385429489173875908374433449065065789554124919652768304878698103) * 10 ^ 70 +
        2717283773918916300192691672220750341610520310081577397069792628306908) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (407 - x)) = _
  rw [show 408 = 262 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 12 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (408 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_408 :
    recurrence4Scalar2Exceptional.coeff 408 =
      -((((6646842409273453836110590520950321602836879504671276 * 10 ^ 70 +
        3724601409862304316492545303429717806865394240107284978175372233711661) * 10 ^ 70 +
        4118062300938728444324243441225517423103040962480483126379983131436187) * 10 ^ 70 +
        9616784713787778006818399563516367532375005676067050112996972984290314) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (408 - x)) = _
  rw [show 409 = 263 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 11 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (409 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_409 :
    recurrence4Scalar2Exceptional.coeff 409 =
      ((((2030657767034710056267509129023967456556363596671428 * 10 ^ 70 +
        7978997270093525634100729454756202057966401734433236338296876481234518) * 10 ^ 70 +
        2330479561861322765132431829147612455340217615920927325588538276538681) * 10 ^ 70 +
        5209872129500413500359693396118219584500125607455571886522894513565586) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (409 - x)) = _
  rw [show 410 = 264 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 10 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (410 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_410 :
    recurrence4Scalar2Exceptional.coeff 410 =
      -((((574468355517337702132075301023574601929119351861848 * 10 ^ 70 +
        8780982888821508716781762000501209768283951167284451555776008395444969) * 10 ^ 70 +
        2302279752400731869571610452235525853505304195604198437469471657490028) * 10 ^ 70 +
        7173579099618262201950487191678869733513354927590215186978861444623199) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (410 - x)) = _
  rw [show 411 = 265 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 9 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (411 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_411 :
    recurrence4Scalar2Exceptional.coeff 411 =
      ((((150272738580388936403341545270750329723648689576794 * 10 ^ 70 +
        0248051378787034517574681339277988259447060272873787528972516458746010) * 10 ^ 70 +
        4954549610912390228619556160706369356792574919789805956348606564358925) * 10 ^ 70 +
        0898846394455645671237384166245366511253936288678783021924773347280632) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (411 - x)) = _
  rw [show 412 = 266 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 8 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (412 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_412 :
    recurrence4Scalar2Exceptional.coeff 412 =
      -((((35939072972762811730063609078087338036737631678326 * 10 ^ 70 +
        7889561690117506982151400716467362469437163920031130977638092057507751) * 10 ^ 70 +
        4341277834454564383361157330069277269504367629693863199345930981653755) * 10 ^ 70 +
        8970599037400074278067872464022587400932997116074790668874439385247623) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (412 - x)) = _
  rw [show 413 = 267 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 7 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (413 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_413 :
    recurrence4Scalar2Exceptional.coeff 413 =
      ((((7628869539731953412620573159134944157308313556304 * 10 ^ 70 +
        8917336324112652431165125045523925253956760472141058125865272614662522) * 10 ^ 70 +
        5427427713420867789317050363943471812957453981577279271793098392537439) * 10 ^ 70 +
        4312251248695448409133324197212448137401312935744415455978501506380453) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (413 - x)) = _
  rw [show 414 = 268 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 6 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (414 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_414 :
    recurrence4Scalar2Exceptional.coeff 414 =
      -((((1324134200034594566475420469952803698900918866031 * 10 ^ 70 +
        4857712503972356254648083542475941784657247245063983457619913165176883) * 10 ^ 70 +
        7280292008343504527064176578081595374853095803761012095911576262249092) * 10 ^ 70 +
        7976697125287621014587090159036811672891035981314299886962533962574070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (414 - x)) = _
  rw [show 415 = 269 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 5 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (415 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_415 :
    recurrence4Scalar2Exceptional.coeff 415 =
      ((((129547994380375934383430475294028492795688007245 * 10 ^ 70 +
        5116781431195289017120181237916215254683065535860669661041131971747795) * 10 ^ 70 +
        4642177293877702892457394520678173274906868873062147181377251499940472) * 10 ^ 70 +
        5830410123784306513442556477421730239500877108663515458846121314046336) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (415 - x)) = _
  rw [show 416 = 270 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 4 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (416 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_416 :
    recurrence4Scalar2Exceptional.coeff 416 =
      ((((28799596927581098551311335526913059123755939841 * 10 ^ 70 +
        5618737072391013067321469121404155696325785805356174792796471923173016) * 10 ^ 70 +
        1058664598809338744084960026570115453811983103803819856004800795170888) * 10 ^ 70 +
        8414980371623965504921789429212959102295465021863377505138142833801853) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (416 - x)) = _
  rw [show 417 = 271 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 3 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (417 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_417 :
    recurrence4Scalar2Exceptional.coeff 417 =
      -((((24019304639848969478980315951255748344610415115 * 10 ^ 70 +
        5303731192486937623334339123504931250044711470113764729579769114996206) * 10 ^ 70 +
        4082197826366773884386614137997331473280196335986812657590670289595010) * 10 ^ 70 +
        9084327808530880766994442878494568418494436070293763378241183360005646) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (417 - x)) = _
  rw [show 418 = 272 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 2 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (418 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_418 :
    recurrence4Scalar2Exceptional.coeff 418 =
      ((((10215663121202858636390052599130637094757346438 * 10 ^ 70 +
        8659915772196377819121472709348308308277387040589104765730001930571404) * 10 ^ 70 +
        3801502859395961254472999828103056778987802460427897179295186541866324) * 10 ^ 70 +
        9471463441093704249190341120630906624620757278757456987087774999534665) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (418 - x)) = _
  rw [show 419 = 273 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 1 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (419 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_419 :
    recurrence4Scalar2Exceptional.coeff 419 =
      -((((3502281556683445030486244889255463890966819990 * 10 ^ 70 +
        3437742582834118601330041708412869234906433071618928319697903122898744) * 10 ^ 70 +
        8010102499526970441103852783679962466108957669630807324148175083272291) * 10 ^ 70 +
        5055324430807282546103348938921402418775265583087217039310723588835111) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (419 - x)) = _
  rw [show 420 = 274 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (420 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_420 :
    recurrence4Scalar2Exceptional.coeff 420 =
      ((((1059685936958712377281105280190366387836743062 * 10 ^ 70 +
        4213639339656786849138796446219581725473010738779232811559906978337394) * 10 ^ 70 +
        9777796013123267561310944411122820912611712826236014733790965322493608) * 10 ^ 70 +
        8425295535224346116574969747505314525462404711397878204451315900490573) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (420 - x)) = _
  rw [show 421 = 275 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 31 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (421 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_421 :
    recurrence4Scalar2Exceptional.coeff 421 =
      -((((291731008339702161466731626308063472133253459 * 10 ^ 70 +
        0602517251204382276337303926002917171861367715779845975311025615837521) * 10 ^ 70 +
        8315640016042348297118983700842866448159815030218715391361948689536581) * 10 ^ 70 +
        8771476129378347006229380839804985420481866196245048988994469199436232) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (421 - x)) = _
  rw [show 422 = 276 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 30 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (422 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_422 :
    recurrence4Scalar2Exceptional.coeff 422 =
      ((((73780956442930037182890233980530343464308965 * 10 ^ 70 +
        7215872946013577414204564945734420785890599819998761139466034970792630) * 10 ^ 70 +
        2029038668320427523851323536164944962508586163346397289856533812616975) * 10 ^ 70 +
        2476864648473278716450199527289152830527594166467675702188624085030977) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (422 - x)) = _
  rw [show 423 = 277 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 29 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
