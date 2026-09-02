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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
