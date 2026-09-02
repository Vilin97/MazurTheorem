/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163

attribute [local simp]
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_170
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59
  recurrence4B1_coeff_60
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91

attribute [local simp]
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_217
  recurrence4QuotientConstant_coeff_218
  recurrence4QuotientConstant_coeff_219
  recurrence4QuotientConstant_coeff_220
  recurrence4QuotientConstant_coeff_221
  recurrence4QuotientConstant_coeff_222
  recurrence4QuotientConstant_coeff_223
  recurrence4QuotientConstant_coeff_224
  recurrence4QuotientConstant_coeff_225
  recurrence4QuotientConstant_coeff_226
  recurrence4QuotientConstant_coeff_227
  recurrence4QuotientConstant_coeff_228
  recurrence4QuotientConstant_coeff_229
  recurrence4QuotientConstant_coeff_230
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_240
  recurrence4QuotientConstant_coeff_241
  recurrence4QuotientConstant_coeff_242
  recurrence4QuotientConstant_coeff_243
  recurrence4QuotientConstant_coeff_244
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_250
  recurrence4QuotientConstant_coeff_251
  recurrence4QuotientConstant_coeff_252
  recurrence4QuotientConstant_coeff_253
  recurrence4QuotientConstant_coeff_254
  recurrence4QuotientConstant_coeff_255
  recurrence4QuotientConstant_coeff_256
  recurrence4QuotientConstant_coeff_257
  recurrence4QuotientConstant_coeff_258
  recurrence4QuotientConstant_coeff_259
  recurrence4QuotientConstant_coeff_260
  recurrence4QuotientConstant_coeff_261
  recurrence4QuotientConstant_coeff_262
  recurrence4QuotientConstant_coeff_263
  recurrence4QuotientConstant_coeff_264
  recurrence4QuotientConstant_coeff_265
  recurrence4QuotientConstant_coeff_266

attribute [local simp]
  recurrence4QuotientConstant_coeff_267
  recurrence4QuotientConstant_coeff_268
  recurrence4QuotientConstant_coeff_269
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_275
  recurrence4QuotientConstant_coeff_276
  recurrence4QuotientConstant_coeff_277
  recurrence4QuotientConstant_coeff_278
  recurrence4QuotientConstant_coeff_279
  recurrence4QuotientConstant_coeff_280
  recurrence4QuotientConstant_coeff_281
  recurrence4QuotientConstant_coeff_282
  recurrence4QuotientConstant_coeff_283
  recurrence4QuotientConstant_coeff_284
  recurrence4QuotientConstant_coeff_285
  recurrence4QuotientConstant_coeff_286
  recurrence4QuotientConstant_coeff_287
  recurrence4QuotientConstant_coeff_288
  recurrence4QuotientConstant_coeff_289
  recurrence4QuotientConstant_coeff_290
  recurrence4QuotientConstant_coeff_291
  recurrence4QuotientConstant_coeff_292
  recurrence4QuotientConstant_coeff_293
  recurrence4QuotientConstant_coeff_294
  recurrence4QuotientConstant_coeff_295
  recurrence4QuotientConstant_coeff_296
  recurrence4QuotientConstant_coeff_297
  recurrence4QuotientConstant_coeff_298
  recurrence4QuotientConstant_coeff_299
  recurrence4QuotientConstant_coeff_300
  recurrence4QuotientConstant_coeff_301
  recurrence4QuotientConstant_coeff_302
  recurrence4QuotientConstant_coeff_303
  recurrence4QuotientConstant_coeff_304
  recurrence4QuotientConstant_coeff_305
  recurrence4QuotientConstant_coeff_306
  recurrence4QuotientConstant_coeff_307
  recurrence4QuotientConstant_coeff_308
  recurrence4QuotientConstant_coeff_309
  recurrence4QuotientConstant_coeff_310
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

attribute [local simp]
  recurrence4QuotientConstant_coeff_331
  recurrence4QuotientConstant_coeff_332
  recurrence4QuotientConstant_coeff_333
  recurrence4QuotientConstant_coeff_334
  recurrence4QuotientConstant_coeff_335
  recurrence4QuotientConstant_coeff_336
  recurrence4QuotientConstant_coeff_337
  recurrence4QuotientConstant_coeff_338
  recurrence4QuotientConstant_coeff_339
  recurrence4QuotientConstant_coeff_340
  recurrence4QuotientConstant_coeff_341
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346

private theorem recurrence4Scalar1Second_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (458 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (458 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_458 :
    recurrence4Scalar1Second.coeff 458 =
      ((((4581517873298164113874 * 10 ^ 70 +
        3654619866315196054315305167362879655163774313039767525678574000162866) * 10 ^ 70 +
        7793732534481366174787485374143383206965391804975088236270616528446765) * 10 ^ 70 +
        9565188165698255832392843002126324297025103457869220362445811069767734) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (458 - x)) = _
  rw [show 459 = 112 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 29 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (459 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (459 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_459 :
    recurrence4Scalar1Second.coeff 459 =
      -((((432545713237268264038 * 10 ^ 70 +
        8846847383545043158314531717237670604040683283187253076760867334503966) * 10 ^ 70 +
        7759074360307310239302396066988505246950798521853110995787266795126920) * 10 ^ 70 +
        9615757288492762735224653406365133445664728087775286139862216666053780) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (459 - x)) = _
  rw [show 460 = 113 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 28 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (460 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (460 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_460 :
    recurrence4Scalar1Second.coeff 460 =
      ((((22443323120204317865 * 10 ^ 70 +
        3410013717827997558040240449012850502408665595925033691079906513684455) * 10 ^ 70 +
        9879769897596063960971265068941528870495051051033936329265196706051764) * 10 ^ 70 +
        5863874211423848697719182350082369667480227280376537632349668590464934) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (460 - x)) = _
  rw [show 461 = 114 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 27 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (461 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (461 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_461 :
    recurrence4Scalar1Second.coeff 461 =
      ((((1441682357280730711 * 10 ^ 70 +
        7688935328864764646372857677043268790646886320081746303706829069519092) * 10 ^ 70 +
        5816161145829036261988579491668766092995711439859503463447578285203052) * 10 ^ 70 +
        1580809211267604623742053321043055142517248016412371198442522584422255) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (461 - x)) = _
  rw [show 462 = 115 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 26 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (462 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (462 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_462 :
    recurrence4Scalar1Second.coeff 462 =
      -((((567366559815404638 * 10 ^ 70 +
        3261158906198887007625323168279180881978545160286549861873064038554336) * 10 ^ 70 +
        8049939538697724238016677278199678556985975507013169691689038757453629) * 10 ^ 70 +
        4771197055534286551354133645942513283037355945709723437668507480616942) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (462 - x)) = _
  rw [show 463 = 116 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 25 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (463 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (463 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_463 :
    recurrence4Scalar1Second.coeff 463 =
      ((((89179515549669399 * 10 ^ 70 +
        7471784165632587326571919730928104607072599481613929598540289102395417) * 10 ^ 70 +
        5942249338509635669001259192721322721278112145171820906418575639484553) * 10 ^ 70 +
        3931590795946166258741877072175368917592270907646814717031078362560172) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (463 - x)) = _
  rw [show 464 = 117 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 24 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (464 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (464 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_464 :
    recurrence4Scalar1Second.coeff 464 =
      -((((9907765037948716 * 10 ^ 70 +
        0528331407780142528559935351341604566726421023888569266638041836039070) * 10 ^ 70 +
        6161227906461529936786617607001145986491832256710782263917737369692219) * 10 ^ 70 +
        1400946975851710891801267059874373967190164737504083867793826527482905) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (464 - x)) = _
  rw [show 465 = 118 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 23 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (465 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (465 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_465 :
    recurrence4Scalar1Second.coeff 465 =
      ((((834084604090698 * 10 ^ 70 +
        4757120470080650318328627491419764688272087199017530241065670679710034) * 10 ^ 70 +
        5800528569266408155580402076027335265561428326700697449699062808096724) * 10 ^ 70 +
        9655272990557246582812968166791290138733346581062508579414353615605788) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (465 - x)) = _
  rw [show 466 = 119 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 22 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (466 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (466 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_466 :
    recurrence4Scalar1Second.coeff 466 =
      -((((50577622808750 * 10 ^ 70 +
        8289160975793817982762427796455460714827102124705169139209567338548238) * 10 ^ 70 +
        1910367270746024379175830177549909578263732080692448314418240426318694) * 10 ^ 70 +
        2915005629145143496218221166227528812547068356611210199051499147385423) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (466 - x)) = _
  rw [show 467 = 120 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 21 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (467 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (467 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_467 :
    recurrence4Scalar1Second.coeff 467 =
      ((((1544924451846 * 10 ^ 70 +
        0760937211628028985112324312099525638728627377387159413466915222569805) * 10 ^ 70 +
        5721224172453197980800945255747555198182358634755437228896430504041336) * 10 ^ 70 +
        8721462947220158694961971591651759696296982263263126932028319830509718) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (467 - x)) = _
  rw [show 468 = 121 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 20 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_467_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (468 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (468 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_468 :
    recurrence4Scalar1Second.coeff 468 =
      ((((91019881947 * 10 ^ 70 +
        7958435466353293113454652865396365160656867327501740681984914246977184) * 10 ^ 70 +
        7245939958660163815258265318294981439440865712330621993441941767775796) * 10 ^ 70 +
        8974825150961522288963795549524251788212015110402846082993047946576950) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (468 - x)) = _
  rw [show 469 = 122 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 19 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_468_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (469 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (469 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_469 :
    recurrence4Scalar1Second.coeff 469 =
      -((((18343279733 * 10 ^ 70 +
        8746310490134331309021774639725432994067528057697815354321558827791967) * 10 ^ 70 +
        0911514547680088673779882532148798455654741735932245737813387346592695) * 10 ^ 70 +
        1465464435858418106382321023353567487619838472030834427374078397022875) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (469 - x)) = _
  rw [show 470 = 123 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 18 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_469_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (470 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (470 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_470 :
    recurrence4Scalar1Second.coeff 470 =
      ((((1585475709 * 10 ^ 70 +
        7645206472878005895511997967913024982324003528615983030743807059241751) * 10 ^ 70 +
        7260196797527650494185715626368187276243934355755832372218279003223610) * 10 ^ 70 +
        9997363018593189682439833267690145781072010975318815468367461822952505) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (470 - x)) = _
  rw [show 471 = 124 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 17 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_470_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (471 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (471 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_471 :
    recurrence4Scalar1Second.coeff 471 =
      -((((88426205 * 10 ^ 70 +
        4968395513310987935922468989234602434515188314208698862354687581812259) * 10 ^ 70 +
        2997593137551502713008340347608044106642980438683787606818514929118399) * 10 ^ 70 +
        3614398183005879834738514946863348574140808180259418404003158390067578) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (471 - x)) = _
  rw [show 472 = 125 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 16 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_471_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (472 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (472 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_472 :
    recurrence4Scalar1Second.coeff 472 =
      ((((2949587 * 10 ^ 70 +
        2984655671956189616080283372341283159972745116942579896765990049284942) * 10 ^ 70 +
        2394425976300166117202826951547767595278237595301183029194983760600329) * 10 ^ 70 +
        1856101929255838676224826293681861678253799064553991939772454120177080) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (472 - x)) = _
  rw [show 473 = 126 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 15 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_472_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (473 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (473 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_473 :
    recurrence4Scalar1Second.coeff 473 =
      -((((8480 * 10 ^ 70 +
        4062256670430238107098051059099171466903496733416305706613481137990626) * 10 ^ 70 +
        1588336253993018278164959393985064325341257677613975849739983794460146) * 10 ^ 70 +
        6085154919660733345219046821530688881279347556210853002551342126947590) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (473 - x)) = _
  rw [show 474 = 127 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 14 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_473_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (474 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (474 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_474 :
    recurrence4Scalar1Second.coeff 474 =
      -((((5383 * 10 ^ 70 +
        5507487619176533618821196324957796522047594029694554317496660138912428) * 10 ^ 70 +
        2119363272602500518536250337703561326989474854462064712212840323482748) * 10 ^ 70 +
        2642594222784148618331405653534334067477561070534166863525150186252902) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (474 - x)) = _
  rw [show 475 = 128 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 13 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_474_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (475 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (475 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_475 :
    recurrence4Scalar1Second.coeff 475 =
      ((((324 * 10 ^ 70 +
        6189776805208155305956146002345574056460404811393284207769810334298913) * 10 ^ 70 +
        0306619364623560185365244456249008507454500100917087119709892187581885) * 10 ^ 70 +
        7053321562663506432088148135834741247317110982927380942025990315967698) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (475 - x)) = _
  rw [show 476 = 129 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 12 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_475_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (476 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (476 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_476 :
    recurrence4Scalar1Second.coeff 476 =
      -((((8 * 10 ^ 70 +
        7989105693678167274757480431326829754256556362813718342227019117872850) * 10 ^ 70 +
        3350077518165092530489711854410633375920371215862553015877263021699183) * 10 ^ 70 +
        1911758053260743213431722195960731353029175831623332895880489907383616) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (476 - x)) = _
  rw [show 477 = 130 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 11 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_476_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (477 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (477 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_477 :
    recurrence4Scalar1Second.coeff 477 =
      (((196466627747958759453827042799814559471602787184527290150702577242808 * 10 ^ 70 +
        0435886928946116580823412936563408396900906050478620190649060463634711) * 10 ^ 70 +
        4224652764726604138745262623916300687753525086652514619849067592594823) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (477 - x)) = _
  rw [show 478 = 131 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 10 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_477_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (478 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (478 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_478 :
    recurrence4Scalar1Second.coeff 478 =
      (((64040068575171941540421377164470683039991094327871264648431700590749 * 10 ^ 70 +
        6828526587496148958938928345668830455038361092006658459664011538270048) * 10 ^ 70 +
        3019141021246222130850136006522531923018735588102414122947628212621733) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (478 - x)) = _
  rw [show 479 = 132 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 9 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (479 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (479 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_479 :
    recurrence4Scalar1Second.coeff 479 =
      -(((1693585157580120967959775794019236823882557577610219235013823675059 * 10 ^ 70 +
        1987761532862521165001718274672105536641002298218225500993352394649733) * 10 ^ 70 +
        4010124984722708573917236082626030441872620983450668829900021919065097) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (479 - x)) = _
  rw [show 480 = 133 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 8 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (480 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (480 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_480 :
    recurrence4Scalar1Second.coeff 480 =
      (((428476796876125402629712499761083863137262312457274023074506165 * 10 ^ 70 +
        5821861131635910850149819542949354326263362240117688414786375518010477) * 10 ^ 70 +
        0324400998211935663345885798760241452897384428430418236613182853900282) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (480 - x)) = _
  rw [show 481 = 134 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 7 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (481 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (481 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_481 :
    recurrence4Scalar1Second.coeff 481 =
      (((571620929562550029966431625721047329796733360869817049113254062 * 10 ^ 70 +
        6366549521343627158179798987345895001937364733753782231369976149994968) * 10 ^ 70 +
        5891765091670282535978187420286377623916784896195974935214465791173872) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (481 - x)) = _
  rw [show 482 = 135 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 6 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (482 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (482 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_482 :
    recurrence4Scalar1Second.coeff 482 =
      -(((3737142562596350340282869761772721630562141053681895513326655 * 10 ^ 70 +
        1990628007641376920732567489993912548162034724799772267010230400454695) * 10 ^ 70 +
        3221948328984620313037461278607904447002614288350536323513535891927386) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (482 - x)) = _
  rw [show 483 = 136 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 5 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (483 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (483 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_483 :
    recurrence4Scalar1Second.coeff 483 =
      -(((91310160464374603435474983446296302341011409367853177217294 * 10 ^ 70 +
        7593641876362595139483609991298344515917770323429099078824620213580538) * 10 ^ 70 +
        4280273193814692449245729147072212814023759519922465361581510025906391) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (483 - x)) = _
  rw [show 484 = 137 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 4 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (484 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (484 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_484 :
    recurrence4Scalar1Second.coeff 484 =
      (((503607785877125461216791671980561889662996031852569481867 * 10 ^ 70 +
        7811584684576150408454181957290438767188406229998696564912333482524741) * 10 ^ 70 +
        7769049816666811792696168116900941160111916767247598012619684706889308) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (484 - x)) = _
  rw [show 485 = 138 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 3 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
