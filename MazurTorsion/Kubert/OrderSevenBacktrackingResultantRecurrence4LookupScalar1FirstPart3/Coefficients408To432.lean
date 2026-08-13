/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163

attribute [local simp]
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_60
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92

attribute [local simp]
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_210
  recurrence4B3A4_coeff_211
  recurrence4B3A4_coeff_212
  recurrence4B3A4_coeff_213
  recurrence4B3A4_coeff_214
  recurrence4B3A4_coeff_215
  recurrence4B3A4_coeff_216
  recurrence4B3A4_coeff_217
  recurrence4B3A4_coeff_218
  recurrence4B3A4_coeff_219
  recurrence4B3A4_coeff_220
  recurrence4B3A4_coeff_221
  recurrence4B3A4_coeff_222
  recurrence4B3A4_coeff_223
  recurrence4B3A4_coeff_224
  recurrence4B3A4_coeff_225
  recurrence4B3A4_coeff_226
  recurrence4B3A4_coeff_227
  recurrence4B3A4_coeff_228
  recurrence4B3A4_coeff_229
  recurrence4B3A4_coeff_230
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_240
  recurrence4B3A4_coeff_241
  recurrence4B3A4_coeff_242
  recurrence4B3A4_coeff_243
  recurrence4B3A4_coeff_244
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251
  recurrence4B3A4_coeff_252
  recurrence4B3A4_coeff_253
  recurrence4B3A4_coeff_254
  recurrence4B3A4_coeff_255
  recurrence4B3A4_coeff_256
  recurrence4B3A4_coeff_257
  recurrence4B3A4_coeff_258
  recurrence4B3A4_coeff_259
  recurrence4B3A4_coeff_260
  recurrence4B3A4_coeff_261
  recurrence4B3A4_coeff_262
  recurrence4B3A4_coeff_263
  recurrence4B3A4_coeff_264

attribute [local simp]
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
  recurrence4B3A4_coeff_275
  recurrence4B3A4_coeff_276
  recurrence4B3A4_coeff_277
  recurrence4B3A4_coeff_278
  recurrence4B3A4_coeff_279
  recurrence4B3A4_coeff_280
  recurrence4B3A4_coeff_281
  recurrence4B3A4_coeff_282
  recurrence4B3A4_coeff_283
  recurrence4B3A4_coeff_284
  recurrence4B3A4_coeff_285
  recurrence4B3A4_coeff_286
  recurrence4B3A4_coeff_287
  recurrence4B3A4_coeff_288
  recurrence4B3A4_coeff_289
  recurrence4B3A4_coeff_290
  recurrence4B3A4_coeff_291
  recurrence4B3A4_coeff_292
  recurrence4B3A4_coeff_293
  recurrence4B3A4_coeff_294
  recurrence4B3A4_coeff_295
  recurrence4B3A4_coeff_296
  recurrence4B3A4_coeff_297
  recurrence4B3A4_coeff_298
  recurrence4B3A4_coeff_299
  recurrence4B3A4_coeff_300
  recurrence4B3A4_coeff_301
  recurrence4B3A4_coeff_302
  recurrence4B3A4_coeff_303
  recurrence4B3A4_coeff_304
  recurrence4B3A4_coeff_305
  recurrence4B3A4_coeff_306
  recurrence4B3A4_coeff_307
  recurrence4B3A4_coeff_308
  recurrence4B3A4_coeff_309
  recurrence4B3A4_coeff_310
  recurrence4B3A4_coeff_311
  recurrence4B3A4_coeff_312
  recurrence4B3A4_coeff_313
  recurrence4B3A4_coeff_314
  recurrence4B3A4_coeff_315
  recurrence4B3A4_coeff_316
  recurrence4B3A4_coeff_317
  recurrence4B3A4_coeff_318
  recurrence4B3A4_coeff_319
  recurrence4B3A4_coeff_320
  recurrence4B3A4_coeff_321
  recurrence4B3A4_coeff_322
  recurrence4B3A4_coeff_323
  recurrence4B3A4_coeff_324
  recurrence4B3A4_coeff_325
  recurrence4B3A4_coeff_326
  recurrence4B3A4_coeff_327
  recurrence4B3A4_coeff_328

attribute [local simp]
  recurrence4B3A4_coeff_329
  recurrence4B3A4_coeff_330
  recurrence4B3A4_coeff_331
  recurrence4B3A4_coeff_332
  recurrence4B3A4_coeff_333
  recurrence4B3A4_coeff_334
  recurrence4B3A4_coeff_335
  recurrence4B3A4_coeff_336
  recurrence4B3A4_coeff_337
  recurrence4B3A4_coeff_338
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar1First_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (408 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (408 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_408 :
    recurrence4Scalar1First.coeff 408 =
      -((((12314685739099620975860896360379613234942106121251067 * 10 ^ 70 +
        0491203118050764144335905889914474969898148244687878621385752682179587) * 10 ^ 70 +
        5952939596071997627138389100751323271957193756800517959646629631770366) * 10 ^ 70 +
        7129285628518049532729208439036854129286319510845475609475835077812672) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (408 - x)) = _
  rw [show 409 = 66 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 15 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (409 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (409 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_409 :
    recurrence4Scalar1First.coeff 409 =
      ((((126094030961639835084911499362699075373938030502806 * 10 ^ 70 +
        3563238178622721904475602054103387314463145290516033711046602745017299) * 10 ^ 70 +
        7539670967817371839203612533101493168624223714557738903482192024788187) * 10 ^ 70 +
        4526198348160514746041733769019642398728004828790494919343158444286335) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (409 - x)) = _
  rw [show 410 = 67 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 14 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (410 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (410 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_410 :
    recurrence4Scalar1First.coeff 410 =
      ((((1261144996264465699241456232569362526294220749464114 * 10 ^ 70 +
        4854385389744970880949666450204246449449169203604411257525630944836748) * 10 ^ 70 +
        4790700044655010580162247542678015723527386959575974079805027412617216) * 10 ^ 70 +
        4318531524001897459105826465684887101500507659910374017998294478392726) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (410 - x)) = _
  rw [show 411 = 68 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 13 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (411 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (411 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_411 :
    recurrence4Scalar1First.coeff 411 =
      -((((832578326569442170203503428575288387019851055342935 * 10 ^ 70 +
        6856756299609761820769159537239681622687106863762339320078117448474967) * 10 ^ 70 +
        2563168898785292935582501889440687945449707912114732765199287448146933) * 10 ^ 70 +
        0883044625708209621345023896949678093537868960049337106467251475110676) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (411 - x)) = _
  rw [show 412 = 69 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 12 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (412 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (412 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_412 :
    recurrence4Scalar1First.coeff 412 =
      ((((405633917461658529955106442537298888721876050988260 * 10 ^ 70 +
        6257194225674942751135934100848406812589047858396635543794544940356708) * 10 ^ 70 +
        7390957701219051321351853312988387545724416797141841489728819012393827) * 10 ^ 70 +
        1229558685573845029953359347103678028825589066741295891755389239293519) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (412 - x)) = _
  rw [show 413 = 70 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 11 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (413 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (413 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_413 :
    recurrence4Scalar1First.coeff 413 =
      -((((175129248352031950367568626172171850928915623248721 * 10 ^ 70 +
        9323729360025516027638882802661668953405589468981055750737104427484301) * 10 ^ 70 +
        8303728918441634563239204852479786879912413781802739131557343299710762) * 10 ^ 70 +
        5871114376928745671420476601367723195428334033484824627494671584863767) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (413 - x)) = _
  rw [show 414 = 71 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 10 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (414 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (414 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_414 :
    recurrence4Scalar1First.coeff 414 =
      ((((71068665389949514774254619344485899375979720817465 * 10 ^ 70 +
        3111637039350829058054046948681500794727183244202171359731212521719991) * 10 ^ 70 +
        2770847764697588608509920474760194134993130960998318190966373292745943) * 10 ^ 70 +
        3165343465221690722454825095828938585059153075698182973773857612590818) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (414 - x)) = _
  rw [show 415 = 72 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 9 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (415 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (415 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_415 :
    recurrence4Scalar1First.coeff 415 =
      -((((27834010972262706447306443565527750713851726815993 * 10 ^ 70 +
        4133609007963615917467710303419079540270712710930483618766780123395516) * 10 ^ 70 +
        2696040407028547209898335527644601589311916863847932007139038705699973) * 10 ^ 70 +
        8950021746110710383200202247763509428473440492276431649674828212000784) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (415 - x)) = _
  rw [show 416 = 73 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 8 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (416 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (416 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_416 :
    recurrence4Scalar1First.coeff 416 =
      ((((10653112188201490388910657403193418904764698526092 * 10 ^ 70 +
        0612110698690949008501865573893788742986459144955735726696502003951116) * 10 ^ 70 +
        5308056587210227364645468210747603974288321514533590336392471957885177) * 10 ^ 70 +
        0842497298834312224078930171073431998457333750963793811236535539827378) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (416 - x)) = _
  rw [show 417 = 74 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 7 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (417 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (417 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_417 :
    recurrence4Scalar1First.coeff 417 =
      -((((4002859509429166695040939599159492825706589709259 * 10 ^ 70 +
        3481227222484025945627106683104168859787411790311966289481892026925077) * 10 ^ 70 +
        5769560478910099862368040303576388503218636237060475426569604787497709) * 10 ^ 70 +
        4931285865364798940893362528886445851591948272307119555214641417809227) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (417 - x)) = _
  rw [show 418 = 75 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 6 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (418 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (418 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_418 :
    recurrence4Scalar1First.coeff 418 =
      ((((1476118563612925448975140044625345148880346186120 * 10 ^ 70 +
        3933310222608179193026554143855234070286079965843832005176473390401412) * 10 ^ 70 +
        3082751439976855163773611764408144687744804335590214848706389799418353) * 10 ^ 70 +
        1899756070116663489074695764128763128769571882720214503484222078575637) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (418 - x)) = _
  rw [show 419 = 76 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 5 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (419 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (419 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_419 :
    recurrence4Scalar1First.coeff 419 =
      -((((532546780661737510224264188479387132480063730469 * 10 ^ 70 +
        2819087271139037001550995347824746800643383076558265203465190960967051) * 10 ^ 70 +
        5533560481734277587649504405380300235566348436113493594580882647409519) * 10 ^ 70 +
        1488000706519842988414620598101744853071426735076472369210396071926393) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (419 - x)) = _
  rw [show 420 = 77 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 4 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (420 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (420 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_420 :
    recurrence4Scalar1First.coeff 420 =
      ((((187112849634670669710045347961181346738007937296 * 10 ^ 70 +
        1527235723999603459510087300264916719232134010882367529520785873928107) * 10 ^ 70 +
        5318542909321838203270407022891920225746276688190440127581402107129491) * 10 ^ 70 +
        9396116421564469112899803386568638689148028235025784665207760682111662) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (420 - x)) = _
  rw [show 421 = 78 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 3 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (421 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (421 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_421 :
    recurrence4Scalar1First.coeff 421 =
      -((((63702355301096879307293242674104702974047304586 * 10 ^ 70 +
        2189859477735125343932496233115402666691905230304474247774730783343492) * 10 ^ 70 +
        6238393883261825228990307175905195964741283177366025028708439281983611) * 10 ^ 70 +
        5333534936561251204821483599877389342653417353469474104284858685847814) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (421 - x)) = _
  rw [show 422 = 79 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 2 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (422 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (422 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_422 :
    recurrence4Scalar1First.coeff 422 =
      ((((20903874329547241551944477327373204386858295987 * 10 ^ 70 +
        7639778737365994564809643393999002780174397265545545109780657600427627) * 10 ^ 70 +
        0576670603025791184416795136359306972836415343396963965323987304969569) * 10 ^ 70 +
        1984251044102986328033610785066826533091749347192295708461225691260931) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (422 - x)) = _
  rw [show 423 = 80 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 1 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (423 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (423 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_423 :
    recurrence4Scalar1First.coeff 423 =
      -((((6574931811378281647287150358130890759458684964 * 10 ^ 70 +
        2644728759879814005306634316018057674089370833134505757886843782808686) * 10 ^ 70 +
        0957051248550719409674419624413264148886686746761880617575433166937306) * 10 ^ 70 +
        5379540712464073059522640782462244013888934855222229250599461691385365) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (423 - x)) = _
  rw [show 424 = 81 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (424 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (424 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_424 :
    recurrence4Scalar1First.coeff 424 =
      ((((1969408069649551648669760350322372556059481701 * 10 ^ 70 +
        7457321776674618216754865223112037122471871356004901198536798706950343) * 10 ^ 70 +
        0628949785018180332918100174176348607634244294087994802161048368695354) * 10 ^ 70 +
        7684468788492534130736881286340706758568735339831459935338028642328335) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (424 - x)) = _
  rw [show 425 = 82 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 31 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (425 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (425 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_425 :
    recurrence4Scalar1First.coeff 425 =
      -((((556993050167933241975068705441896131132744936 * 10 ^ 70 +
        7874025919768391511892391673726626029342757745222840684741696779943335) * 10 ^ 70 +
        4879995749888719256801526529517725346394468102677265448383214406899683) * 10 ^ 70 +
        6866683335767896737008278033354764573596503529890106678596197851808715) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (425 - x)) = _
  rw [show 426 = 83 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 30 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (426 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (426 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_426 :
    recurrence4Scalar1First.coeff 426 =
      ((((146818243655961183929081422081159288334296316 * 10 ^ 70 +
        1232793750179516738566177621066918319901299315189813460958490334872471) * 10 ^ 70 +
        7028427543965112671030972013545318661955081735247541668186706943588746) * 10 ^ 70 +
        0276433936169911095187710135509397277941009065668364790512493812847076) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (426 - x)) = _
  rw [show 427 = 84 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 29 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (427 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (427 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_427 :
    recurrence4Scalar1First.coeff 427 =
      -((((35241793777768178260823436641252756735768406 * 10 ^ 70 +
        2259808898090659142176180203951696777790485574783715026061855339877771) * 10 ^ 70 +
        0446204906840038030225491585500861297434379932996907671828241395976807) * 10 ^ 70 +
        8690893496861929865666039025171121890083560730701544563293992041661860) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (427 - x)) = _
  rw [show 428 = 85 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 28 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (428 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (428 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_428 :
    recurrence4Scalar1First.coeff 428 =
      ((((7325061108222872675037770520055189708283993 * 10 ^ 70 +
        5807302855314584089624889951576483985685278119344422509335845781324231) * 10 ^ 70 +
        2032762213538020225009186279631056851644701748260096917996736362637626) * 10 ^ 70 +
        3323458566730419172708948740876950078136155823339629447982376322543370) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (428 - x)) = _
  rw [show 429 = 86 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 27 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (429 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (429 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_429 :
    recurrence4Scalar1First.coeff 429 =
      -((((1130004530642996826581922239117057477063746 * 10 ^ 70 +
        3564265967269146680637668517209474866626395314879361943436831207812383) * 10 ^ 70 +
        4774013190024858324426789873932875597446292154805267664378242422861012) * 10 ^ 70 +
        5488696314079257376469923623659357150203392793859860516326568092267992) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (429 - x)) = _
  rw [show 430 = 87 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 26 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (430 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (430 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_430 :
    recurrence4Scalar1First.coeff 430 =
      ((((21053159365973591235619219175767840491349 * 10 ^ 70 +
        6335475446623151487780580733072541228141212595651040009417615719950922) * 10 ^ 70 +
        9725109152225720311987235096160575099802467396423817091132733968759946) * 10 ^ 70 +
        4669404413082969540221680011944962880406000894933604329615817666811707) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (430 - x)) = _
  rw [show 431 = 88 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 25 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (431 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (431 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_431 :
    recurrence4Scalar1First.coeff 431 =
      ((((79599620568323515975148767013230774199049 * 10 ^ 70 +
        9502493399342054907121272448589060601860189957479814247313628706733997) * 10 ^ 70 +
        1151765277197106308599427188146878363970352087917324862514098139665005) * 10 ^ 70 +
        2260084616645496212734756360397814449279092543928143419367725043245799) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (431 - x)) = _
  rw [show 432 = 89 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 24 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (432 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (432 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_432 :
    recurrence4Scalar1First.coeff 432 =
      -((((44671674980263173513733185486935342783545 * 10 ^ 70 +
        9381185907282987752361044073798624666566161192986342912371165627309212) * 10 ^ 70 +
        3043269643145482557647032966017402695487434106821007120634159206121337) * 10 ^ 70 +
        4868800498700953537236501411222313976546167961514819607211384815982394) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (432 - x)) = _
  rw [show 433 = 90 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 23 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
