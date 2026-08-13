/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart2Simp
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
  recurrence4C1_coeff_1
  recurrence4C1_coeff_10
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
  recurrence4C1_coeff_11
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
  recurrence4C1_coeff_12
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
  recurrence4C1_coeff_13
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
  recurrence4C1_coeff_2
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21

attribute [local simp]
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_3
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
  recurrence4C1_coeff_4
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
  recurrence4C1_coeff_5
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
  recurrence4C1_coeff_6
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
  recurrence4C1_coeff_7
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
  recurrence4C1_coeff_8

attribute [local simp]
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
  recurrence4C1_coeff_9
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
  recurrence4ExceptionalProduct_coeff_123
  recurrence4ExceptionalProduct_coeff_124
  recurrence4ExceptionalProduct_coeff_125
  recurrence4ExceptionalProduct_coeff_126
  recurrence4ExceptionalProduct_coeff_127
  recurrence4ExceptionalProduct_coeff_128
  recurrence4ExceptionalProduct_coeff_129
  recurrence4ExceptionalProduct_coeff_130
  recurrence4ExceptionalProduct_coeff_131
  recurrence4ExceptionalProduct_coeff_132
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139
  recurrence4ExceptionalProduct_coeff_140
  recurrence4ExceptionalProduct_coeff_141
  recurrence4ExceptionalProduct_coeff_142
  recurrence4ExceptionalProduct_coeff_143
  recurrence4ExceptionalProduct_coeff_144
  recurrence4ExceptionalProduct_coeff_145
  recurrence4ExceptionalProduct_coeff_146
  recurrence4ExceptionalProduct_coeff_147
  recurrence4ExceptionalProduct_coeff_148
  recurrence4ExceptionalProduct_coeff_149
  recurrence4ExceptionalProduct_coeff_150
  recurrence4ExceptionalProduct_coeff_151
  recurrence4ExceptionalProduct_coeff_152
  recurrence4ExceptionalProduct_coeff_153
  recurrence4ExceptionalProduct_coeff_154
  recurrence4ExceptionalProduct_coeff_155
  recurrence4ExceptionalProduct_coeff_156
  recurrence4ExceptionalProduct_coeff_157
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_160
  recurrence4ExceptionalProduct_coeff_161
  recurrence4ExceptionalProduct_coeff_162
  recurrence4ExceptionalProduct_coeff_163
  recurrence4ExceptionalProduct_coeff_164
  recurrence4ExceptionalProduct_coeff_165

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_166
  recurrence4ExceptionalProduct_coeff_167
  recurrence4ExceptionalProduct_coeff_168
  recurrence4ExceptionalProduct_coeff_169
  recurrence4ExceptionalProduct_coeff_170
  recurrence4ExceptionalProduct_coeff_171
  recurrence4ExceptionalProduct_coeff_172
  recurrence4ExceptionalProduct_coeff_173
  recurrence4ExceptionalProduct_coeff_174
  recurrence4ExceptionalProduct_coeff_175
  recurrence4ExceptionalProduct_coeff_176
  recurrence4ExceptionalProduct_coeff_177
  recurrence4ExceptionalProduct_coeff_178
  recurrence4ExceptionalProduct_coeff_179
  recurrence4ExceptionalProduct_coeff_180
  recurrence4ExceptionalProduct_coeff_181
  recurrence4ExceptionalProduct_coeff_182
  recurrence4ExceptionalProduct_coeff_183
  recurrence4ExceptionalProduct_coeff_184
  recurrence4ExceptionalProduct_coeff_185
  recurrence4ExceptionalProduct_coeff_186
  recurrence4ExceptionalProduct_coeff_187
  recurrence4ExceptionalProduct_coeff_188
  recurrence4ExceptionalProduct_coeff_189
  recurrence4ExceptionalProduct_coeff_190
  recurrence4ExceptionalProduct_coeff_191
  recurrence4ExceptionalProduct_coeff_192
  recurrence4ExceptionalProduct_coeff_193
  recurrence4ExceptionalProduct_coeff_194
  recurrence4ExceptionalProduct_coeff_195
  recurrence4ExceptionalProduct_coeff_196
  recurrence4ExceptionalProduct_coeff_197
  recurrence4ExceptionalProduct_coeff_198
  recurrence4ExceptionalProduct_coeff_199
  recurrence4ExceptionalProduct_coeff_200
  recurrence4ExceptionalProduct_coeff_201
  recurrence4ExceptionalProduct_coeff_202
  recurrence4ExceptionalProduct_coeff_203
  recurrence4ExceptionalProduct_coeff_204
  recurrence4ExceptionalProduct_coeff_205
  recurrence4ExceptionalProduct_coeff_206
  recurrence4ExceptionalProduct_coeff_207
  recurrence4ExceptionalProduct_coeff_208
  recurrence4ExceptionalProduct_coeff_209
  recurrence4ExceptionalProduct_coeff_210
  recurrence4ExceptionalProduct_coeff_211
  recurrence4ExceptionalProduct_coeff_212
  recurrence4ExceptionalProduct_coeff_213
  recurrence4ExceptionalProduct_coeff_214
  recurrence4ExceptionalProduct_coeff_215
  recurrence4ExceptionalProduct_coeff_216
  recurrence4ExceptionalProduct_coeff_217
  recurrence4ExceptionalProduct_coeff_218
  recurrence4ExceptionalProduct_coeff_219
  recurrence4ExceptionalProduct_coeff_220
  recurrence4ExceptionalProduct_coeff_221
  recurrence4ExceptionalProduct_coeff_222
  recurrence4ExceptionalProduct_coeff_223
  recurrence4ExceptionalProduct_coeff_224
  recurrence4ExceptionalProduct_coeff_225
  recurrence4ExceptionalProduct_coeff_226
  recurrence4ExceptionalProduct_coeff_227
  recurrence4ExceptionalProduct_coeff_228
  recurrence4ExceptionalProduct_coeff_229

attribute [local simp]
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

attribute [local simp]
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
  recurrence4ExceptionalProduct_coeff_354
  recurrence4ExceptionalProduct_coeff_355
  recurrence4ExceptionalProduct_coeff_356
  recurrence4ExceptionalProduct_coeff_357

attribute [local simp]
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

private theorem recurrence4Scalar1Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (360 + x) *
        remainder6Coefficient1.coeff (360 - (360 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 360 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (360 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (360 - (360 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_360 :
    recurrence4Scalar1Exceptional.coeff 360 =
      -(((((9338 * 10 ^ 70 +
        3261254314628054523021829557110196966750550057293192522769364739612186) * 10 ^ 70 +
        8310327363483544705881590126530024630876934343909808514164284026840074) * 10 ^ 70 +
        9256095209076598469846314005563918024396934472658396646016602089172793) * 10 ^ 70 +
        9533427029520305650079858446883736472397384314884034660743374795620946) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (360 - x)) = _
  rw [show 361 = 211 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (361 + x) *
        remainder6Coefficient1.coeff (361 - (361 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 361 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (361 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (361 - (361 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_361 :
    recurrence4Scalar1Exceptional.coeff 361 =
      (((((3233 * 10 ^ 70 +
        2874210103881027202435304172486999140522753686800794834093130427224629) * 10 ^ 70 +
        6955715443984568546916196254241761558777276705273247687643812471933075) * 10 ^ 70 +
        0280608966501642660892481681576182888568259484256220418585513546888178) * 10 ^ 70 +
        9929899691360070199697754920959883790443390776543396369806393848644640) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (361 - x)) = _
  rw [show 362 = 212 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (362 + x) *
        remainder6Coefficient1.coeff (362 - (362 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 362 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (362 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (362 - (362 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_362 :
    recurrence4Scalar1Exceptional.coeff 362 =
      -(((((1063 * 10 ^ 70 +
        5249056201281744760275717010896938634479590212223120835382222038239118) * 10 ^ 70 +
        1323221366865851445301278645897570206584945349206828486888072110298191) * 10 ^ 70 +
        2720687165390902890041305433567684750193409268773753376808211137991309) * 10 ^ 70 +
        7824829457818677613808078215990115921414450976275516421436633742651690) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (362 - x)) = _
  rw [show 363 = 213 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (363 + x) *
        remainder6Coefficient1.coeff (363 - (363 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 363 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (363 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (363 - (363 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_363 :
    recurrence4Scalar1Exceptional.coeff 363 =
      (((((326 * 10 ^ 70 +
        2025582543476069575931930355015581854831193984081890350188596356066913) * 10 ^ 70 +
        6722033192139229516541136419497651498555966850403567666338674439311511) * 10 ^ 70 +
        7721795513803744628444009714720029902814352530872333141472114707397191) * 10 ^ 70 +
        2610904834625079692251189722910848274658588102428057854799991462315045) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (363 - x)) = _
  rw [show 364 = 214 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (364 + x) *
        remainder6Coefficient1.coeff (364 - (364 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 364 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (364 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (364 - (364 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_364 :
    recurrence4Scalar1Exceptional.coeff 364 =
      -(((((89 * 10 ^ 70 +
        5510138895895699561640806266743409114250294054727159921425966696399820) * 10 ^ 70 +
        7323268306238071928567036198930738148200508883728122747792734705553379) * 10 ^ 70 +
        3290337871432009694642902365599699135736323252270760944480287827937228) * 10 ^ 70 +
        5534715584505578378486114263528814656995980157896655032913652308697441) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (364 - x)) = _
  rw [show 365 = 215 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (365 + x) *
        remainder6Coefficient1.coeff (365 - (365 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 365 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (365 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (365 - (365 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_365 :
    recurrence4Scalar1Exceptional.coeff 365 =
      (((((19 * 10 ^ 70 +
        5325134345780802259849257304341058374711823886251328758199945287267524) * 10 ^ 70 +
        3193805410022875561909885305412865121647881236862705230441964498249422) * 10 ^ 70 +
        8994589320383403692715072260644332917204908272082804259607195847663610) * 10 ^ 70 +
        7564588044708827458933564989162347807085621921130152319621749474874741) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (365 - x)) = _
  rw [show 366 = 216 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (366 + x) *
        remainder6Coefficient1.coeff (366 - (366 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 366 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (366 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (366 - (366 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_366 :
    recurrence4Scalar1Exceptional.coeff 366 =
      -(((((1 * 10 ^ 70 +
        5128743315695287713186368569607847553104734850984514545839318544733238) * 10 ^ 70 +
        5566773276648736786958341400747604323902836923812983233584144518972657) * 10 ^ 70 +
        0939455256300665367624253854943671232711897177353676404095983836613315) * 10 ^ 70 +
        3539265449626840701484939590754562872750869874615410904351376087105703) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (366 - x)) = _
  rw [show 367 = 217 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (367 + x) *
        remainder6Coefficient1.coeff (367 - (367 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 367 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (367 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (367 - (367 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_367 :
    recurrence4Scalar1Exceptional.coeff 367 =
      -(((((1 * 10 ^ 70 +
        7796832809661783847714579448735735517376209843099687846041355565111358) * 10 ^ 70 +
        7459599795620751968127381267911769186695313691905600050535830326777902) * 10 ^ 70 +
        5839851135007745284361198683837527809042181781033712836330187733334470) * 10 ^ 70 +
        0445870928862988515864099491404757144933836561258226087751573321475979) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (367 - x)) = _
  rw [show 368 = 218 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (368 + x) *
        remainder6Coefficient1.coeff (368 - (368 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 368 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (368 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (368 - (368 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_368 :
    recurrence4Scalar1Exceptional.coeff 368 =
      (((((1 * 10 ^ 70 +
        6004845870171700904850279026247375560859055817785568484024066045202399) * 10 ^ 70 +
        3995591748570273112208135796693612865655083851281976356218052451535252) * 10 ^ 70 +
        8916843113738174091558420933085087577774854130798703319839323349361591) * 10 ^ 70 +
        3402989592753341141620469367857974823094121997901004666264395935296103) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (368 - x)) = _
  rw [show 369 = 219 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (369 + x) *
        remainder6Coefficient1.coeff (369 - (369 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 369 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (369 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (369 - (369 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_369 :
    recurrence4Scalar1Exceptional.coeff 369 =
      -((((9673735015895763794632328272203612405270846227820966138073634843822976 * 10 ^ 70 +
        2049108783558268270207866713731327661269715578942194610041372565953074) * 10 ^ 70 +
        0732664115778743503476385214194962824072582260766534087560581492504446) * 10 ^ 70 +
        4462129441393284945401573933438415271331950723178873658703164155274414) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (369 - x)) = _
  rw [show 370 = 220 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (370 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (370 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_370 :
    recurrence4Scalar1Exceptional.coeff 370 =
      ((((5060295351764261427115721359061479645209915341772905547136019275992204 * 10 ^ 70 +
        8442783638669295920761111449853293157219898414232487344229264670168633) * 10 ^ 70 +
        5538734989504458187514829822757808664449809407491691780364741932345929) * 10 ^ 70 +
        8712719440515873642454626239925172004044942907564060839527926579269663) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (370 - x)) = _
  rw [show 371 = 221 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (371 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (371 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_371 :
    recurrence4Scalar1Exceptional.coeff 371 =
      -((((2450400881246336126743943643431664173417710899428042033916140698749456 * 10 ^ 70 +
        9946199170780872530248039448937928500110627772608352060491247081088076) * 10 ^ 70 +
        0473670923988825520531427804804183406877470439457645536384787950750827) * 10 ^ 70 +
        9432766920223989460841533382753035690463352239730442219543622464658801) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (371 - x)) = _
  rw [show 372 = 222 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 20 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (372 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (372 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_372 :
    recurrence4Scalar1Exceptional.coeff 372 =
      ((((1128374236491658342061114212005907551418260129795465043282151805073601 * 10 ^ 70 +
        7510777008297573843917174816036828269706340488565291171650962807088257) * 10 ^ 70 +
        9682262072898298983269795295882784257377153683906687043768220423865471) * 10 ^ 70 +
        8160709174987997845208596579433932344034156464304783448875984192709744) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (372 - x)) = _
  rw [show 373 = 223 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 19 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (373 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (373 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_373 :
    recurrence4Scalar1Exceptional.coeff 373 =
      -((((500201204403585630359838139518939424883766000400478289888301618757444 * 10 ^ 70 +
        7546249909292678433312651975514256414816859550055347068716537243890618) * 10 ^ 70 +
        3145020542686121055295930183164361346441962085704570834161674001172990) * 10 ^ 70 +
        2033403573956889733330340905907866098571223608424349843581209981879866) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (373 - x)) = _
  rw [show 374 = 224 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 18 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (374 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (374 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_374 :
    recurrence4Scalar1Exceptional.coeff 374 =
      ((((214626093688518059438017211451530616657489872125541398892544544249912 * 10 ^ 70 +
        4576067261154120758273474806685402033542399263019988723370754003801915) * 10 ^ 70 +
        3196748643701608694902520570804552519985173925887817191893154037455573) * 10 ^ 70 +
        6706808140254365787714717351658378087401531468193980452257485958522363) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (374 - x)) = _
  rw [show 375 = 225 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 17 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (375 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (375 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_375 :
    recurrence4Scalar1Exceptional.coeff 375 =
      -((((89299701045799645013895468969660524328668125271682754989055872290012 * 10 ^ 70 +
        2989095564442020552645489084930162456059773195897549406215503093909614) * 10 ^ 70 +
        1615003906534050443274040385126199024847295611649731582823265139404696) * 10 ^ 70 +
        8586347043146032292818735347335464887615979352652456692000845036850997) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (375 - x)) = _
  rw [show 376 = 226 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 16 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (376 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (376 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_376 :
    recurrence4Scalar1Exceptional.coeff 376 =
      ((((36014924033741463364435427390356483301658719124580542689601701568791 * 10 ^ 70 +
        4377557690453167106962876169440487961064199880597698931588614237843762) * 10 ^ 70 +
        2597430390390391864474383729783932968183376711755192631669864644334666) * 10 ^ 70 +
        3435890922387900843970758173151993729554340617622586746181429715970754) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (376 - x)) = _
  rw [show 377 = 227 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 15 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (377 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (377 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_377 :
    recurrence4Scalar1Exceptional.coeff 377 =
      -((((14053253501468797426241601724513341651014841574569634773220900379381 * 10 ^ 70 +
        4864380470454688229279859565939545569018529639552395446388733961060342) * 10 ^ 70 +
        6990017508230490798738310403025295109312089891194811356287447274808301) * 10 ^ 70 +
        6760413150722463550932057366422804461097395771445641817185323899321181) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (377 - x)) = _
  rw [show 378 = 228 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 14 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (378 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (378 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_378 :
    recurrence4Scalar1Exceptional.coeff 378 =
      ((((5289420272725199184226421489904075992044184223183230667215659746936 * 10 ^ 70 +
        8975722493132312838108676238438280154450807757839784187838963782160650) * 10 ^ 70 +
        5253189455069377848246083646042519772625227887876599739842909934957400) * 10 ^ 70 +
        4384528097780627009770820349876646828331567998087103254796062370511412) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (378 - x)) = _
  rw [show 379 = 229 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 13 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (379 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (379 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_379 :
    recurrence4Scalar1Exceptional.coeff 379 =
      -((((1912017810631492468323058372591987731642076648082403539931707620080 * 10 ^ 70 +
        6273807964601144064329395014748613100369854905811501311217489682645839) * 10 ^ 70 +
        7406009621769920956495864647697609736729792913783295007246367062457459) * 10 ^ 70 +
        9491088791073373212520388204475895338171533311658300068768500749433490) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (379 - x)) = _
  rw [show 380 = 230 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 12 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (380 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (380 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_380 :
    recurrence4Scalar1Exceptional.coeff 380 =
      ((((659734121039728085180097221952101661336647704624497346323990998735 * 10 ^ 70 +
        1188998150132435118925782612491729617728755550989358440527050048878806) * 10 ^ 70 +
        0737536064283986820689901586774929977113471751937943572997911743070950) * 10 ^ 70 +
        4459554628328935814539740938716358198790557948944846812812386611537137) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (380 - x)) = _
  rw [show 381 = 231 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 11 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (381 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (381 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_381 :
    recurrence4Scalar1Exceptional.coeff 381 =
      -((((215319689293408322001758653740023008124377095802080510214547200234 * 10 ^ 70 +
        3584005357379339135248089170966200370483713270102387077009161333282830) * 10 ^ 70 +
        8849344127181712224775288812480393377417500255841415470113801310724236) * 10 ^ 70 +
        4737136135391745735981421797860706551768489271017424201768839561925383) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (381 - x)) = _
  rw [show 382 = 232 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 10 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (382 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (382 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_382 :
    recurrence4Scalar1Exceptional.coeff 382 =
      ((((65490488871895209253048086667787864506020495951695019152158882907 * 10 ^ 70 +
        1589160243980865769373071388437149788723598917945921228309087443025178) * 10 ^ 70 +
        3556095096093366551183209434852477485560008741546849347421350915746429) * 10 ^ 70 +
        8910078003939086557890000724332326231024309016025536666425337499648759) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (382 - x)) = _
  rw [show 383 = 233 +
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 9 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
