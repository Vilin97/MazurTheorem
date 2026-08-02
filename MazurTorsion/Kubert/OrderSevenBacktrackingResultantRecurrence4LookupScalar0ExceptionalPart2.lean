/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C0_coeff_1
  recurrence4C0_coeff_10
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
  recurrence4C0_coeff_11
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
  recurrence4C0_coeff_12
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
  recurrence4C0_coeff_13
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

attribute [local simp]
  recurrence4C0_coeff_19
  recurrence4C0_coeff_2
  recurrence4C0_coeff_20
  recurrence4C0_coeff_21
  recurrence4C0_coeff_22
  recurrence4C0_coeff_23
  recurrence4C0_coeff_24
  recurrence4C0_coeff_25
  recurrence4C0_coeff_26
  recurrence4C0_coeff_27
  recurrence4C0_coeff_28
  recurrence4C0_coeff_29
  recurrence4C0_coeff_3
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
  recurrence4C0_coeff_4
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
  recurrence4C0_coeff_5
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
  recurrence4C0_coeff_6
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
  recurrence4C0_coeff_7
  recurrence4C0_coeff_70
  recurrence4C0_coeff_71
  recurrence4C0_coeff_72
  recurrence4C0_coeff_73
  recurrence4C0_coeff_74
  recurrence4C0_coeff_75
  recurrence4C0_coeff_76

attribute [local simp]
  recurrence4C0_coeff_77
  recurrence4C0_coeff_78
  recurrence4C0_coeff_79
  recurrence4C0_coeff_8
  recurrence4C0_coeff_80
  recurrence4C0_coeff_81
  recurrence4C0_coeff_82
  recurrence4C0_coeff_83
  recurrence4C0_coeff_84
  recurrence4C0_coeff_85
  recurrence4C0_coeff_86
  recurrence4C0_coeff_87
  recurrence4C0_coeff_88
  recurrence4C0_coeff_89
  recurrence4C0_coeff_9
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
  recurrence4ExceptionalProduct_coeff_119
  recurrence4ExceptionalProduct_coeff_120
  recurrence4ExceptionalProduct_coeff_121
  recurrence4ExceptionalProduct_coeff_122
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_160
  recurrence4ExceptionalProduct_coeff_161
  recurrence4ExceptionalProduct_coeff_162
  recurrence4ExceptionalProduct_coeff_163
  recurrence4ExceptionalProduct_coeff_164
  recurrence4ExceptionalProduct_coeff_165
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_222
  recurrence4ExceptionalProduct_coeff_223
  recurrence4ExceptionalProduct_coeff_224
  recurrence4ExceptionalProduct_coeff_225
  recurrence4ExceptionalProduct_coeff_226
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

attribute [local simp]
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
  recurrence4ExceptionalProduct_coeff_346
  recurrence4ExceptionalProduct_coeff_347
  recurrence4ExceptionalProduct_coeff_348
  recurrence4ExceptionalProduct_coeff_349

attribute [local simp]
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

private theorem recurrence4Scalar0Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (272 + x) *
        remainder6Coefficient0.coeff (272 - (272 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 272 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (272 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (272 - (272 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_272 :
    recurrence4Scalar0Exceptional.coeff 272 =
      (((((22489324879589881609165458651 * 10 ^ 70 +
        9356043914745825236416938156298439886315945713298290530996264440637998) * 10 ^ 70 +
        9858690443907859501345995087439641390197428317754749582507394503446671) * 10 ^ 70 +
        7308762410536588249806766703027147373094156950412610110430653783387576) * 10 ^ 70 +
        9825586969911661374689409707805419499430555395386415910235969220408505) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (272 - x)) = _
  rw [show 273 = 119 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (273 + x) *
        remainder6Coefficient0.coeff (273 - (273 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 273 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (273 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (273 - (273 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_273 :
    recurrence4Scalar0Exceptional.coeff 273 =
      -(((((19129468261696974690965360052 * 10 ^ 70 +
        3409577510751409399099546036670122636323059308965448160331133004957715) * 10 ^ 70 +
        4179030366769411842516586777278394354195728286641620307471144095498999) * 10 ^ 70 +
        5715265469243639139473018157603107404245977729716801064464331235747683) * 10 ^ 70 +
        8125076869339672952797101757330704332516288314004775809556855477238061) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (273 - x)) = _
  rw [show 274 = 120 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (274 + x) *
        remainder6Coefficient0.coeff (274 - (274 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 274 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (274 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (274 - (274 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_274 :
    recurrence4Scalar0Exceptional.coeff 274 =
      (((((16060096512943871814715860848 * 10 ^ 70 +
        6006278006718647042529802481973618263434888885691893535988182795139628) * 10 ^ 70 +
        5996012140763943684531972604698230402338620144083597577762295322219716) * 10 ^ 70 +
        5692774069831670800676520569687864323670329726244666054564453660494472) * 10 ^ 70 +
        4527394163659961878730817944383119987117070715648975845942059686408971) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (274 - x)) = _
  rw [show 275 = 121 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (275 + x) *
        remainder6Coefficient0.coeff (275 - (275 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 275 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (275 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (275 - (275 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_275 :
    recurrence4Scalar0Exceptional.coeff 275 =
      -(((((13307513908237332960871651463 * 10 ^ 70 +
        4865213539260753210009729855544224722541757578794878436468463121250198) * 10 ^ 70 +
        1576137387215986994139735170057325356039150521268521766928289324515891) * 10 ^ 70 +
        2629931696092403263862060624964238003642443347480728653262632248994367) * 10 ^ 70 +
        3579379198581035430215437583882739858909915598962977267782256475323261) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (275 - x)) = _
  rw [show 276 = 122 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (276 + x) *
        remainder6Coefficient0.coeff (276 - (276 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 276 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (276 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (276 - (276 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_276 :
    recurrence4Scalar0Exceptional.coeff 276 =
      (((((10882573330553662125506572746 * 10 ^ 70 +
        5435629604821111506104246055790582742783192172723711672952935722156961) * 10 ^ 70 +
        5541380970015459590581448509298530871316696570036683725143819471527018) * 10 ^ 70 +
        0838223818372901204144920533315402432634137235317841686063549685063434) * 10 ^ 70 +
        8198932018986074847271928850909004896276322674478743878721862989659488) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (276 - x)) = _
  rw [show 277 = 123 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (277 + x) *
        remainder6Coefficient0.coeff (277 - (277 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 277 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (277 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (277 - (277 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_277 :
    recurrence4Scalar0Exceptional.coeff 277 =
      -(((((8782774894398333308968519904 * 10 ^ 70 +
        2920659768555546037784108871444301335804435751211053805355278044270987) * 10 ^ 70 +
        9958567572677968364084775929148716934931325250714142498837674523316812) * 10 ^ 70 +
        6613010145380264772176411601333819019322449466065117220220579474270397) * 10 ^ 70 +
        1005431785970458937880161081768404975512595817587164893775845119857191) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (277 - x)) = _
  rw [show 278 = 124 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (278 + x) *
        remainder6Coefficient0.coeff (278 - (278 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 278 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (278 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (278 - (278 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_278 :
    recurrence4Scalar0Exceptional.coeff 278 =
      (((((6994773790274364887351077364 * 10 ^ 70 +
        2218358955004705008113489145746592946205577369101627292599797468610023) * 10 ^ 70 +
        8363475498940508370825122270621541811880158883871570070167602774705332) * 10 ^ 70 +
        3495545339766571423361256315280770655738233468723555599271014458371307) * 10 ^ 70 +
        1139469950103188340171392295808173707733412816280391885700454390955153) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (278 - x)) = _
  rw [show 279 = 125 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (279 + x) *
        remainder6Coefficient0.coeff (279 - (279 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 279 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (279 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (279 - (279 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_279 :
    recurrence4Scalar0Exceptional.coeff 279 =
      -(((((5497051210711192207817184838 * 10 ^ 70 +
        3970553481758933838234686712026420330871728177947073105539852035113318) * 10 ^ 70 +
        7530160933786350445115429268613523888736482696646798180853967276493641) * 10 ^ 70 +
        9487427415658847747852437031344254549306946019517241986632616024204429) * 10 ^ 70 +
        5309097318729676234172366060929992537910559343347510360719878742217108) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (279 - x)) = _
  rw [show 280 = 126 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (280 + x) *
        remainder6Coefficient0.coeff (280 - (280 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 280 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (280 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (280 - (280 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_280 :
    recurrence4Scalar0Exceptional.coeff 280 =
      (((((4262534219795976618424375962 * 10 ^ 70 +
        4810672295377280638720449250579004622514351649655038878751600129756083) * 10 ^ 70 +
        8333710394757128630894226267050516073697219976376482569995626880934537) * 10 ^ 70 +
        0789058617373195239038615117349121846956124684903948010172851142214324) * 10 ^ 70 +
        0324213590690169274255133988302363975821122864387876961127357615188360) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (280 - x)) = _
  rw [show 281 = 127 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (281 + x) *
        remainder6Coefficient0.coeff (281 - (281 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 281 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (281 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (281 - (281 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_281 :
    recurrence4Scalar0Exceptional.coeff 281 =
      -(((((3260995905856227826690583079 * 10 ^ 70 +
        9883897424960717854146296621500322553046607805905680945969179130621478) * 10 ^ 70 +
        4388327210411433210313676922117402478897785018267216719358406452846779) * 10 ^ 70 +
        4394035515178169143879939700659034413447230625535540404528830265147919) * 10 ^ 70 +
        0834017833506279214832204794279787629857522988857428577818407066554757) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (281 - x)) = _
  rw [show 282 = 128 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (282 + x) *
        remainder6Coefficient0.coeff (282 - (282 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 282 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (282 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (282 - (282 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_282 :
    recurrence4Scalar0Exceptional.coeff 282 =
      (((((2461118884230616280910941668 * 10 ^ 70 +
        6018826984777001118298899180952212115469767175953321731154830683462887) * 10 ^ 70 +
        4231117361213477139287351883406974735142998507384041336163979666227605) * 10 ^ 70 +
        9208836835757331008629211122662012538019384209892889830562773557617315) * 10 ^ 70 +
        8413665734163023355955331876037841001249565584662225100861674398922101) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (282 - x)) = _
  rw [show 283 = 129 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (283 + x) *
        remainder6Coefficient0.coeff (283 - (283 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 283 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (283 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (283 - (283 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_283 :
    recurrence4Scalar0Exceptional.coeff 283 =
      -(((((1832156690940788767199892764 * 10 ^ 70 +
        1046865536506915321438062835725940250726247561723982466423302141676098) * 10 ^ 70 +
        7699456698251513441084613391481055110278064238950821450897181260740410) * 10 ^ 70 +
        3926731050175200490151453293862982969433186119195513205176600982059487) * 10 ^ 70 +
        1711821021232436904654913262280769016823411170545212837272833613811932) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (283 - x)) = _
  rw [show 284 = 130 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (284 + x) *
        remainder6Coefficient0.coeff (284 - (284 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 284 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (284 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (284 - (284 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_284 :
    recurrence4Scalar0Exceptional.coeff 284 =
      (((((1345173703313058476736908265 * 10 ^ 70 +
        3710264524579037266256186461040124252275467543572263846160903655841195) * 10 ^ 70 +
        8989764756401729912485373214598053863450717769113836411346732395602411) * 10 ^ 70 +
        9473870840142405900396600254217225863862112562967477263559526480699391) * 10 ^ 70 +
        8640651801702706720871969677307706284769598479264700278145098793751948) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (284 - x)) = _
  rw [show 285 = 131 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (285 + x) *
        remainder6Coefficient0.coeff (285 - (285 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 285 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (285 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (285 - (285 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_285 :
    recurrence4Scalar0Exceptional.coeff 285 =
      -(((((973881527508504130082546735 * 10 ^ 70 +
        7411961211793654265888534188527484346139095218389464356202150781095792) * 10 ^ 70 +
        6759859178203763831012634365261677138423347807074597446403813765101722) * 10 ^ 70 +
        4447401081756317597230836647474736374769012080205221758853691579309133) * 10 ^ 70 +
        1266601685401917200645577939430730464581556457347148926529000955591211) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (285 - x)) = _
  rw [show 286 = 132 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (286 + x) *
        remainder6Coefficient0.coeff (286 - (286 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 286 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (286 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (286 - (286 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_286 :
    recurrence4Scalar0Exceptional.coeff 286 =
      (((((695116640216799791562943632 * 10 ^ 70 +
        5617408743840924643265565461289714756020587260699133982251224230406758) * 10 ^ 70 +
        0435223981191650055859809314565993823801113737385387240847802626240171) * 10 ^ 70 +
        8342306046681831639728381000728034098708692652499668783131126512568196) * 10 ^ 70 +
        4618714851111330825846045993185633571603479641476926957329008413235905) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (286 - x)) = _
  rw [show 287 = 133 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (287 + x) *
        remainder6Coefficient0.coeff (287 - (287 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 287 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (287 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (287 - (287 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_287 :
    recurrence4Scalar0Exceptional.coeff 287 =
      -(((((489020340895686472328392262 * 10 ^ 70 +
        6044959610206064050163239413990320086653962500438630621680118206383671) * 10 ^ 70 +
        8775731937411165711173945076450313306793407205640754531590850034210099) * 10 ^ 70 +
        9890680270143442409056801255952503190891780515130352480161206151106025) * 10 ^ 70 +
        9233045278491621231454062691925843196829440888241495651907729934494017) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (287 - x)) = _
  rw [show 288 = 134 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (288 + x) *
        remainder6Coefficient0.coeff (288 - (288 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 288 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (288 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (288 - (288 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_288 :
    recurrence4Scalar0Exceptional.coeff 288 =
      (((((338988825949007136860220687 * 10 ^ 70 +
        1309062519833809204796981452924033940720568134031185435331560204712475) * 10 ^ 70 +
        7664596957994539482994460216986644037047106773894246405844665020622216) * 10 ^ 70 +
        7941556327347683640207881135080242024861668750798098638068779070114176) * 10 ^ 70 +
        4962970277372318731530751527765480109823383682566179914631278003852440) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (288 - x)) = _
  rw [show 289 = 135 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (289 + x) *
        remainder6Coefficient0.coeff (289 - (289 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 289 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (289 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (289 - (289 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_289 :
    recurrence4Scalar0Exceptional.coeff 289 =
      -(((((231460262050818521119349474 * 10 ^ 70 +
        6505108861931222179197979359702640379611980082215064125975161298017666) * 10 ^ 70 +
        4300365218223093514170168543191740708139530703763884713613210356046070) * 10 ^ 70 +
        4173314614888092970439671505274742016557117934558573305034940461371989) * 10 ^ 70 +
        7051174648384023513409915667863292412945836832021220208080426918502112) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (289 - x)) = _
  rw [show 290 = 136 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (290 + x) *
        remainder6Coefficient0.coeff (290 - (290 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 290 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (290 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (290 - (290 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_290 :
    recurrence4Scalar0Exceptional.coeff 290 =
      (((((155599283236948089132808623 * 10 ^ 70 +
        7778261019432144612180063669129824182880833142947581355327179813603665) * 10 ^ 70 +
        4679827275798394541062026516460957555825274839347956246796887991005362) * 10 ^ 70 +
        2372980001598247825003994345540879387609461762811015054140082071807574) * 10 ^ 70 +
        4540501617217959194265717333985336327528530469135675607317750335030540) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (290 - x)) = _
  rw [show 291 = 137 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (291 + x) *
        remainder6Coefficient0.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 291 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (291 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (291 - (291 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_291 :
    recurrence4Scalar0Exceptional.coeff 291 =
      -(((((102929532317824262542363213 * 10 ^ 70 +
        0604829662131675919038494427198087948922702365012481928051605295783593) * 10 ^ 70 +
        2988791459246212809665217558654866126904618467620578948873614592753460) * 10 ^ 70 +
        2578573667690434454064833411554402290807146347064747423905946886319701) * 10 ^ 70 +
        1854275292711479775345875316457426318678393784464918869435174357292188) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (291 - x)) = _
  rw [show 292 = 138 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (292 + x) *
        remainder6Coefficient0.coeff (292 - (292 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 292 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (292 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (292 - (292 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_292 :
    recurrence4Scalar0Exceptional.coeff 292 =
      (((((66953621209051824355789032 * 10 ^ 70 +
        2508074372280785802365323396058981337169307580361020796232102881567364) * 10 ^ 70 +
        4768654351434534168668626315344252869082042516633224127704222853618980) * 10 ^ 70 +
        0954240021976392566148838049595257343576309582645522467644918121709816) * 10 ^ 70 +
        0537974196936124546640143962998016646183311982766977420060639003991307) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (292 - x)) = _
  rw [show 293 = 139 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (293 + x) *
        remainder6Coefficient0.coeff (293 - (293 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 293 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (293 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (293 - (293 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_293 :
    recurrence4Scalar0Exceptional.coeff 293 =
      -(((((42788700283497585799171985 * 10 ^ 70 +
        0487933013891721459809580986928058292308694614331267427104036026169923) * 10 ^ 70 +
        7750257826650095112200714564420484919503806559955805980166600571584073) * 10 ^ 70 +
        9358901317409010327309497039255401563366313350672192059451902886427111) * 10 ^ 70 +
        7620520492676591145984166107684931797012888578913799233065687083148677) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (293 - x)) = _
  rw [show 294 = 140 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (294 + x) *
        remainder6Coefficient0.coeff (294 - (294 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 294 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (294 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (294 - (294 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_294 :
    recurrence4Scalar0Exceptional.coeff 294 =
      (((((26835747006440298454566478 * 10 ^ 70 +
        2314901114949950642251050054306750483530565319489239568339042413534327) * 10 ^ 70 +
        8330178109653036389297627067363019561931914403712684754417987042219615) * 10 ^ 70 +
        4662301119569718902070449330237674573299652934572886558300938278187776) * 10 ^ 70 +
        1037728596480498753891713058883932641100777190965217132232691797208843) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (294 - x)) = _
  rw [show 295 = 141 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (295 + x) *
        remainder6Coefficient0.coeff (295 - (295 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 295 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (295 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (295 - (295 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_295 :
    recurrence4Scalar0Exceptional.coeff 295 =
      -(((((16492312226375052791282387 * 10 ^ 70 +
        5093625881088257175053363007772478613003978772029906119567774905373626) * 10 ^ 70 +
        9872835022506007729169718655431730370910983776550632252676928591873283) * 10 ^ 70 +
        9849171530787850009382481116635001372001796382903435110918825906023886) * 10 ^ 70 +
        0384052425517194031820385579885655488376263008436431909120816583254266) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (295 - x)) = _
  rw [show 296 = 142 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (296 + x) *
        remainder6Coefficient0.coeff (296 - (296 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 296 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (296 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (296 - (296 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_296 :
    recurrence4Scalar0Exceptional.coeff 296 =
      (((((9912031088391437444958295 * 10 ^ 70 +
        5938446432022468374195070239833247182802738813729375637919697640322586) * 10 ^ 70 +
        9851765946269478106911062519289990364318282938063463050196586428849315) * 10 ^ 70 +
        1779087669256322821374366987770134387823670612205816829144316033134427) * 10 ^ 70 +
        8585970719120566119407824612770754414519544618298829737498101060014060) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (296 - x)) = _
  rw [show 297 = 143 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (297 + x) *
        remainder6Coefficient0.coeff (297 - (297 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 297 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (297 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (297 - (297 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_297 :
    recurrence4Scalar0Exceptional.coeff 297 =
      -(((((5809669655453080565506635 * 10 ^ 70 +
        2913507450067707389933808416532376220320914705135618467419685651481960) * 10 ^ 70 +
        7380745521199427825298497214962890839047487760494672923842988774132503) * 10 ^ 70 +
        5274630764864256663296794209429888784891469908061205747782123642193730) * 10 ^ 70 +
        8381815644027938470395047085315742122977213215331563637321341176486173) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (297 - x)) = _
  rw [show 298 = 144 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (298 + x) *
        remainder6Coefficient0.coeff (298 - (298 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 298 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (298 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (298 - (298 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_298 :
    recurrence4Scalar0Exceptional.coeff 298 =
      (((((3307612655762197855800437 * 10 ^ 70 +
        9477950014185045809565656053644420432944034297764210677295076640956082) * 10 ^ 70 +
        4511052977448235580607390767579599303757053318592308935275786339722456) * 10 ^ 70 +
        4915838068704367119585436869465768412936897561800534064868491756590987) * 10 ^ 70 +
        8801121714429051042479838486282794269396807273850530899463314229876673) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (298 - x)) = _
  rw [show 299 = 145 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (299 + x) *
        remainder6Coefficient0.coeff (299 - (299 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 299 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (299 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (299 - (299 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_299 :
    recurrence4Scalar0Exceptional.coeff 299 =
      -(((((1818183413391114474305845 * 10 ^ 70 +
        3247712004195727707321173541514766257473201557331528653518398106536267) * 10 ^ 70 +
        9520413375266994801171536096751051938935436988671730747141060265534764) * 10 ^ 70 +
        4314465306397097546584169521685579908844110223288239349884163907511675) * 10 ^ 70 +
        0590588671124168604081517828922208498830612347546647107714275195497424) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (299 - x)) = _
  rw [show 300 = 146 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (300 + x) *
        remainder6Coefficient0.coeff (300 - (300 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 300 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (300 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (300 - (300 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_300 :
    recurrence4Scalar0Exceptional.coeff 300 =
      (((((955679834051840072112400 * 10 ^ 70 +
        0424937745952384304825486539444662732495227134188358174373620864962439) * 10 ^ 70 +
        4615337014152030329583131249426210139839522108697328227456646067616721) * 10 ^ 70 +
        0420804869987176000282491901297236230650222355832676751806785139050171) * 10 ^ 70 +
        3087112525039873063125107120972472990711261344113380431554483128978574) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (300 - x)) = _
  rw [show 301 = 147 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (301 + x) *
        remainder6Coefficient0.coeff (301 - (301 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 301 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (301 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (301 - (301 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_301 :
    recurrence4Scalar0Exceptional.coeff 301 =
      -(((((472188323821417328731233 * 10 ^ 70 +
        2754802669774538991753330638664528619896218244009769398110936096831007) * 10 ^ 70 +
        2683058013827704459445582928956112616718063964334764519801192686780349) * 10 ^ 70 +
        8987645950949852953540298367530980584953065500993136644655797182458020) * 10 ^ 70 +
        1012072275787613724867802746440351012155704035428101336941079679691535) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (301 - x)) = _
  rw [show 302 = 148 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (302 + x) *
        remainder6Coefficient0.coeff (302 - (302 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 302 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (302 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (302 - (302 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_302 :
    recurrence4Scalar0Exceptional.coeff 302 =
      (((((211828500333474202767976 * 10 ^ 70 +
        0691895275948059664600501482025898556896993881844996094160673364783000) * 10 ^ 70 +
        0822760876909041736676385903907039230287267787928056781599277688615093) * 10 ^ 70 +
        9261282646615417508966889258259565279169516382035696118838651223485887) * 10 ^ 70 +
        1505768677403528582457870256234764832005388039891540469562278361026583) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (302 - x)) = _
  rw [show 303 = 149 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (303 + x) *
        remainder6Coefficient0.coeff (303 - (303 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 303 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (303 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (303 - (303 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_303 :
    recurrence4Scalar0Exceptional.coeff 303 =
      -(((((78874529223399295672047 * 10 ^ 70 +
        6204373506504032125616687135372695277676369777771906584714302816555699) * 10 ^ 70 +
        1893268741647176649035340827200877319893749884186329706784865197730105) * 10 ^ 70 +
        9688205189741711343210370135372777055958576378192093474064900627977292) * 10 ^ 70 +
        1262291082778813693273788695292944551974106529273302306465561620966430) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (303 - x)) = _
  rw [show 304 = 150 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (304 + x) *
        remainder6Coefficient0.coeff (304 - (304 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 304 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (304 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (304 - (304 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_304 :
    recurrence4Scalar0Exceptional.coeff 304 =
      (((((16043957955970884834549 * 10 ^ 70 +
        5478496195631733704057334054871877148969469005661322708748422814166764) * 10 ^ 70 +
        4515812109178308874503333277634880665446164606927300444073187880173116) * 10 ^ 70 +
        3603845098689454007024035713402013117908441105929404100646912896499933) * 10 ^ 70 +
        0390575183111290826827686396753158668625302823085505006527059088042408) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (304 - x)) = _
  rw [show 305 = 151 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (305 + x) *
        remainder6Coefficient0.coeff (305 - (305 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 305 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (305 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (305 - (305 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_305 :
    recurrence4Scalar0Exceptional.coeff 305 =
      (((((9954208158013868752912 * 10 ^ 70 +
        7921452065014509650681025081710475869465638750720108365384736018518649) * 10 ^ 70 +
        0703006533206484114798812627778444354953572155211869384200724700887075) * 10 ^ 70 +
        4284739360479196823274652263775523316687395417406719343586434907725992) * 10 ^ 70 +
        2945930593532747653135563928920747820382655323514215064118664886707666) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (305 - x)) = _
  rw [show 306 = 152 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (306 + x) *
        remainder6Coefficient0.coeff (306 - (306 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 306 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (306 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (306 - (306 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_306 :
    recurrence4Scalar0Exceptional.coeff 306 =
      -(((((17817103871941449966031 * 10 ^ 70 +
        4081495121263185970028564395815443513713006282011437881312739136318251) * 10 ^ 70 +
        5366957173837231755464907144348798963164996007325473276807643896202718) * 10 ^ 70 +
        2967211078388320385880473008344576616268499570920115307319420962833605) * 10 ^ 70 +
        8715862402782152579470480705005465747483504689329163088390875090758036) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (306 - x)) = _
  rw [show 307 = 153 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (307 + x) *
        remainder6Coefficient0.coeff (307 - (307 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 307 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (307 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (307 - (307 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_307 :
    recurrence4Scalar0Exceptional.coeff 307 =
      (((((17612428686271736986028 * 10 ^ 70 +
        2537981363476874326655403135629398075579861787109653610419627472857439) * 10 ^ 70 +
        9040781960893324395605418525618302115592752546496354153621286223410363) * 10 ^ 70 +
        0744348597159470755300598416365153953609828069581694602312231971715942) * 10 ^ 70 +
        6949769916298187197738091104097193047520010949981863275766319009510588) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (307 - x)) = _
  rw [show 308 = 154 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (308 + x) *
        remainder6Coefficient0.coeff (308 - (308 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 308 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (308 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (308 - (308 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_308 :
    recurrence4Scalar0Exceptional.coeff 308 =
      -(((((14467887481817718556345 * 10 ^ 70 +
        7980683335251705498908981956740759937579182528828246150743250466258254) * 10 ^ 70 +
        1363379675866601803234755218613725088259225538384295174911263493340699) * 10 ^ 70 +
        3377403442376930311141461100975435320468587426033863063387890055066210) * 10 ^ 70 +
        4323330190162818595134228433005987306751385546773853877361777982785862) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (308 - x)) = _
  rw [show 309 = 155 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (309 + x) *
        remainder6Coefficient0.coeff (309 - (309 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 309 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (309 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (309 - (309 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_309 :
    recurrence4Scalar0Exceptional.coeff 309 =
      (((((10790651403501194746706 * 10 ^ 70 +
        2775121248547614697883987510569877758060933623979901756422146403052024) * 10 ^ 70 +
        6558871313909438786447479291061820863401376639305937805957059755046975) * 10 ^ 70 +
        0585870838100915996951495059518704913024830335565367703212167028434067) * 10 ^ 70 +
        0502877156007623431079679128561730230350217402356007227587580839855680) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (309 - x)) = _
  rw [show 310 = 156 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (310 + x) *
        remainder6Coefficient0.coeff (310 - (310 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 310 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (310 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (310 - (310 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_310 :
    recurrence4Scalar0Exceptional.coeff 310 =
      -(((((7561547363210459973411 * 10 ^ 70 +
        8877794119466128315599949142600982942386521718871928411338308165379946) * 10 ^ 70 +
        6731519522391347531980561360327055710109699560616912105620430393575494) * 10 ^ 70 +
        6015736392855632139675655341138528247997986990590380719787875520217601) * 10 ^ 70 +
        6865483721855700100389763160736078236377451170990896534636718589566842) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (310 - x)) = _
  rw [show 311 = 157 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (311 + x) *
        remainder6Coefficient0.coeff (311 - (311 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 311 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (311 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (311 - (311 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_311 :
    recurrence4Scalar0Exceptional.coeff 311 =
      (((((5062836745158143690653 * 10 ^ 70 +
        3047530021486165428970153206294529399836702458465121837490137888256545) * 10 ^ 70 +
        9625805409428626037865968724225511266086159337000321207709085360167285) * 10 ^ 70 +
        6040329919656129190856618767479647420446556688739055129026758258966329) * 10 ^ 70 +
        5355235576050068132633093001930735835703965057787789867915443183003166) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (311 - x)) = _
  rw [show 312 = 158 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (312 + x) *
        remainder6Coefficient0.coeff (312 - (312 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 312 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (312 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (312 - (312 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_312 :
    recurrence4Scalar0Exceptional.coeff 312 =
      -(((((3269667600030967523289 * 10 ^ 70 +
        9558419836182821535094095022525417112334791617124204656406908414437090) * 10 ^ 70 +
        2042033348908228003187613635343308697486981726005563184453815204692738) * 10 ^ 70 +
        9279703465371096806586155735439233114667351779528356471071065289127365) * 10 ^ 70 +
        2947028875034864677848114327184867531209635940386237664715903352857103) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (312 - x)) = _
  rw [show 313 = 159 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (313 + x) *
        remainder6Coefficient0.coeff (313 - (313 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 313 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (313 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (313 - (313 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_313 :
    recurrence4Scalar0Exceptional.coeff 313 =
      (((((2048605062695816443812 * 10 ^ 70 +
        3047956286512270624681212737436357246488195768388560173810795202258588) * 10 ^ 70 +
        6721940558296957493770639509755530824619376334606171135947290498724717) * 10 ^ 70 +
        9642258958037370481077540383581541822604286304227967697627020681346054) * 10 ^ 70 +
        9770537345692729382884252153015227131651589097852725643206538647137823) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (313 - x)) = _
  rw [show 314 = 160 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (314 + x) *
        remainder6Coefficient0.coeff (314 - (314 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 314 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (314 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (314 - (314 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_314 :
    recurrence4Scalar0Exceptional.coeff 314 =
      -(((((1249955071080548391117 * 10 ^ 70 +
        9662601095585257332313148321494708617178577028768119348628366378401295) * 10 ^ 70 +
        6100518010417006647431047040018200549745159067865363392597328622117215) * 10 ^ 70 +
        3073571694329367382994137949377746729910572917808784177186837350383613) * 10 ^ 70 +
        8275403007749897943852183443550207771612476624348472241986972833596620) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (314 - x)) = _
  rw [show 315 = 161 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (315 + x) *
        remainder6Coefficient0.coeff (315 - (315 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 315 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (315 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (315 - (315 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_315 :
    recurrence4Scalar0Exceptional.coeff 315 =
      (((((744589427150435622216 * 10 ^ 70 +
        8925680751578497539448009955733704642793448205068689564527228241744112) * 10 ^ 70 +
        8647280051322951412873807576408004109624710209688277187833317859957942) * 10 ^ 70 +
        6014430006067196549322650942358544217711598179397495821092166200868551) * 10 ^ 70 +
        3170081000670416873074271123936308593974690038291515958702591503158782) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (315 - x)) = _
  rw [show 316 = 162 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (316 + x) *
        remainder6Coefficient0.coeff (316 - (316 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 316 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (316 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (316 - (316 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_316 :
    recurrence4Scalar0Exceptional.coeff 316 =
      -(((((433798762159304600392 * 10 ^ 70 +
        6334117714533754095217201373668906817883667724575682837153797415677543) * 10 ^ 70 +
        7002446622518497798508101734931855614940267596741813518311435506690398) * 10 ^ 70 +
        9718016451817325384477542225643392659081150652920074988209626104346345) * 10 ^ 70 +
        8509007644537884981997898873007617006656332446420352495054741521361670) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (316 - x)) = _
  rw [show 317 = 163 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (317 + x) *
        remainder6Coefficient0.coeff (317 - (317 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 317 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (317 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (317 - (317 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_317 :
    recurrence4Scalar0Exceptional.coeff 317 =
      (((((247479365378230777082 * 10 ^ 70 +
        5716845709151042841258035236159516062492495130992717754151242892159991) * 10 ^ 70 +
        6438211546712112580424143684054558887438359208558048495546884088488342) * 10 ^ 70 +
        7160413876712967090520240728038416258806203527538410776359940540458222) * 10 ^ 70 +
        0198137535896796519211237915266055971441763397104261681263889491180313) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (317 - x)) = _
  rw [show 318 = 164 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (318 + x) *
        remainder6Coefficient0.coeff (318 - (318 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 318 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (318 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (318 - (318 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_318 :
    recurrence4Scalar0Exceptional.coeff 318 =
      -(((((138367236378942399711 * 10 ^ 70 +
        5413028764315513735809721560373393575710827961841081568785366752729044) * 10 ^ 70 +
        5859345202514130253651530841335607238662954646869397541135059186204257) * 10 ^ 70 +
        3763856318392355865599474965522966086290812679852830712871601788968524) * 10 ^ 70 +
        9904527933533992578144882611992708835346298324986479224247504997697546) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (318 - x)) = _
  rw [show 319 = 165 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (319 + x) *
        remainder6Coefficient0.coeff (319 - (319 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 319 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (319 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (319 - (319 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_319 :
    recurrence4Scalar0Exceptional.coeff 319 =
      (((((75859701209721452128 * 10 ^ 70 +
        5056875306796813346330393412254355912395538461840227776886005916612305) * 10 ^ 70 +
        6723330793614420427370955646073220811185228387188956505954822046018732) * 10 ^ 70 +
        9042060702423386081459558778149794591940057996139937620392867560631148) * 10 ^ 70 +
        8903090972697861114311406236750000235991172520319964171501247879682871) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (319 - x)) = _
  rw [show 320 = 166 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (320 + x) *
        remainder6Coefficient0.coeff (320 - (320 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 320 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (320 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (320 - (320 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_320 :
    recurrence4Scalar0Exceptional.coeff 320 =
      -(((((40795703835268182371 * 10 ^ 70 +
        9340050663842514900216869896451374220593773910460123592493248939029349) * 10 ^ 70 +
        1768757043379541189934668524887464200225177665676079550475163533305749) * 10 ^ 70 +
        2220647506071337529219889183870866423459490125878838358044408156107034) * 10 ^ 70 +
        3928419483278416694907531931892975427103502105525435480967582533995679) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (320 - x)) = _
  rw [show 321 = 167 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (321 + x) *
        remainder6Coefficient0.coeff (321 - (321 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 321 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (321 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (321 - (321 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_321 :
    recurrence4Scalar0Exceptional.coeff 321 =
      (((((21523004518034986587 * 10 ^ 70 +
        0816515951963817663971541920932631729998286720442982259520007328266620) * 10 ^ 70 +
        5278505392280527059958454148436566404448477939858847271995414380032502) * 10 ^ 70 +
        0340144836106027516896673362433851534733155923582780347258637373661468) * 10 ^ 70 +
        6168147798591171891403514275538852087830564302195826547684495197660222) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (321 - x)) = _
  rw [show 322 = 168 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (322 + x) *
        remainder6Coefficient0.coeff (322 - (322 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 322 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (322 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (322 - (322 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_322 :
    recurrence4Scalar0Exceptional.coeff 322 =
      -(((((11139423911414300696 * 10 ^ 70 +
        9621544772117557417292490905641613263491233534828515969339106524189413) * 10 ^ 70 +
        5593250976300245666683261060836850445991777537027983848418952903124631) * 10 ^ 70 +
        8742760527474138603174561124211940298718319277607258519839201367486389) * 10 ^ 70 +
        6281335290483645863829463137137097321052759537528885450678678946395340) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (322 - x)) = _
  rw [show 323 = 169 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (323 + x) *
        remainder6Coefficient0.coeff (323 - (323 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 323 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (323 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (323 - (323 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_323 :
    recurrence4Scalar0Exceptional.coeff 323 =
      (((((5654694391357435660 * 10 ^ 70 +
        8773633169352598211005214714907362302027667255344030469324045720307635) * 10 ^ 70 +
        5558076324469519285212147324384560035753352540356163513199176760183087) * 10 ^ 70 +
        4700213128262358637299984576262974166076824448966813685236734517897964) * 10 ^ 70 +
        6128145745949405818016650497423071815242134458772974522031146354263827) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (323 - x)) = _
  rw [show 324 = 170 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (324 + x) *
        remainder6Coefficient0.coeff (324 - (324 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 324 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (324 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (324 - (324 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_324 :
    recurrence4Scalar0Exceptional.coeff 324 =
      -(((((2814381640588080974 * 10 ^ 70 +
        7508424940708198204278880202529125952407112514166612896980209861218139) * 10 ^ 70 +
        8966657972470791772268776405909924283082637257223139175088147928506047) * 10 ^ 70 +
        3484509368692888280529630998748393359462888954036521378803067440249390) * 10 ^ 70 +
        3236969978747674416878651967291032468096750524208479232608030089120349) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (324 - x)) = _
  rw [show 325 = 171 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (325 + x) *
        remainder6Coefficient0.coeff (325 - (325 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 325 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (325 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (325 - (325 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_325 :
    recurrence4Scalar0Exceptional.coeff 325 =
      (((((1372590114349415669 * 10 ^ 70 +
        2274646982246345503274104232743202774454445415007391522092820321762561) * 10 ^ 70 +
        6995354449644518413449359342890640042800617012271809907204269923794032) * 10 ^ 70 +
        8508993555177914890762516620821623616402513875829731748103550672943372) * 10 ^ 70 +
        4107944407174452053997406249824204896032150456854363099636291658007394) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (325 - x)) = _
  rw [show 326 = 172 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (326 + x) *
        remainder6Coefficient0.coeff (326 - (326 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 326 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (326 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (326 - (326 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_326 :
    recurrence4Scalar0Exceptional.coeff 326 =
      -(((((655445351414752069 * 10 ^ 70 +
        5672922730148791930310467246373327015446876851422650610411630315892057) * 10 ^ 70 +
        5027851490151461902373822123104257910086575457064000618927785257514873) * 10 ^ 70 +
        1918751140323947668314218850709033033148656372080937120689348221463130) * 10 ^ 70 +
        8608040101154428592361798206211395417502734275106900786767634471680187) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (326 - x)) = _
  rw [show 327 = 173 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (327 + x) *
        remainder6Coefficient0.coeff (327 - (327 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 327 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (327 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (327 - (327 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_327 :
    recurrence4Scalar0Exceptional.coeff 327 =
      (((((306118518928448420 * 10 ^ 70 +
        7669049524745767512251514961438112495126139127043873347390523096674350) * 10 ^ 70 +
        6781833642894190998255608663110781451622168920308891930192668682955752) * 10 ^ 70 +
        8672575096537917365813262434234146772606791803038547656713982073756192) * 10 ^ 70 +
        4610753287838445793736733169212715698624586054827018578617666752594839) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (327 - x)) = _
  rw [show 328 = 174 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (328 + x) *
        remainder6Coefficient0.coeff (328 - (328 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 328 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (328 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (328 - (328 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_328 :
    recurrence4Scalar0Exceptional.coeff 328 =
      -(((((139616004840130988 * 10 ^ 70 +
        6899159918836410668321909354167421127617917124194604619769164299053548) * 10 ^ 70 +
        3375172726549048901439050749854316953463654920849484741175804337020754) * 10 ^ 70 +
        9750790826812212056891385032668641789546797941363497435644883135842734) * 10 ^ 70 +
        0265949395052726950127887764007101375939812435111586989584188961205419) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (328 - x)) = _
  rw [show 329 = 175 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (329 + x) *
        remainder6Coefficient0.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 329 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (329 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_329 :
    recurrence4Scalar0Exceptional.coeff 329 =
      (((((62049687364935925 * 10 ^ 70 +
        4776149408739934292272680188197904372384990273717947533689046647521109) * 10 ^ 70 +
        5849905514121633450536643723792326103338024131829687429827348530198857) * 10 ^ 70 +
        9015873084503795679907379127900344405358405370944997239139017456011790) * 10 ^ 70 +
        8462946991396148838747947063725318486663571945830951402958203990753372) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (329 - x)) = _
  rw [show 330 = 176 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (330 + x) *
        remainder6Coefficient0.coeff (330 - (330 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 330 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (330 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (330 - (330 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_330 :
    recurrence4Scalar0Exceptional.coeff 330 =
      -(((((26789028181771436 * 10 ^ 70 +
        6404714850550137876200570340381723502796260827360462785703115953712504) * 10 ^ 70 +
        7682884625042279324708980892013106539273482904536658321775087249946517) * 10 ^ 70 +
        9817632691897397562886029470307569922508379261450867293660195381631391) * 10 ^ 70 +
        2057935782784202286441831463375669931226333787444616156704646357735945) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (330 - x)) = _
  rw [show 331 = 177 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (331 + x) *
        remainder6Coefficient0.coeff (331 - (331 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 331 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (331 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (331 - (331 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_331 :
    recurrence4Scalar0Exceptional.coeff 331 =
      (((((11183328842133886 * 10 ^ 70 +
        0497559387675523257713612481325721247777424411175705136737057957718934) * 10 ^ 70 +
        8473732115815166353196877876240469913797444201835329780815434320281999) * 10 ^ 70 +
        1120629822829861085476020224916491285612485005983623231455866437861682) * 10 ^ 70 +
        5212545007052664719563491413565663916360243477526749276773215053884490) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (331 - x)) = _
  rw [show 332 = 178 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (332 + x) *
        remainder6Coefficient0.coeff (332 - (332 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 332 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (332 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (332 - (332 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_332 :
    recurrence4Scalar0Exceptional.coeff 332 =
      -(((((4481208055887998 * 10 ^ 70 +
        3422665763500063039710090497520494668632175253324832012873203067300752) * 10 ^ 70 +
        3641370478079110163660599982599964554619560012961270283915260376213692) * 10 ^ 70 +
        5368983233251122553073931575796686924793966320722281248167524767212191) * 10 ^ 70 +
        5826758415640317159569194669937419367449309196237157865095391413210330) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (332 - x)) = _
  rw [show 333 = 179 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (333 + x) *
        remainder6Coefficient0.coeff (333 - (333 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 333 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (333 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (333 - (333 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_333 :
    recurrence4Scalar0Exceptional.coeff 333 =
      (((((1702152577690804 * 10 ^ 70 +
        6008478144677673983813564173674915267336848005972894210237341425112841) * 10 ^ 70 +
        4424005345437590844275034777140858794758383241950963136153630448846265) * 10 ^ 70 +
        2860402851662091170104844549920483505486932406451360773514391205446603) * 10 ^ 70 +
        4252058582105882498769864585554583345873398501681514335765163660196489) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (333 - x)) = _
  rw [show 334 = 180 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (334 + x) *
        remainder6Coefficient0.coeff (334 - (334 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 334 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (334 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (334 - (334 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_334 :
    recurrence4Scalar0Exceptional.coeff 334 =
      -(((((598471945740846 * 10 ^ 70 +
        6828290377808724493052214007325316966381502286723137925282469075015843) * 10 ^ 70 +
        5944040599194870712787574458376448035568426258821369570294671382268291) * 10 ^ 70 +
        1314298665596159573422579063149759737730905512077350675486552721002548) * 10 ^ 70 +
        0962391176085916400029797832089622794767156166250123344546573429361011) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (334 - x)) = _
  rw [show 335 = 181 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (335 + x) *
        remainder6Coefficient0.coeff (335 - (335 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 335 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (335 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (335 - (335 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_335 :
    recurrence4Scalar0Exceptional.coeff 335 =
      (((((184489772772104 * 10 ^ 70 +
        4094341626857258493826212250103821641855934863689556618878855666167176) * 10 ^ 70 +
        4341514844573594573271738420327474184538010117143139988105133084179627) * 10 ^ 70 +
        3009947488311972576590752408576529459784794283218698304488352912388893) * 10 ^ 70 +
        9077625317809910743982297970318730339532315799712633638932070903937859) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (335 - x)) = _
  rw [show 336 = 182 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (336 + x) *
        remainder6Coefficient0.coeff (336 - (336 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 336 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (336 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (336 - (336 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_336 :
    recurrence4Scalar0Exceptional.coeff 336 =
      -(((((41789034947383 * 10 ^ 70 +
        9599878693586031651513224888097066562798590242424653144469799380748786) * 10 ^ 70 +
        8797460117203554603697627096393177163940713877781493668104535009634105) * 10 ^ 70 +
        0548381341593462613921166057641437781089256288774770876051746528285173) * 10 ^ 70 +
        0808133122168603469928204298196944614625462237141071729340294437198722) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (336 - x)) = _
  rw [show 337 = 183 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (337 + x) *
        remainder6Coefficient0.coeff (337 - (337 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 337 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (337 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (337 - (337 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_337 :
    recurrence4Scalar0Exceptional.coeff 337 =
      -(((((548535417451 * 10 ^ 70 +
        2897356711471464891227807940955339420138447841279210149909070729054924) * 10 ^ 70 +
        4365246232401716766167251984413452841364868122321499623709912428767316) * 10 ^ 70 +
        7205100960412726588329446054009155002187870784025551549839220501267902) * 10 ^ 70 +
        1608509018893827637724650837710310814609549326969894958299823881536092) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (337 - x)) = _
  rw [show 338 = 184 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (338 + x) *
        remainder6Coefficient0.coeff (338 - (338 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 338 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (338 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (338 - (338 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_338 :
    recurrence4Scalar0Exceptional.coeff 338 =
      (((((9053068472701 * 10 ^ 70 +
        8319507474692214009623356860136884126996693589263308051378829797345690) * 10 ^ 70 +
        0017264991593441026860894816473229650302372561325210839593882159358778) * 10 ^ 70 +
        8237738287149057868169337820618776740215235930073819159342096304805812) * 10 ^ 70 +
        0851422545700015547562152994598023883504461252342838810947349359596156) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (338 - x)) = _
  rw [show 339 = 185 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (339 + x) *
        remainder6Coefficient0.coeff (339 - (339 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 339 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (339 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (339 - (339 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_339 :
    recurrence4Scalar0Exceptional.coeff 339 =
      -(((((7967715866907 * 10 ^ 70 +
        7851920461900319506129487163713891295618459018274225193626783658123059) * 10 ^ 70 +
        9515908615209919768677070904741429347727698623296063306654901990465626) * 10 ^ 70 +
        2718689128206270662577022625576438063007803915710709311785129015397003) * 10 ^ 70 +
        0763159155907843631380383341204685114263980681900560130993852956679150) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (339 - x)) = _
  rw [show 340 = 186 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (340 + x) *
        remainder6Coefficient0.coeff (340 - (340 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 340 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (340 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (340 - (340 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_340 :
    recurrence4Scalar0Exceptional.coeff 340 =
      (((((5260841701931 * 10 ^ 70 +
        2241333263035354143371379240057396355518189970114424396702938288357571) * 10 ^ 70 +
        1862028837512041395925648124204223616515855258879644709795829690774045) * 10 ^ 70 +
        9947315173027980652093312599958478595263386706764607105617811982501228) * 10 ^ 70 +
        5088196936874506487928315077102470596870553302988774713406477360449571) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (340 - x)) = _
  rw [show 341 = 187 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (341 + x) *
        remainder6Coefficient0.coeff (341 - (341 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 341 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (341 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (341 - (341 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_341 :
    recurrence4Scalar0Exceptional.coeff 341 =
      -(((((3069002028179 * 10 ^ 70 +
        7340492704438298333607320730084978267166111743279809448020571494993212) * 10 ^ 70 +
        5109758509025577911813090406101081172078154471584623051670122726414070) * 10 ^ 70 +
        6240087712105419921970394740463322416020840160760456353915312664452049) * 10 ^ 70 +
        3949181826208063123656585292325635175327454335936401720095925237264408) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (341 - x)) = _
  rw [show 342 = 188 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (342 + x) *
        remainder6Coefficient0.coeff (342 - (342 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 342 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (342 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (342 - (342 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_342 :
    recurrence4Scalar0Exceptional.coeff 342 =
      (((((1666742669598 * 10 ^ 70 +
        1227023903552245867426550027254618823066650987025079409178489555385876) * 10 ^ 70 +
        2840248726594537912151331796404093786028349941615923572822469760578967) * 10 ^ 70 +
        1455422959470792091344144193979034498938320158434513474064500544678494) * 10 ^ 70 +
        4396949455452640862824449625644471755198354176099829893963229818701106) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (342 - x)) = _
  rw [show 343 = 189 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (343 + x) *
        remainder6Coefficient0.coeff (343 - (343 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 343 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (343 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (343 - (343 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_343 :
    recurrence4Scalar0Exceptional.coeff 343 =
      -(((((862806759108 * 10 ^ 70 +
        3958873564254592187581280549971376661829119354333371656456453175712292) * 10 ^ 70 +
        6867069207764265894653376947552821440870397513941946605202306466191177) * 10 ^ 70 +
        5905051546637897251560581092909843579755619348911101888164000358835396) * 10 ^ 70 +
        4996125837520483953005071298689548457797675371804257273174017066904856) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (343 - x)) = _
  rw [show 344 = 190 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (344 + x) *
        remainder6Coefficient0.coeff (344 - (344 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 344 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (344 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (344 - (344 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_344 :
    recurrence4Scalar0Exceptional.coeff 344 =
      (((((431155619022 * 10 ^ 70 +
        9844242859685824393014464289685404206805018535154995535179551231113075) * 10 ^ 70 +
        1634811532743022225710692139317287430188096561782336404112311595091172) * 10 ^ 70 +
        3084187889351096004582688225025082189635296269194340506620255439894403) * 10 ^ 70 +
        2153584489784371781279093323260096005446962687096833626309775515957102) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (344 - x)) = _
  rw [show 345 = 191 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (345 + x) *
        remainder6Coefficient0.coeff (345 - (345 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 345 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (345 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (345 - (345 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_345 :
    recurrence4Scalar0Exceptional.coeff 345 =
      -(((((209555422739 * 10 ^ 70 +
        9316917031207526430822437709531041931832240939632092979228651506841980) * 10 ^ 70 +
        9649002993309230482239322858186681474483976934305262074237336780137246) * 10 ^ 70 +
        4071200589689481800197116046832073280064870663315318530609658303121502) * 10 ^ 70 +
        6405570943809808061150297398824299298590137490554306428915855395372511) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (345 - x)) = _
  rw [show 346 = 192 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (346 + x) *
        remainder6Coefficient0.coeff (346 - (346 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 346 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (346 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (346 - (346 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_346 :
    recurrence4Scalar0Exceptional.coeff 346 =
      (((((99531955229 * 10 ^ 70 +
        5114902121393700750931524659066643692284513753851678084752528041334037) * 10 ^ 70 +
        8930008710186067797688582537818553725828627915939250460752055486883080) * 10 ^ 70 +
        3659277963832521023388874769950462776069066085814919666031972362210863) * 10 ^ 70 +
        0219053277901020901955960639785231105067733291174944960196818530058801) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (346 - x)) = _
  rw [show 347 = 193 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (347 + x) *
        remainder6Coefficient0.coeff (347 - (347 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 347 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (347 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (347 - (347 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_347 :
    recurrence4Scalar0Exceptional.coeff 347 =
      -(((((46338715682 * 10 ^ 70 +
        1853375751110162505452174975867701368143251333040243521765690353950178) * 10 ^ 70 +
        3764132739012054499027895113360006618065358449210309780378992884901571) * 10 ^ 70 +
        9736226665261813063491154047057183486106351000300518897552696177472065) * 10 ^ 70 +
        7320697689001777746283042105203794237102341594795671632400259943476035) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (347 - x)) = _
  rw [show 348 = 194 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (348 + x) *
        remainder6Coefficient0.coeff (348 - (348 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 348 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (348 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (348 - (348 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_348 :
    recurrence4Scalar0Exceptional.coeff 348 =
      (((((21187431959 * 10 ^ 70 +
        8617648174026914850606747902408055676262796796823987775761634948564892) * 10 ^ 70 +
        5616781111865699253133929885128622430098162209065991085518403016091228) * 10 ^ 70 +
        6686949689354591421351097603260316338560600808535926068563264631458040) * 10 ^ 70 +
        6617924942659912876133370084740118908514542532675764303826479237512147) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (348 - x)) = _
  rw [show 349 = 195 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (349 + x) *
        remainder6Coefficient0.coeff (349 - (349 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 349 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (349 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (349 - (349 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_349 :
    recurrence4Scalar0Exceptional.coeff 349 =
      -(((((9524911506 * 10 ^ 70 +
        5968986705568806164126391638428802410253357078063289026224335986544444) * 10 ^ 70 +
        1759457670407913036936300318876174558048897458379092594467754159054363) * 10 ^ 70 +
        3794729748655135660876803437903290459093967501702240421938246840162312) * 10 ^ 70 +
        2890559384974372815283530290793453525170221572801524177714176819169187) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (349 - x)) = _
  rw [show 350 = 196 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (350 + x) *
        remainder6Coefficient0.coeff (350 - (350 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 350 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (350 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (350 - (350 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_350 :
    recurrence4Scalar0Exceptional.coeff 350 =
      (((((4212471451 * 10 ^ 70 +
        5659923570943679172632613864831278537152796335758511668504917437131945) * 10 ^ 70 +
        9532598207631174428241540515153819155620127790478298864863316354616873) * 10 ^ 70 +
        5744903411341940673831990945061691077694064444169805154687902173182318) * 10 ^ 70 +
        4732278398648958213410311498129037118683671803420505068446096579671112) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (350 - x)) = _
  rw [show 351 = 197 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (351 + x) *
        remainder6Coefficient0.coeff (351 - (351 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 351 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (351 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (351 - (351 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_351 :
    recurrence4Scalar0Exceptional.coeff 351 =
      -(((((1832985740 * 10 ^ 70 +
        0538301511777684908407662592689885869319311007660042287642580683287267) * 10 ^ 70 +
        9783893718191507549619988542850743268866053765733808488898845481805749) * 10 ^ 70 +
        7505675178566114688000627750656722276171540830369431168030723096242977) * 10 ^ 70 +
        1375517099636958255372477441573829197372143849915444999982482367182443) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (351 - x)) = _
  rw [show 352 = 198 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (352 + x) *
        remainder6Coefficient0.coeff (352 - (352 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 352 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (352 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (352 - (352 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_352 :
    recurrence4Scalar0Exceptional.coeff 352 =
      (((((784558303 * 10 ^ 70 +
        4854098743661894853131319756472334392486673754333203124381132869483590) * 10 ^ 70 +
        6217198048720663869360662120922350431256786820341926439671792299625107) * 10 ^ 70 +
        4299286124506981461987237970449732792946700382205831579474859568626796) * 10 ^ 70 +
        8903206333175683699392561207572289024686175356227635599017129698816523) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (352 - x)) = _
  rw [show 353 = 199 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (353 + x) *
        remainder6Coefficient0.coeff (353 - (353 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 353 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (353 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (353 - (353 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_353 :
    recurrence4Scalar0Exceptional.coeff 353 =
      -(((((330141710 * 10 ^ 70 +
        2816688447825136213693890416395931034460347326916554421016008418907803) * 10 ^ 70 +
        1428783991367048455755779539882582103269705705519754187462111412453429) * 10 ^ 70 +
        4841169380923770545883594556665427400732563716552519932146258262995670) * 10 ^ 70 +
        4636159498641263746882558011374378021552569828631626592000546122532216) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (353 - x)) = _
  rw [show 354 = 200 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (354 + x) *
        remainder6Coefficient0.coeff (354 - (354 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 354 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (354 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (354 - (354 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_354 :
    recurrence4Scalar0Exceptional.coeff 354 =
      (((((136465743 * 10 ^ 70 +
        3645308922238207117086431383256799707115911436611303878304923304457297) * 10 ^ 70 +
        2544753760365282885805089825631144450160909142798227983636656047010582) * 10 ^ 70 +
        4475039529286354641432611084426068020223786073316548610888104430420322) * 10 ^ 70 +
        9104790482874479111340820773663451615929791268044277926222053567523799) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (354 - x)) = _
  rw [show 355 = 201 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (355 + x) *
        remainder6Coefficient0.coeff (355 - (355 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 355 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (355 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (355 - (355 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_355 :
    recurrence4Scalar0Exceptional.coeff 355 =
      -(((((55347480 * 10 ^ 70 +
        8922283064620067169955156813478546662604803835776561149768557925071163) * 10 ^ 70 +
        0617042337381127188575503421951879295761214584904211194959749058062786) * 10 ^ 70 +
        6493046505493161421513873453558416944846971097498951517597456916022313) * 10 ^ 70 +
        3287357432921353673791826842090784406986826938374520858638309300054743) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (355 - x)) = _
  rw [show 356 = 202 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (356 + x) *
        remainder6Coefficient0.coeff (356 - (356 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 356 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (356 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (356 - (356 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_356 :
    recurrence4Scalar0Exceptional.coeff 356 =
      (((((21991594 * 10 ^ 70 +
        0117209148380667335342168343221378853637864999571529214069895881384143) * 10 ^ 70 +
        0943756875196627567613940890770165569862993947789479190540996046808002) * 10 ^ 70 +
        8729913347811572899145967553977364127975280355338388337826854195999242) * 10 ^ 70 +
        1737080916706239286572555302285483231004977625666137073481403935038786) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (356 - x)) = _
  rw [show 357 = 203 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (357 + x) *
        remainder6Coefficient0.coeff (357 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 357 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (357 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (357 - (357 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_357 :
    recurrence4Scalar0Exceptional.coeff 357 =
      -(((((8542733 * 10 ^ 70 +
        2948836865592444512334228834438577825339597781176374343095154781974787) * 10 ^ 70 +
        7068146923438722446355635594678842037493901056203225998112932735139794) * 10 ^ 70 +
        0266354562344340650161583355779033580407091699520051884501230647225935) * 10 ^ 70 +
        7277224228211412024377720747340237265614054065136267990389624528476523) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (357 - x)) = _
  rw [show 358 = 204 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (358 + x) *
        remainder6Coefficient0.coeff (358 - (358 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 358 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (358 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (358 - (358 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_358 :
    recurrence4Scalar0Exceptional.coeff 358 =
      (((((3234831 * 10 ^ 70 +
        7325171505310157922797280255071138339909673154884066459541520542509715) * 10 ^ 70 +
        7725080641752298967914681606012643503865732724276242504539152908454950) * 10 ^ 70 +
        5632411385951154872028371824985154143415248990847615628596462570330902) * 10 ^ 70 +
        6356756175592946155657195953553594281323962506433660219764748125550510) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (358 - x)) = _
  rw [show 359 = 205 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (359 + x) *
        remainder6Coefficient0.coeff (359 - (359 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 359 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (359 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (359 - (359 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_359 :
    recurrence4Scalar0Exceptional.coeff 359 =
      -(((((1188932 * 10 ^ 70 +
        5333856294606041638438803925350240344867767776990734993024365142848435) * 10 ^ 70 +
        0438241685750105882427520105226600827346487353523876127872145803927938) * 10 ^ 70 +
        7918576163235552906387901143693001162774940732369787742000232255634316) * 10 ^ 70 +
        9457340308110162336285984510227857152873807991759001111406846213128894) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (359 - x)) = _
  rw [show 360 = 206 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (360 + x) *
        remainder6Coefficient0.coeff (360 - (360 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 360 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (360 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (360 - (360 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_360 :
    recurrence4Scalar0Exceptional.coeff 360 =
      (((((421305 * 10 ^ 70 +
        4408520093390920301126807926666965659029262380138563213461782936999367) * 10 ^ 70 +
        8082871895779773634515128864794289307333653827296501725668472374433036) * 10 ^ 70 +
        8762206052473161891593088460541804044195263181621722808832867577800670) * 10 ^ 70 +
        0243454873638903351509758770082087287014204171278194210989001573289339) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (360 - x)) = _
  rw [show 361 = 207 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (361 + x) *
        remainder6Coefficient0.coeff (361 - (361 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 361 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (361 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (361 - (361 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_361 :
    recurrence4Scalar0Exceptional.coeff 361 =
      -(((((142311 * 10 ^ 70 +
        7177682740904539433627671669031838953911423877466876405167946060529939) * 10 ^ 70 +
        3169740920171351951483586473474263415889387567655297025462717952200469) * 10 ^ 70 +
        4119207191410306068659894949356753674111647083048549281151240365608703) * 10 ^ 70 +
        8720334609839838213945240861140092790199021136909331375457613981570074) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (361 - x)) = _
  rw [show 362 = 208 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (362 + x) *
        remainder6Coefficient0.coeff (362 - (362 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 362 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (362 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (362 - (362 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_362 :
    recurrence4Scalar0Exceptional.coeff 362 =
      (((((44855 * 10 ^ 70 +
        5992296316580714798685637260966096094683086225526717395906719982383756) * 10 ^ 70 +
        0967213043264909595148135389532160468380929029846535021087974334626737) * 10 ^ 70 +
        0986666633799138034425953323503338394960589966468505086870186579631231) * 10 ^ 70 +
        5486249256938385934255720599622599215024248649375221472358803421902522) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (362 - x)) = _
  rw [show 363 = 209 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (363 + x) *
        remainder6Coefficient0.coeff (363 - (363 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 363 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (363 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (363 - (363 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_363 :
    recurrence4Scalar0Exceptional.coeff 363 =
      -(((((12582 * 10 ^ 70 +
        0910420897491518603501410670093393946510521406111397255770257454560019) * 10 ^ 70 +
        3233666695390322529968688052229568967280341887457507555580749170746974) * 10 ^ 70 +
        4019669657481356535953729781586616571981189052562111979484570685340514) * 10 ^ 70 +
        4110898226014406612526979266589243525041672215042225181729193738657512) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (363 - x)) = _
  rw [show 364 = 210 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (364 + x) *
        remainder6Coefficient0.coeff (364 - (364 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 364 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (364 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (364 - (364 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_364 :
    recurrence4Scalar0Exceptional.coeff 364 =
      (((((2719 * 10 ^ 70 +
        5463817420524711315363130980348911129951799423331760800178663458021083) * 10 ^ 70 +
        7151899880448585094442919394882044853808708849957474775694594364604973) * 10 ^ 70 +
        4151137357323468951532174895860319702112640810476217035695474894051429) * 10 ^ 70 +
        4378786235015172984979994913741243524547231309549852063645384749023602) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (364 - x)) = _
  rw [show 365 = 211 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (365 + x) *
        remainder6Coefficient0.coeff (365 - (365 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 365 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (365 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (365 - (365 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_365 :
    recurrence4Scalar0Exceptional.coeff 365 =
      -(((((112 * 10 ^ 70 +
        7613767190100324308764258250798174349890705598384149564198776779828790) * 10 ^ 70 +
        8552612547810043847152629182923781966474218832775550715518338215588898) * 10 ^ 70 +
        9953274377686970699198997830555882323772651828782871449369329010551079) * 10 ^ 70 +
        2206911612886009564584868307546753807835413377287709891051872220676855) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (365 - x)) = _
  rw [show 366 = 212 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (366 + x) *
        remainder6Coefficient0.coeff (366 - (366 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 366 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (366 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (366 - (366 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_366 :
    recurrence4Scalar0Exceptional.coeff 366 =
      -(((((357 * 10 ^ 70 +
        6238578242218612101273983803021494552710510688613864332172115053338478) * 10 ^ 70 +
        9945503626855611327383373728478595550639657098088257355028139324668311) * 10 ^ 70 +
        8619128081150976317659917949520592641364048183940315511883996729452012) * 10 ^ 70 +
        4930026026670792512065085363953946084119309904432152653116782846034574) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (366 - x)) = _
  rw [show 367 = 213 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (367 + x) *
        remainder6Coefficient0.coeff (367 - (367 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 367 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (367 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (367 - (367 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_367 :
    recurrence4Scalar0Exceptional.coeff 367 =
      (((((306 * 10 ^ 70 +
        3319750820162289107594211805037093867647973485262368420084269837254755) * 10 ^ 70 +
        4010941537746092103470998211408407952733317757854056306315499550879606) * 10 ^ 70 +
        4529443456311182009521423982556109061156636864443427868573780660246103) * 10 ^ 70 +
        3057567576965598657594000710896261001121335501218868952539633687248808) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (367 - x)) = _
  rw [show 368 = 214 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (368 + x) *
        remainder6Coefficient0.coeff (368 - (368 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 368 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (368 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (368 - (368 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_368 :
    recurrence4Scalar0Exceptional.coeff 368 =
      -(((((187 * 10 ^ 70 +
        5289940369560003341569762533257175437115997052017710411485077919472215) * 10 ^ 70 +
        7840754781615232445064315345738421240334320125844064368310228850708402) * 10 ^ 70 +
        6715501305233387131670002907563384402978633039403751851075280216602603) * 10 ^ 70 +
        0029676339871571286791588747623182435197243250209899594077782033570904) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (368 - x)) = _
  rw [show 369 = 215 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (369 + x) *
        remainder6Coefficient0.coeff (369 - (369 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 369 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (369 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (369 - (369 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_369 :
    recurrence4Scalar0Exceptional.coeff 369 =
      (((((100 * 10 ^ 70 +
        3731805501221164332423419159676835311879063148698254610791664245022766) * 10 ^ 70 +
        1174476547095371047604871642441134826686589284103888768910828322566099) * 10 ^ 70 +
        0412169257721044843838204799603280901210173934941273956832006051962541) * 10 ^ 70 +
        2522314618943546984359147108865800451230835744920901492626429502475348) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (369 - x)) = _
  rw [show 370 = 216 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (370 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (370 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_370 :
    recurrence4Scalar0Exceptional.coeff 370 =
      -(((((49 * 10 ^ 70 +
        8150521521819266412150889196966656012110467312279326954153207358626958) * 10 ^ 70 +
        6708998687680356244542712896327029113970080931307163877448232983076841) * 10 ^ 70 +
        9398292535687770210113498119753794421492776920206974946268667990718580) * 10 ^ 70 +
        7645894501444807693935310444393024512210550621075730240704221213232894) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (370 - x)) = _
  rw [show 371 = 217 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (371 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (371 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_371 :
    recurrence4Scalar0Exceptional.coeff 371 =
      (((((23 * 10 ^ 70 +
        5018159344600153985450566403333206646947876462658448366284937339596858) * 10 ^ 70 +
        7232118061037689424636518131300481416338905148923601309011707435193164) * 10 ^ 70 +
        8324784731084816511176816790855986737474044229611017576398937077628483) * 10 ^ 70 +
        2782412184534495859516103831433392805650626017458165431991349531873007) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (371 - x)) = _
  rw [show 372 = 218 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 24 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (372 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (372 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_372 :
    recurrence4Scalar0Exceptional.coeff 372 =
      -(((((10 * 10 ^ 70 +
        6719712289286032192203502272050285325009470802591481140503444362945834) * 10 ^ 70 +
        6104594811679963948163815334197374989406830389948266428833959271752962) * 10 ^ 70 +
        0852597730256502309107891730702917756861151858545180031876817229706662) * 10 ^ 70 +
        2369201519362292228444095649124264785172993628103233118423288841893214) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (372 - x)) = _
  rw [show 373 = 219 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 23 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (373 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (373 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_373 :
    recurrence4Scalar0Exceptional.coeff 373 =
      (((((4 * 10 ^ 70 +
        6958808409728860779753567386487502552310669401938134387071276895325315) * 10 ^ 70 +
        3788346107429629753954298828321941355001251917943924249036343850663872) * 10 ^ 70 +
        6545604997262338646531439690862464012300011039988884240546682450265246) * 10 ^ 70 +
        0382943648519725516750219129979935721055595895082517951913185866689227) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (373 - x)) = _
  rw [show 374 = 220 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 22 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (374 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (374 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_374 :
    recurrence4Scalar0Exceptional.coeff 374 =
      -(((((2 * 10 ^ 70 +
        0097350106612655916580831683969691179987241479916588811647016875268091) * 10 ^ 70 +
        4986932414589038602421873691920994622892302301639307817105206482051383) * 10 ^ 70 +
        1989687571503025340712126793882901450069233906861546517050291255013750) * 10 ^ 70 +
        1478540210712977773372941129684806266251560306269143286556859320001545) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (374 - x)) = _
  rw [show 375 = 221 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 21 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (375 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (375 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_375 :
    recurrence4Scalar0Exceptional.coeff 375 =
      ((((8382448698130158356502059716168094119414742398856798865075946013841489 * 10 ^ 70 +
        4629265336360791370046526367633129414688557032380827851937647659271263) * 10 ^ 70 +
        5305176649865728581717448627240115097767821937874318456308216216932010) * 10 ^ 70 +
        5050152048604338825684897015524486936004190768254595666253384583137724) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (375 - x)) = _
  rw [show 376 = 222 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 20 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (376 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (376 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_376 :
    recurrence4Scalar0Exceptional.coeff 376 =
      -((((3410337108986014535993425180716678977244101758245846178546321033712531 * 10 ^ 70 +
        7272466813817007069646172310427480526755128934089142900204673710975959) * 10 ^ 70 +
        3922913880644704621719256086254508957459316766153868483762865260412167) * 10 ^ 70 +
        1167456209803427711072876490941622528882533423682243340668406432208678) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (376 - x)) = _
  rw [show 377 = 223 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 19 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (377 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (377 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_377 :
    recurrence4Scalar0Exceptional.coeff 377 =
      ((((1353551639955695095609154452974357933476289830395190402921681649253099 * 10 ^ 70 +
        2441954418531851680178959948680179971219422835317022136972208781106368) * 10 ^ 70 +
        3325782918321236908264646052394385780136685224363826823883178843593670) * 10 ^ 70 +
        5009673972964582384526902896899591131479448604397758542910996219570028) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (377 - x)) = _
  rw [show 378 = 224 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 18 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (378 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (378 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_378 :
    recurrence4Scalar0Exceptional.coeff 378 =
      -((((523849021027259782842871004377478228675295244637713213900523237961171 * 10 ^ 70 +
        1832418449412368529768585147577421550417333583010366796330968413966865) * 10 ^ 70 +
        3276476469115443868824482063266104692750337655573363190329833117716914) * 10 ^ 70 +
        9496258028133045714380072330701128095758051356484528871496041822251321) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (378 - x)) = _
  rw [show 379 = 225 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 17 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (379 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (379 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_379 :
    recurrence4Scalar0Exceptional.coeff 379 =
      ((((197495176999037531749626441038569683657639608278283208035508564038395 * 10 ^ 70 +
        2590694824484230367686674529595187737442186363780904490739613432696425) * 10 ^ 70 +
        2876733586590592529152739590252842954672482318128992736240940549231019) * 10 ^ 70 +
        9679277584696681366571100456837651537115121382328543503997722832881811) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (379 - x)) = _
  rw [show 380 = 226 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 16 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (380 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (380 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_380 :
    recurrence4Scalar0Exceptional.coeff 380 =
      -((((72412698707393043387531922805736628069808820253312283707126484404258 * 10 ^ 70 +
        9058266835117659852149171117370302650433805720129483998353254656748477) * 10 ^ 70 +
        7989383674093592716042256405279363702011909791273381067513841577635028) * 10 ^ 70 +
        1858318309499715169068627160289410067763895290794437856556656289979634) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (380 - x)) = _
  rw [show 381 = 227 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 15 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (381 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (381 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_381 :
    recurrence4Scalar0Exceptional.coeff 381 =
      ((((25756000332550194748705836114153813731521101445821289767937864835131 * 10 ^ 70 +
        6501279654325240830868962046134380238595031308659715735497846375316683) * 10 ^ 70 +
        4071538797497197327262927696012087308825888228145398065750540887641151) * 10 ^ 70 +
        4450729124837472951651842368612515652915064578741952967742365552016155) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (381 - x)) = _
  rw [show 382 = 228 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 14 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient0.coeff (382 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (382 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_382 :
    recurrence4Scalar0Exceptional.coeff 382 =
      -((((8851326189393614876817776839550490436579582374721687177208945860123 * 10 ^ 70 +
        8867239010020598098325474518177062108530554415659386729002433152162862) * 10 ^ 70 +
        0493562682336161986515704721058784449938927167234845238369524702859512) * 10 ^ 70 +
        3833086409748287730982323033240564388278194943202246129292419847537932) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (382 - x)) = _
  rw [show 383 = 229 +
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 13 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
