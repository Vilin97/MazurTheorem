/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0ExceptionalPart2Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
