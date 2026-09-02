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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
