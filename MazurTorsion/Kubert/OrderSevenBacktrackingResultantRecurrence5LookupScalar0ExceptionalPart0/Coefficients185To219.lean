/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_0
  recurrence5ExceptionalProduct_coeff_1
  recurrence5ExceptionalProduct_coeff_2
  recurrence5ExceptionalProduct_coeff_3
  recurrence5ExceptionalProduct_coeff_4
  recurrence5ExceptionalProduct_coeff_5
  recurrence5ExceptionalProduct_coeff_6
  recurrence5ExceptionalProduct_coeff_7
  recurrence5ExceptionalProduct_coeff_8
  recurrence5ExceptionalProduct_coeff_9
  recurrence5ExceptionalProduct_coeff_10
  recurrence5ExceptionalProduct_coeff_11
  recurrence5ExceptionalProduct_coeff_12
  recurrence5ExceptionalProduct_coeff_13
  recurrence5ExceptionalProduct_coeff_14
  recurrence5ExceptionalProduct_coeff_15
  recurrence5ExceptionalProduct_coeff_16
  recurrence5ExceptionalProduct_coeff_17
  recurrence5ExceptionalProduct_coeff_18
  recurrence5ExceptionalProduct_coeff_19
  recurrence5ExceptionalProduct_coeff_20
  recurrence5ExceptionalProduct_coeff_21
  recurrence5ExceptionalProduct_coeff_22
  recurrence5ExceptionalProduct_coeff_23
  recurrence5ExceptionalProduct_coeff_24
  recurrence5ExceptionalProduct_coeff_25
  recurrence5ExceptionalProduct_coeff_26
  recurrence5ExceptionalProduct_coeff_27
  recurrence5ExceptionalProduct_coeff_28
  recurrence5ExceptionalProduct_coeff_29
  recurrence5ExceptionalProduct_coeff_30
  recurrence5ExceptionalProduct_coeff_31
  recurrence5ExceptionalProduct_coeff_32
  recurrence5ExceptionalProduct_coeff_33
  recurrence5ExceptionalProduct_coeff_34
  recurrence5ExceptionalProduct_coeff_35
  recurrence5ExceptionalProduct_coeff_36
  recurrence5ExceptionalProduct_coeff_37
  recurrence5ExceptionalProduct_coeff_38
  recurrence5ExceptionalProduct_coeff_39
  recurrence5ExceptionalProduct_coeff_40
  recurrence5ExceptionalProduct_coeff_41
  recurrence5ExceptionalProduct_coeff_42
  recurrence5ExceptionalProduct_coeff_43
  recurrence5ExceptionalProduct_coeff_44
  recurrence5ExceptionalProduct_coeff_45
  recurrence5ExceptionalProduct_coeff_46
  recurrence5ExceptionalProduct_coeff_47
  recurrence5ExceptionalProduct_coeff_48
  recurrence5ExceptionalProduct_coeff_49
  recurrence5ExceptionalProduct_coeff_50
  recurrence5ExceptionalProduct_coeff_51
  recurrence5ExceptionalProduct_coeff_52
  recurrence5ExceptionalProduct_coeff_53
  recurrence5ExceptionalProduct_coeff_54
  recurrence5ExceptionalProduct_coeff_55
  recurrence5ExceptionalProduct_coeff_56
  recurrence5ExceptionalProduct_coeff_57
  recurrence5ExceptionalProduct_coeff_58
  recurrence5ExceptionalProduct_coeff_59
  recurrence5ExceptionalProduct_coeff_60
  recurrence5ExceptionalProduct_coeff_61
  recurrence5ExceptionalProduct_coeff_62
  recurrence5ExceptionalProduct_coeff_63

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_64
  recurrence5ExceptionalProduct_coeff_65
  recurrence5ExceptionalProduct_coeff_66
  recurrence5ExceptionalProduct_coeff_67
  recurrence5ExceptionalProduct_coeff_68
  recurrence5ExceptionalProduct_coeff_69
  recurrence5ExceptionalProduct_coeff_70
  recurrence5ExceptionalProduct_coeff_71
  recurrence5ExceptionalProduct_coeff_72
  recurrence5ExceptionalProduct_coeff_73
  recurrence5ExceptionalProduct_coeff_74
  recurrence5ExceptionalProduct_coeff_75
  recurrence5ExceptionalProduct_coeff_76
  recurrence5ExceptionalProduct_coeff_77
  recurrence5ExceptionalProduct_coeff_78
  recurrence5ExceptionalProduct_coeff_79
  recurrence5ExceptionalProduct_coeff_80
  recurrence5ExceptionalProduct_coeff_81
  recurrence5ExceptionalProduct_coeff_82
  recurrence5ExceptionalProduct_coeff_83
  recurrence5ExceptionalProduct_coeff_84
  recurrence5ExceptionalProduct_coeff_85
  recurrence5ExceptionalProduct_coeff_86
  recurrence5ExceptionalProduct_coeff_87
  recurrence5ExceptionalProduct_coeff_88
  recurrence5ExceptionalProduct_coeff_89
  recurrence5ExceptionalProduct_coeff_90
  recurrence5ExceptionalProduct_coeff_91
  recurrence5ExceptionalProduct_coeff_92
  recurrence5ExceptionalProduct_coeff_93
  recurrence5ExceptionalProduct_coeff_94
  recurrence5ExceptionalProduct_coeff_95
  recurrence5ExceptionalProduct_coeff_96
  recurrence5ExceptionalProduct_coeff_97
  recurrence5ExceptionalProduct_coeff_98
  recurrence5ExceptionalProduct_coeff_99
  recurrence5ExceptionalProduct_coeff_100
  recurrence5ExceptionalProduct_coeff_101
  recurrence5ExceptionalProduct_coeff_102
  recurrence5ExceptionalProduct_coeff_103
  recurrence5ExceptionalProduct_coeff_104
  recurrence5ExceptionalProduct_coeff_105
  recurrence5ExceptionalProduct_coeff_106
  recurrence5ExceptionalProduct_coeff_107
  recurrence5ExceptionalProduct_coeff_108
  recurrence5ExceptionalProduct_coeff_109
  recurrence5ExceptionalProduct_coeff_110
  recurrence5ExceptionalProduct_coeff_111
  recurrence5ExceptionalProduct_coeff_112
  recurrence5ExceptionalProduct_coeff_113
  recurrence5ExceptionalProduct_coeff_114
  recurrence5ExceptionalProduct_coeff_115
  recurrence5ExceptionalProduct_coeff_116
  recurrence5ExceptionalProduct_coeff_117
  recurrence5ExceptionalProduct_coeff_118
  recurrence5ExceptionalProduct_coeff_119
  recurrence5ExceptionalProduct_coeff_120
  recurrence5ExceptionalProduct_coeff_121
  recurrence5ExceptionalProduct_coeff_122
  recurrence5ExceptionalProduct_coeff_123
  recurrence5ExceptionalProduct_coeff_124
  recurrence5ExceptionalProduct_coeff_125
  recurrence5ExceptionalProduct_coeff_126
  recurrence5ExceptionalProduct_coeff_127

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_128
  recurrence5ExceptionalProduct_coeff_129
  recurrence5ExceptionalProduct_coeff_130
  recurrence5ExceptionalProduct_coeff_131
  recurrence5ExceptionalProduct_coeff_132
  recurrence5ExceptionalProduct_coeff_133
  recurrence5ExceptionalProduct_coeff_134
  recurrence5ExceptionalProduct_coeff_135
  recurrence5ExceptionalProduct_coeff_136
  recurrence5ExceptionalProduct_coeff_137
  recurrence5ExceptionalProduct_coeff_138
  recurrence5ExceptionalProduct_coeff_139
  recurrence5ExceptionalProduct_coeff_140
  recurrence5ExceptionalProduct_coeff_141
  recurrence5ExceptionalProduct_coeff_142
  recurrence5ExceptionalProduct_coeff_143
  recurrence5ExceptionalProduct_coeff_144
  recurrence5ExceptionalProduct_coeff_145
  recurrence5ExceptionalProduct_coeff_146
  recurrence5ExceptionalProduct_coeff_147
  recurrence5ExceptionalProduct_coeff_148
  recurrence5ExceptionalProduct_coeff_149
  recurrence5ExceptionalProduct_coeff_150
  recurrence5ExceptionalProduct_coeff_151
  recurrence5ExceptionalProduct_coeff_152
  recurrence5ExceptionalProduct_coeff_153
  recurrence5ExceptionalProduct_coeff_154
  recurrence5ExceptionalProduct_coeff_155
  recurrence5ExceptionalProduct_coeff_156
  recurrence5ExceptionalProduct_coeff_157
  recurrence5ExceptionalProduct_coeff_158
  recurrence5ExceptionalProduct_coeff_159
  recurrence5ExceptionalProduct_coeff_160
  recurrence5ExceptionalProduct_coeff_161
  recurrence5ExceptionalProduct_coeff_162
  recurrence5ExceptionalProduct_coeff_163
  recurrence5ExceptionalProduct_coeff_164
  recurrence5ExceptionalProduct_coeff_165
  recurrence5ExceptionalProduct_coeff_166
  recurrence5ExceptionalProduct_coeff_167
  recurrence5ExceptionalProduct_coeff_168
  recurrence5ExceptionalProduct_coeff_169
  recurrence5ExceptionalProduct_coeff_170
  recurrence5ExceptionalProduct_coeff_171
  recurrence5ExceptionalProduct_coeff_172
  recurrence5ExceptionalProduct_coeff_173
  recurrence5ExceptionalProduct_coeff_174
  recurrence5ExceptionalProduct_coeff_175
  recurrence5ExceptionalProduct_coeff_176
  recurrence5ExceptionalProduct_coeff_177
  recurrence5ExceptionalProduct_coeff_178
  recurrence5ExceptionalProduct_coeff_179
  recurrence5ExceptionalProduct_coeff_180
  recurrence5ExceptionalProduct_coeff_181
  recurrence5ExceptionalProduct_coeff_182
  recurrence5ExceptionalProduct_coeff_183
  recurrence5ExceptionalProduct_coeff_184
  recurrence5ExceptionalProduct_coeff_185
  recurrence5ExceptionalProduct_coeff_186
  recurrence5ExceptionalProduct_coeff_187
  recurrence5ExceptionalProduct_coeff_188
  recurrence5ExceptionalProduct_coeff_189
  recurrence5ExceptionalProduct_coeff_190
  recurrence5ExceptionalProduct_coeff_191

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_192
  recurrence5ExceptionalProduct_coeff_193
  recurrence5ExceptionalProduct_coeff_194
  recurrence5ExceptionalProduct_coeff_195
  recurrence5ExceptionalProduct_coeff_196
  recurrence5ExceptionalProduct_coeff_197
  recurrence5ExceptionalProduct_coeff_198
  recurrence5ExceptionalProduct_coeff_199
  recurrence5ExceptionalProduct_coeff_200
  recurrence5ExceptionalProduct_coeff_201
  recurrence5ExceptionalProduct_coeff_202
  recurrence5ExceptionalProduct_coeff_203
  recurrence5ExceptionalProduct_coeff_204
  recurrence5ExceptionalProduct_coeff_205
  recurrence5ExceptionalProduct_coeff_206
  recurrence5ExceptionalProduct_coeff_207
  recurrence5ExceptionalProduct_coeff_208
  recurrence5ExceptionalProduct_coeff_209
  recurrence5ExceptionalProduct_coeff_210
  recurrence5ExceptionalProduct_coeff_211
  recurrence5ExceptionalProduct_coeff_212
  recurrence5ExceptionalProduct_coeff_213
  recurrence5ExceptionalProduct_coeff_214
  recurrence5ExceptionalProduct_coeff_215
  recurrence5ExceptionalProduct_coeff_216
  recurrence5ExceptionalProduct_coeff_217
  recurrence5ExceptionalProduct_coeff_218
  recurrence5ExceptionalProduct_coeff_219
  recurrence5ExceptionalProduct_coeff_220
  recurrence5ExceptionalProduct_coeff_221
  recurrence5ExceptionalProduct_coeff_222
  recurrence5ExceptionalProduct_coeff_223
  recurrence5ExceptionalProduct_coeff_224
  recurrence5ExceptionalProduct_coeff_225
  recurrence5ExceptionalProduct_coeff_226
  recurrence5ExceptionalProduct_coeff_227
  recurrence5ExceptionalProduct_coeff_228
  recurrence5ExceptionalProduct_coeff_229
  recurrence5ExceptionalProduct_coeff_230
  recurrence5ExceptionalProduct_coeff_231
  recurrence5ExceptionalProduct_coeff_232
  recurrence5ExceptionalProduct_coeff_233
  recurrence5ExceptionalProduct_coeff_234
  recurrence5ExceptionalProduct_coeff_235
  recurrence5ExceptionalProduct_coeff_236
  recurrence5ExceptionalProduct_coeff_237
  recurrence5ExceptionalProduct_coeff_238
  recurrence5ExceptionalProduct_coeff_239
  recurrence5ExceptionalProduct_coeff_240
  recurrence5ExceptionalProduct_coeff_241
  recurrence5ExceptionalProduct_coeff_242
  recurrence5ExceptionalProduct_coeff_243
  recurrence5ExceptionalProduct_coeff_244
  recurrence5ExceptionalProduct_coeff_245
  recurrence5ExceptionalProduct_coeff_246
  recurrence5ExceptionalProduct_coeff_247
  recurrence5ExceptionalProduct_coeff_248
  recurrence5ExceptionalProduct_coeff_249
  recurrence5ExceptionalProduct_coeff_250
  recurrence5ExceptionalProduct_coeff_251
  recurrence5ExceptionalProduct_coeff_252
  recurrence5ExceptionalProduct_coeff_253
  recurrence5ExceptionalProduct_coeff_254
  recurrence5ExceptionalProduct_coeff_255

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_256
  recurrence5ExceptionalProduct_coeff_257
  recurrence5ExceptionalProduct_coeff_258
  recurrence5ExceptionalProduct_coeff_259
  recurrence5ExceptionalProduct_coeff_260
  recurrence5ExceptionalProduct_coeff_261
  recurrence5ExceptionalProduct_coeff_262
  recurrence5ExceptionalProduct_coeff_263
  recurrence5ExceptionalProduct_coeff_264
  recurrence5ExceptionalProduct_coeff_265
  recurrence5ExceptionalProduct_coeff_266
  recurrence5ExceptionalProduct_coeff_267
  recurrence5ExceptionalProduct_coeff_268
  recurrence5ExceptionalProduct_coeff_269
  recurrence5ExceptionalProduct_coeff_270
  recurrence5ExceptionalProduct_coeff_271
  recurrence5ExceptionalProduct_coeff_272
  recurrence5ExceptionalProduct_coeff_273
  recurrence5ExceptionalProduct_coeff_274
  recurrence5ExceptionalProduct_coeff_275
  recurrence5ExceptionalProduct_coeff_276
  recurrence5ExceptionalProduct_coeff_277
  recurrence5ExceptionalProduct_coeff_278
  recurrence5ExceptionalProduct_coeff_279
  recurrence5ExceptionalProduct_coeff_280
  recurrence5ExceptionalProduct_coeff_281
  recurrence5ExceptionalProduct_coeff_282
  recurrence5ExceptionalProduct_coeff_283
  recurrence5ExceptionalProduct_coeff_284
  recurrence5ExceptionalProduct_coeff_285
  recurrence5ExceptionalProduct_coeff_286
  recurrence5ExceptionalProduct_coeff_287
  recurrence5ExceptionalProduct_coeff_288
  recurrence5ExceptionalProduct_coeff_289
  recurrence5ExceptionalProduct_coeff_290
  recurrence5ExceptionalProduct_coeff_291
  recurrence5ExceptionalProduct_coeff_292
  recurrence5ExceptionalProduct_coeff_293
  recurrence5ExceptionalProduct_coeff_294
  recurrence5ExceptionalProduct_coeff_295
  recurrence5ExceptionalProduct_coeff_296
  recurrence5ExceptionalProduct_coeff_297
  recurrence5ExceptionalProduct_coeff_298
  recurrence5ExceptionalProduct_coeff_299
  recurrence5ExceptionalProduct_coeff_300
  recurrence5ExceptionalProduct_coeff_301
  recurrence5ExceptionalProduct_coeff_302
  recurrence5ExceptionalProduct_coeff_303
  recurrence5ExceptionalProduct_coeff_304
  recurrence5ExceptionalProduct_coeff_305
  recurrence5ExceptionalProduct_coeff_306
  recurrence5ExceptionalProduct_coeff_307
  recurrence5ExceptionalProduct_coeff_308
  recurrence5ExceptionalProduct_coeff_309
  recurrence5ExceptionalProduct_coeff_310
  recurrence5ExceptionalProduct_coeff_311
  recurrence5ExceptionalProduct_coeff_312
  recurrence5ExceptionalProduct_coeff_313
  recurrence5ExceptionalProduct_coeff_314
  recurrence5ExceptionalProduct_coeff_315
  recurrence5ExceptionalProduct_coeff_316
  recurrence5ExceptionalProduct_coeff_317
  recurrence5ExceptionalProduct_coeff_318
  recurrence5ExceptionalProduct_coeff_319

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_320
  recurrence5ExceptionalProduct_coeff_321
  recurrence5ExceptionalProduct_coeff_322
  recurrence5ExceptionalProduct_coeff_323
  recurrence5ExceptionalProduct_coeff_324
  recurrence5ExceptionalProduct_coeff_325
  recurrence5ExceptionalProduct_coeff_326
  recurrence5ExceptionalProduct_coeff_327
  recurrence5ExceptionalProduct_coeff_328
  recurrence5ExceptionalProduct_coeff_329
  recurrence5ExceptionalProduct_coeff_330
  recurrence5ExceptionalProduct_coeff_331
  recurrence5ExceptionalProduct_coeff_332
  recurrence5ExceptionalProduct_coeff_333
  recurrence5ExceptionalProduct_coeff_334
  recurrence5ExceptionalProduct_coeff_335
  recurrence5ExceptionalProduct_coeff_336
  recurrence5ExceptionalProduct_coeff_337
  recurrence5ExceptionalProduct_coeff_338
  recurrence5ExceptionalProduct_coeff_339
  recurrence5ExceptionalProduct_coeff_340
  recurrence5ExceptionalProduct_coeff_341
  recurrence5ExceptionalProduct_coeff_342
  recurrence5ExceptionalProduct_coeff_343
  recurrence5ExceptionalProduct_coeff_344
  recurrence5ExceptionalProduct_coeff_345
  recurrence5ExceptionalProduct_coeff_346
  recurrence5ExceptionalProduct_coeff_347
  recurrence5ExceptionalProduct_coeff_348
  recurrence5ExceptionalProduct_coeff_349
  recurrence5ExceptionalProduct_coeff_350
  recurrence5ExceptionalProduct_coeff_351
  recurrence5ExceptionalProduct_coeff_352
  recurrence5ExceptionalProduct_coeff_353
  recurrence5ExceptionalProduct_coeff_354
  recurrence5ExceptionalProduct_coeff_355
  recurrence5ExceptionalProduct_coeff_356
  recurrence5ExceptionalProduct_coeff_357
  recurrence5ExceptionalProduct_coeff_358
  recurrence5ExceptionalProduct_coeff_359
  recurrence5ExceptionalProduct_coeff_360
  recurrence5ExceptionalProduct_coeff_361
  recurrence5ExceptionalProduct_coeff_362
  recurrence5ExceptionalProduct_coeff_363
  recurrence5ExceptionalProduct_coeff_364
  recurrence5ExceptionalProduct_coeff_365
  recurrence5ExceptionalProduct_coeff_366
  recurrence5ExceptionalProduct_coeff_367
  recurrence5ExceptionalProduct_coeff_368
  recurrence5ExceptionalProduct_coeff_369
  recurrence5ExceptionalProduct_coeff_370
  recurrence5ExceptionalProduct_coeff_371
  recurrence5ExceptionalProduct_coeff_372
  recurrence5ExceptionalProduct_coeff_373
  recurrence5ExceptionalProduct_coeff_374
  recurrence5ExceptionalProduct_coeff_375
  recurrence5ExceptionalProduct_coeff_376
  recurrence5ExceptionalProduct_coeff_377
  recurrence5ExceptionalProduct_coeff_378
  recurrence5C0_coeff_0
  recurrence5C0_coeff_1
  recurrence5C0_coeff_2
  recurrence5C0_coeff_3
  recurrence5C0_coeff_4

attribute [local simp]
  recurrence5C0_coeff_5
  recurrence5C0_coeff_6
  recurrence5C0_coeff_7
  recurrence5C0_coeff_8
  recurrence5C0_coeff_9
  recurrence5C0_coeff_10
  recurrence5C0_coeff_11
  recurrence5C0_coeff_12
  recurrence5C0_coeff_13
  recurrence5C0_coeff_14
  recurrence5C0_coeff_15
  recurrence5C0_coeff_16
  recurrence5C0_coeff_17
  recurrence5C0_coeff_18
  recurrence5C0_coeff_19
  recurrence5C0_coeff_20
  recurrence5C0_coeff_21
  recurrence5C0_coeff_22
  recurrence5C0_coeff_23
  recurrence5C0_coeff_24
  recurrence5C0_coeff_25
  recurrence5C0_coeff_26
  recurrence5C0_coeff_27
  recurrence5C0_coeff_28
  recurrence5C0_coeff_29
  recurrence5C0_coeff_30
  recurrence5C0_coeff_31
  recurrence5C0_coeff_32
  recurrence5C0_coeff_33
  recurrence5C0_coeff_34
  recurrence5C0_coeff_35
  recurrence5C0_coeff_36
  recurrence5C0_coeff_37
  recurrence5C0_coeff_38
  recurrence5C0_coeff_39
  recurrence5C0_coeff_40
  recurrence5C0_coeff_41
  recurrence5C0_coeff_42
  recurrence5C0_coeff_43
  recurrence5C0_coeff_44
  recurrence5C0_coeff_45
  recurrence5C0_coeff_46
  recurrence5C0_coeff_47
  recurrence5C0_coeff_48
  recurrence5C0_coeff_49
  recurrence5C0_coeff_50
  recurrence5C0_coeff_51
  recurrence5C0_coeff_52
  recurrence5C0_coeff_53
  recurrence5C0_coeff_54
  recurrence5C0_coeff_55
  recurrence5C0_coeff_56
  recurrence5C0_coeff_57
  recurrence5C0_coeff_58
  recurrence5C0_coeff_59
  recurrence5C0_coeff_60
  recurrence5C0_coeff_61
  recurrence5C0_coeff_62
  recurrence5C0_coeff_63
  recurrence5C0_coeff_64
  recurrence5C0_coeff_65
  recurrence5C0_coeff_66
  recurrence5C0_coeff_67
  recurrence5C0_coeff_68

attribute [local simp]
  recurrence5C0_coeff_69
  recurrence5C0_coeff_70
  recurrence5C0_coeff_71
  recurrence5C0_coeff_72
  recurrence5C0_coeff_73
  recurrence5C0_coeff_74
  recurrence5C0_coeff_75
  recurrence5C0_coeff_76
  recurrence5C0_coeff_77
  recurrence5C0_coeff_78
  recurrence5C0_coeff_79
  recurrence5C0_coeff_80
  recurrence5C0_coeff_81
  recurrence5C0_coeff_82
  recurrence5C0_coeff_83
  recurrence5C0_coeff_84
  recurrence5C0_coeff_85
  recurrence5C0_coeff_86
  recurrence5C0_coeff_87
  recurrence5C0_coeff_88

private theorem recurrence5Scalar0Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_185 :
    recurrence5Scalar0Exceptional.coeff 185 =
      ((((((121 * 10 ^ 70 +
        4299552935600502712812194525951334574809571489533425168005513686187408) * 10 ^ 70 +
        3561995624877278662873549072201417250834470674995483785468863420249949) * 10 ^ 70 +
        1597927057966084528028542294391966012435741028431512114842803952595665) * 10 ^ 70 +
        3915794282385812913861651009264111699317720772850916614050418805980962) * 10 ^ 70 +
        5790655582809190499215544951177985120411791647861744899982704391477670) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 97 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_185_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_186 :
    recurrence5Scalar0Exceptional.coeff 186 =
      -((((((251 * 10 ^ 70 +
        1215551750229611937624250645284491896191328879925927529660199227149402) * 10 ^ 70 +
        7778659628190026237605068342411913803018549197220305208492809003058741) * 10 ^ 70 +
        4688349835791985578373329114701341931833479948661143772576281570780448) * 10 ^ 70 +
        3397478855125423282911431891600830545763119917066902787668883064381488) * 10 ^ 70 +
        9570461135527033775991928343267548720095293153202165684265437713338064) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 98 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_186_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_187 :
    recurrence5Scalar0Exceptional.coeff 187 =
      ((((((508 * 10 ^ 70 +
        8119895043011357031628029079089525139561726265312631424716745822514849) * 10 ^ 70 +
        2655106443214303720463384515958265669540253551264987849137142366427174) * 10 ^ 70 +
        7535066712164364289647251896184627530950402988672672555453193292370136) * 10 ^ 70 +
        0938004465917715868934386552854375743233439189576543464824002715837717) * 10 ^ 70 +
        5057460788854983229097212851062865051668133736618139684129424141417970) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 99 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_187_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_188 :
    recurrence5Scalar0Exceptional.coeff 188 =
      -((((((1010 * 10 ^ 70 +
        2224948494269363478389414809649317799075560330710068539195177700598121) * 10 ^ 70 +
        6517954328261416182122036186800908073668131336060861793255822897169086) * 10 ^ 70 +
        5481157782117681392637814443137897175695678679120212356371635388809235) * 10 ^ 70 +
        5255078986618238655826762043384429548669613085655783785880230281016477) * 10 ^ 70 +
        7340704104827488100828921238070945051163067562139789760887762118771875) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 100 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_188_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_189 :
    recurrence5Scalar0Exceptional.coeff 189 =
      ((((((1965 * 10 ^ 70 +
        7436979284926022443687136206676173551722609569213630430210694340132868) * 10 ^ 70 +
        2367649481241741915408765394729036778874479039964509073835261513562012) * 10 ^ 70 +
        8471953969489427896372020577146122618312630644227858609405969010958403) * 10 ^ 70 +
        5972457786356028648229267126415778251204669413073180672469347542201821) * 10 ^ 70 +
        1820097260647894184714389494836379356527465534117539452118759403728834) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 101 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_189_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_190 :
    recurrence5Scalar0Exceptional.coeff 190 =
      -((((((3749 * 10 ^ 70 +
        2449515214815627357476573396697403270181195143110577403228997413796056) * 10 ^ 70 +
        9783479720847991044557564006875144431214587893291086969392485574974708) * 10 ^ 70 +
        0466906401578536619646511472180493878738131944380258728796282833535198) * 10 ^ 70 +
        7415160929110819142282945998676894358398805204196007037162142485578743) * 10 ^ 70 +
        5562515184721451140458298396684286188669296716985294752221455813600024) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 102 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_190_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_191 :
    recurrence5Scalar0Exceptional.coeff 191 =
      ((((((7010 * 10 ^ 70 +
        0028294504068573265345503608729700482066230899817442776327842244887380) * 10 ^ 70 +
        6206343186988612339336802618743265457922662239412519142078212630460537) * 10 ^ 70 +
        3373579125628609508208586482385031715266025357575777668414421862970886) * 10 ^ 70 +
        5161625857243165210412634800540866036784278150694309323622431109712403) * 10 ^ 70 +
        9532376834228015318289642041285495833028226086402851321677785812517659) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 103 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_191_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_192 :
    recurrence5Scalar0Exceptional.coeff 192 =
      -((((((12849 * 10 ^ 70 +
        7356887032872058675390116377083681834588876240436833079846416237498973) * 10 ^ 70 +
        5005614013063304548089891610915683450903870074239387781663399145018959) * 10 ^ 70 +
        9262853080373558745730621193959372073390075279484971147352696409131855) * 10 ^ 70 +
        5934980043257090111030756077424034098613292777913311521323494793395951) * 10 ^ 70 +
        5365674318939281778284190592349510590397258398506475911970636078549118) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 104 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_192_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_193 :
    recurrence5Scalar0Exceptional.coeff 193 =
      ((((((23094 * 10 ^ 70 +
        5761529180307573572727220998720918088705242326271160877790676525433459) * 10 ^ 70 +
        0782293598226317446122410864838193019569932670386999980312708661970169) * 10 ^ 70 +
        0700800747430708315576947158082272303139675520707647223983538427613060) * 10 ^ 70 +
        3464487389342690231149860185020601705944967461914759034058843467775561) * 10 ^ 70 +
        1452135293403025088656711689846891601696681012810252011923259123531737) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 105 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_193_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_194 :
    recurrence5Scalar0Exceptional.coeff 194 =
      -((((((40700 * 10 ^ 70 +
        3312173727303083823561882609326966757232339435802397222692298079870748) * 10 ^ 70 +
        5781797439926024499868540461230003173309078649392643357174544714001346) * 10 ^ 70 +
        8249061369878922088992846130888699609826098987973197519418612724516916) * 10 ^ 70 +
        6855070369606594474009638233584307066200514046101606031170579894915989) * 10 ^ 70 +
        3653939343557818566492210423932502418324616716483449562308901874271617) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 106 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_194_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_195 :
    recurrence5Scalar0Exceptional.coeff 195 =
      ((((((70337 * 10 ^ 70 +
        1304923228558340427633516570405537647659590499423407300945436094492841) * 10 ^ 70 +
        3633775260648523660560522284999108034877894619251027392512264305399948) * 10 ^ 70 +
        2202679417551694020218756002838298818987416506172645160943995689630791) * 10 ^ 70 +
        2962736773307678484416823763676338462091715088845488846977866392539526) * 10 ^ 70 +
        2165274985997934748317966759214062947938436677630641782295262787313545) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 107 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_195_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_196 :
    recurrence5Scalar0Exceptional.coeff 196 =
      -((((((119204 * 10 ^ 70 +
        0506008476381416230178707847482922857598485510912105911053667126859094) * 10 ^ 70 +
        2691354175801587028017952453703385714322049979509022644113887192956096) * 10 ^ 70 +
        6490799352742246760779279028419042363297122970857665997059500365361896) * 10 ^ 70 +
        4507628221794753490399687317468327341632241136533319674503316610592126) * 10 ^ 70 +
        3197516982022303885759539876862976995075735731985910748128985668437389) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 108 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_196_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_197 :
    recurrence5Scalar0Exceptional.coeff 197 =
      ((((((198121 * 10 ^ 70 +
        7777156940139854754207740026499873960992207254538868799501420934007685) * 10 ^ 70 +
        2777563034268786389547550704442375372436541596157578359415158063687247) * 10 ^ 70 +
        9931711459258663385651219587830817023374384895246183247903608829134059) * 10 ^ 70 +
        2648155029049740498078253620453326107257170438658748988229389934557424) * 10 ^ 70 +
        5538882094340938769600500398965971024398545377833672243108450243096208) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 109 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_197_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_198 :
    recurrence5Scalar0Exceptional.coeff 198 =
      -((((((322936 * 10 ^ 70 +
        8431748250666965143916560334733544174041887694887880077341375784317228) * 10 ^ 70 +
        1921586781145898466426322300143963381328376882693747309881641166707028) * 10 ^ 70 +
        5027850981617380420341400510673391102748074473234102705431920987070311) * 10 ^ 70 +
        3560706609973169438752349146433601640033133824482105761982203416262637) * 10 ^ 70 +
        7145750050332584639644917261055422450169537879349171866694165201118220) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 110 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_198_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_199 :
    recurrence5Scalar0Exceptional.coeff 199 =
      ((((((516238 * 10 ^ 70 +
        6145418803508960184575571813951722966811360786425559676656188094996534) * 10 ^ 70 +
        9812930713353770494044580364125003896656457808993760409237421687566725) * 10 ^ 70 +
        6193307384244145338307442996633192952370783498919758110597210195661271) * 10 ^ 70 +
        3857507807108707675673365666139799631915038210089000696889328172850657) * 10 ^ 70 +
        8830194145377637168948831250592383250435964073727898224842703174821325) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 111 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_199_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_200 :
    recurrence5Scalar0Exceptional.coeff 200 =
      -((((((809334 * 10 ^ 70 +
        3420483145815168916942547149015242619006477323584219014312964306234185) * 10 ^ 70 +
        7721990448547050626687740595933900049582833955606934033244493719240068) * 10 ^ 70 +
        5433275882913759878918666483426646958756461345240757606797625506742511) * 10 ^ 70 +
        1213588892606733591846002311381637075504911201958795150370848815861468) * 10 ^ 70 +
        3236153503703687639466432017274791769792078324934263254134055825222394) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 112 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_200_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_201 :
    recurrence5Scalar0Exceptional.coeff 201 =
      ((((((1244344 * 10 ^ 70 +
        1962815801213687409324504525336680580013631890502242323346895598003548) * 10 ^ 70 +
        6419069230017071392701551390274656246366059103031993952121968680986032) * 10 ^ 70 +
        3537225884872898883493311268274435652910145430191292138804186564500451) * 10 ^ 70 +
        2201634199753196969532717734286999467517776535860941735590317490358945) * 10 ^ 70 +
        3575671413896479496934092147881257525391457623012466931021589175134184) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 113 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_201_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_202 :
    recurrence5Scalar0Exceptional.coeff 202 =
      -((((((1876167 * 10 ^ 70 +
        4748102031442464986196564016652589317951575900292581128309700678035769) * 10 ^ 70 +
        4637939946889056568320986979967134282305235593069734245687538631253012) * 10 ^ 70 +
        0788362003889591203445055379172288420089806848355872072330136303218067) * 10 ^ 70 +
        3433100415114956978543805986859607843906026119550735088188249445447044) * 10 ^ 70 +
        7723777609072993571749828837148023918528288033900248263229171550365834) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 114 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_202_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_203 :
    recurrence5Scalar0Exceptional.coeff 203 =
      ((((((2773939 * 10 ^ 70 +
        8190148507410516962695481869333117650570572266429706067213245367431269) * 10 ^ 70 +
        0393134126488044327098003419590475842256662163196762174966407915208317) * 10 ^ 70 +
        8344699798507938047104961224315783403503636118934037783211218953707279) * 10 ^ 70 +
        2824503221277845748058755422807017112028956883890299611654050557656292) * 10 ^ 70 +
        5892420708180656050002667035995601001132311418663616671349965792423072) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 115 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_203_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_204 :
    recurrence5Scalar0Exceptional.coeff 204 =
      -((((((4021465 * 10 ^ 70 +
        4472954730348406766908643149641589080579034171402069580070204690200950) * 10 ^ 70 +
        4229867505533661774084885191307405648270994171107788877960094773614949) * 10 ^ 70 +
        8803117567453206346893551235526491908044032491326861186227400399953615) * 10 ^ 70 +
        3226841878907354243248097923980615425876466621096259361474184602383172) * 10 ^ 70 +
        1482254645377583732279734166357899885793402572768717560367409558479776) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 116 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_204_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_205 :
    recurrence5Scalar0Exceptional.coeff 205 =
      ((((((5715994 * 10 ^ 70 +
        9339031471891675142222890807189560562985816729374189602127532291702784) * 10 ^ 70 +
        4124384802656960279474209569799614523418758783782403967885439431496097) * 10 ^ 70 +
        2306737622657687427102416857902918714647020123339419134986753682019496) * 10 ^ 70 +
        4598932298974136652189416998112011559288166331961296996046232961802374) * 10 ^ 70 +
        0669143887981895955141398828277209156807745712638541388399665023726789) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 117 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_205_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_206 :
    recurrence5Scalar0Exceptional.coeff 206 =
      -((((((7964664 * 10 ^ 70 +
        9880622964789147860857341698375388619885069650386245188239477285932011) * 10 ^ 70 +
        5284266610084337833563075714026102325194069785016362130716365780009688) * 10 ^ 70 +
        7585481271203177051260768898885217812117916788639181099027242014395496) * 10 ^ 70 +
        0239809123976833784764845590460892195432549928719272275992603882743198) * 10 ^ 70 +
        7442397242491486174806067772373510998515599110853317186422378307912175) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 118 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_206_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_207 :
    recurrence5Scalar0Exceptional.coeff 207 =
      ((((((10877965 * 10 ^ 70 +
        4962531864268599940649550822492108495982570799598287953409466742495143) * 10 ^ 70 +
        7739533072834070769250312966514504408458685756304941127429520440974063) * 10 ^ 70 +
        1507888899953610574850730958988484693245667868302778603131445542338366) * 10 ^ 70 +
        8939895300979171310497291684884874903802452894824374864743906309326321) * 10 ^ 70 +
        3792805356329971137960857265557427330688443184221146289318451474906905) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 119 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_207_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_208 :
    recurrence5Scalar0Exceptional.coeff 208 =
      -((((((14559793 * 10 ^ 70 +
        1232552169639476311273887449369229758138625895435761141837253874499678) * 10 ^ 70 +
        3363565391413021613927551668094945397321255118707926355478556823428020) * 10 ^ 70 +
        3474708565295561216624798318023445119612316688323430590052499368535442) * 10 ^ 70 +
        2797325359956437378164694758240465010773109401722184375462700211357258) * 10 ^ 70 +
        0898958933311088903263783380556972714069918859666691620273160805320329) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 120 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_208_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_209 :
    recurrence5Scalar0Exceptional.coeff 209 =
      ((((((19094020 * 10 ^ 70 +
        0017683511269361751185880621554562160647260969059045687136834975231754) * 10 ^ 70 +
        7678947403575438145062979605034104748803457620339870422867623387050250) * 10 ^ 70 +
        3449659326054843202922017352817148107323161498075215739168801264727330) * 10 ^ 70 +
        1033757974180401951779456063138510103237820882070863917992730690331488) * 10 ^ 70 +
        3512276574202057327644770711539056778856088166721283508229511135096216) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 121 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_209_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_210 :
    recurrence5Scalar0Exceptional.coeff 210 =
      -((((((24528054 * 10 ^ 70 +
        6076183140589851027978957875340008403947805665469122864379139398889596) * 10 ^ 70 +
        0578306253006404133501491415602285689947076851516562688785604478590713) * 10 ^ 70 +
        4963862937973692229579389109136528019767398148940298559988892012577506) * 10 ^ 70 +
        6866608840873669051212187258866221035172500350437142651675371272607548) * 10 ^ 70 +
        5738732992052200550527812874974430387738482479405718024181762757794808) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 122 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_210_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_211 :
    recurrence5Scalar0Exceptional.coeff 211 =
      ((((((30854565 * 10 ^ 70 +
        1514450777907399384072491253614454889963620579356627345035384751080670) * 10 ^ 70 +
        4652566246782781237605605329945668318802164037148088341275573650746970) * 10 ^ 70 +
        0664809987619680005972111472067141187021559629168215186393018015190790) * 10 ^ 70 +
        5614829873167161150478440358785272226252639319176752004393920557778989) * 10 ^ 70 +
        5617740055932153724517253120900009366994492047470549069395951535251008) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 123 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_211_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_212 :
    recurrence5Scalar0Exceptional.coeff 212 =
      -((((((37993291 * 10 ^ 70 +
        7656168616049666382298081648134388381319944291881934627740903221490391) * 10 ^ 70 +
        8255876311323372326454980518832211994792327744542016208409230264597361) * 10 ^ 70 +
        4614005174858990521629687421221298052940215811118425891434217486760931) * 10 ^ 70 +
        6412233632271254052824820321413304482743111202514774997935106307866632) * 10 ^ 70 +
        0236757729436993895759720487711734893746715885737851413993641280210502) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 124 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_212_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_213 :
    recurrence5Scalar0Exceptional.coeff 213 =
      ((((((45775563 * 10 ^ 70 +
        5111018309558120496381795706831852894627983863179534834576822043297644) * 10 ^ 70 +
        8352531783198322418045725472267231256796190805677312510504046578409171) * 10 ^ 70 +
        7735868248964940440127595021179584501017572261175651229499182280762804) * 10 ^ 70 +
        4508632003018063891772994707384591046257046776319099778137500638121161) * 10 ^ 70 +
        3161331870126471984172378647496558035883421322719587342659067754553840) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 125 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_213_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_214 :
    recurrence5Scalar0Exceptional.coeff 214 =
      -((((((53934596 * 10 ^ 70 +
        5837283369037940225220609055681973731213469144325714849465820197278540) * 10 ^ 70 +
        9548291907170165235265000711914205430067723781106714788233734486860438) * 10 ^ 70 +
        4805161655387318222070932710135280401456420402439983537299808350744748) * 10 ^ 70 +
        3348994271048830159984143989098235698142997553546535590975087412132186) * 10 ^ 70 +
        0090640853486450450650467892456501443424066795475533207311255008270769) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 126 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_214_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_215 :
    recurrence5Scalar0Exceptional.coeff 215 =
      ((((((62104709 * 10 ^ 70 +
        9609378863655903853449523525782014018687677949902437294052522040934615) * 10 ^ 70 +
        9135991164457849464383973006120699766176753410217660329811266416052944) * 10 ^ 70 +
        2273055541553267192038239377903029401707725667406774699832656154961570) * 10 ^ 70 +
        0883353252864966415668299379349852566166871263758337686364965274690945) * 10 ^ 70 +
        7726413507557173558742766437658823236726719973811379871232991509943137) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 127 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_215_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_216 :
    recurrence5Scalar0Exceptional.coeff 216 =
      -((((((69832112 * 10 ^ 70 +
        8898913853680158476820900138048437893817965529052039493445925538507785) * 10 ^ 70 +
        3181489408516156837808548709013311371958774121896551889418682583236975) * 10 ^ 70 +
        5712775343910708277982393481518176405688236698784128534612489699028951) * 10 ^ 70 +
        2149097110048074952848268996073204512295395446302695603530172603395917) * 10 ^ 70 +
        4811757589006641515794265628734501871177448272359788245211043649390631) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 128 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_216_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_217 :
    recurrence5Scalar0Exceptional.coeff 217 =
      ((((((76598826 * 10 ^ 70 +
        6405368873578925982842642545096032273544700757169999202279518774203182) * 10 ^ 70 +
        1668473577009538886067613925183259038907258805816107895954825299580829) * 10 ^ 70 +
        7881249350703877940120484060383017470093461080477759899955576794654958) * 10 ^ 70 +
        5618891358218594805382204252107835225844262375964754453697659219267196) * 10 ^ 70 +
        9241371170010141759901004842915780357459591723334939105066804514739803) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 129 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_217_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_218 :
    recurrence5Scalar0Exceptional.coeff 218 =
      -((((((81859643 * 10 ^ 70 +
        1548089593908338397904972442219785249049482412703495366885023963392831) * 10 ^ 70 +
        3302340382355147861927806653904774039362682279039540728465143773728664) * 10 ^ 70 +
        5843418497555932511257876807054077839949683065667112796019267022482483) * 10 ^ 70 +
        4514698245193690275740559517654945354787810296473721264541759064787462) * 10 ^ 70 +
        1351062839558912586589317629050864417275679028650804027868457254440719) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 130 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_218_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_219 :
    recurrence5Scalar0Exceptional.coeff 219 =
      ((((((85089970 * 10 ^ 70 +
        0841018599604080666416080552889860851145914220137349765275709861175428) * 10 ^ 70 +
        3077661823374036748840610815816239541498667705774986451046555041971432) * 10 ^ 70 +
        1875479019052224093363585277498976655909713784426132779637457913701627) * 10 ^ 70 +
        1303835031586932377218254775243362704159543253523151942410747524034660) * 10 ^ 70 +
        2234938217202014235504511712389119963507453525484194396637991460119653) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 131 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_219_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
