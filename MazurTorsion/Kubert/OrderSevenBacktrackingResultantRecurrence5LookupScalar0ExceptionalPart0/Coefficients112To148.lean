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

private theorem recurrence5Scalar0Exceptional_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_112 :
    recurrence5Scalar0Exceptional.coeff 112 =
      (((((1104880774280823040204930667 * 10 ^ 70 +
        8953138231183013789872739503739472902250235625837132104282079392778418) * 10 ^ 70 +
        8083444488455445853481925574018763799321219474214420615975606514635625) * 10 ^ 70 +
        3819987323241649486515414522732376607603739431567066637923767309491345) * 10 ^ 70 +
        9612347463229900050114843031892980998754437112085724305044043309345006) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 24 +
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
  rw [recurrence5Scalar0Exceptional_coeff_112_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_113 :
    recurrence5Scalar0Exceptional.coeff 113 =
      -(((((14468026686154964166189005669 * 10 ^ 70 +
        0694802218126329301889882843554050013286589113381838542300573334322571) * 10 ^ 70 +
        7260072171299780881426986473396057470595791161471079541632156360781641) * 10 ^ 70 +
        5553931607594072256150248142448047189737513703780119942608337044654928) * 10 ^ 70 +
        7687621341368209577425972612532434236182294218751454265782976155740930) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 25 +
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
  rw [recurrence5Scalar0Exceptional_coeff_113_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_114 :
    recurrence5Scalar0Exceptional.coeff 114 =
      (((((105723714838829024319942507433 * 10 ^ 70 +
        9383989925555265582285106211193813432543893107648890791605946750638017) * 10 ^ 70 +
        6175355793006395146572340174588200899410100922757700093463724778084382) * 10 ^ 70 +
        3238757941403509293526921524333530300974180345596429539058525070467847) * 10 ^ 70 +
        8410775535975408020228062027597507826032404650742866868954467117195470) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 26 +
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
  rw [recurrence5Scalar0Exceptional_coeff_114_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_115 :
    recurrence5Scalar0Exceptional.coeff 115 =
      -(((((531339370582907138657385702563 * 10 ^ 70 +
        6407342016161978396311598525472449675967644870109804965916930534083413) * 10 ^ 70 +
        7746581222699913340367355162412156747453367874952414644935492997884056) * 10 ^ 70 +
        3538442689975873443253825430212119389366791461407664870542310815554879) * 10 ^ 70 +
        2909363181707854360379736225011181953961611968802434660212915038021103) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 27 +
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
  rw [recurrence5Scalar0Exceptional_coeff_115_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_116 :
    recurrence5Scalar0Exceptional.coeff 116 =
      (((((1480003749457405205315994300055 * 10 ^ 70 +
        1937069761053764626381956608896436738150066939435785022133617486930824) * 10 ^ 70 +
        5203772193380966799187365321230008476867434002876635060141501232368685) * 10 ^ 70 +
        4729029781161410171430325097716258379960268072053277830879620934787545) * 10 ^ 70 +
        6633816548560200217428250863000621471540450950702692682763866203696936) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 28 +
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
  rw [recurrence5Scalar0Exceptional_coeff_116_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_117 :
    recurrence5Scalar0Exceptional.coeff 117 =
      (((((4194752586840221997761876842022 * 10 ^ 70 +
        8649790646137378021451949444531832763853508841150428706347200602141703) * 10 ^ 70 +
        7805650925635614190378860400776356688782285954583345537444921986168841) * 10 ^ 70 +
        3823344667236379032327874744463819720211917242531685721172448526375983) * 10 ^ 70 +
        1440463563114179247932795270935826657215250373876476243650412680224517) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 29 +
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
  rw [recurrence5Scalar0Exceptional_coeff_117_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_118 :
    recurrence5Scalar0Exceptional.coeff 118 =
      -(((((92666027141130428401528477468406 * 10 ^ 70 +
        1772515268276874074982672322927810992466979863292551102505114719341855) * 10 ^ 70 +
        9389347053496721211801058861500006847833104850979827891801968223004906) * 10 ^ 70 +
        3092907169408854810337680154674209481061923324174618468387523119021856) * 10 ^ 70 +
        8053676811258020628888495625056134522671870001630996362203707199429458) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 30 +
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
  rw [recurrence5Scalar0Exceptional_coeff_118_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_119 :
    recurrence5Scalar0Exceptional.coeff 119 =
      (((((760137971743796360944392655310933 * 10 ^ 70 +
        8126300129781238062921895967865957504860031477407823642001886915791333) * 10 ^ 70 +
        7542717107261251763740454272155571460425265779145738036971110172639863) * 10 ^ 70 +
        4313298274540222554946777044750817307709317049634759647996567155939634) * 10 ^ 70 +
        5010923366056088722212899905277159069853636211877201966342461512670723) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 31 +
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
  rw [recurrence5Scalar0Exceptional_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_120 :
    recurrence5Scalar0Exceptional.coeff 120 =
      -(((((4257401853940287024141484511589128 * 10 ^ 70 +
        7791158553120336470694283677302785769113174858547936753525258714243271) * 10 ^ 70 +
        5373547225216654073908206486145086823516671546889044800563140279611557) * 10 ^ 70 +
        6493877528073124727779615209156231772251758354622261398275831298215056) * 10 ^ 70 +
        4212776068109801843768850590668397934055351141158199574467797708549857) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 32 +
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
  rw [recurrence5Scalar0Exceptional_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_121 :
    recurrence5Scalar0Exceptional.coeff 121 =
      (((((16005913016390552498228726839409483 * 10 ^ 70 +
        5811244185490589474942847237960497214269916560520931839250917554286588) * 10 ^ 70 +
        6324944825454348088491794895109512659612610335247099284823186954402323) * 10 ^ 70 +
        4350486132885514540583916996364932399541588655325867038230522663291503) * 10 ^ 70 +
        9315712066749271513785840300775083032033937300629999860989122945215867) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 33 +
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
  rw [recurrence5Scalar0Exceptional_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_122 :
    recurrence5Scalar0Exceptional.coeff 122 =
      -(((((16209498422467029099285705693095734 * 10 ^ 70 +
        4725899599557405926026288218999911284372034300257212546300228310402068) * 10 ^ 70 +
        8672281251252646310860678351091663396006981481324224295561632324334187) * 10 ^ 70 +
        6404956979357929313035996756762353382918374395883310621902119912700857) * 10 ^ 70 +
        3468554845354011045824133350226413831362990301639271462420889730683726) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 34 +
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
  rw [recurrence5Scalar0Exceptional_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_123 :
    recurrence5Scalar0Exceptional.coeff 123 =
      -(((((347266389912696859903632415911325688 * 10 ^ 70 +
        5414335730843174046429817852454570576878453660242240956873221659463014) * 10 ^ 70 +
        6166725472905363779305446481714632993031017082104388579364098295759087) * 10 ^ 70 +
        3027251398475301157911302120539233791523102489249125809612967780015227) * 10 ^ 70 +
        9727016045554948173563094944493867740572921696747132162835230425891798) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 35 +
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
  rw [recurrence5Scalar0Exceptional_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_124 :
    recurrence5Scalar0Exceptional.coeff 124 =
      (((((3741277779746653137803312423166139468 * 10 ^ 70 +
        8673223700383172837552162304855769452423956415232016949758440202531294) * 10 ^ 70 +
        2915839134965768124998596393990376354008295911570636553146334690660255) * 10 ^ 70 +
        9635680234304328851805461811938900906481518833444741221421389411303605) * 10 ^ 70 +
        5706063279818182640460343019581278122414992457091639038120032700370581) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 36 +
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
  rw [recurrence5Scalar0Exceptional_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_125 :
    recurrence5Scalar0Exceptional.coeff 125 =
      -(((((24284377304838151755457273176033991854 * 10 ^ 70 +
        0881970033172193948601319671809663413707377638398688534038961985595126) * 10 ^ 70 +
        2785513577723757344206457573753907301576279910311814419604075109495757) * 10 ^ 70 +
        8606912912651943691851422919269896525111165028488230323002326415606611) * 10 ^ 70 +
        4900437444648193113950762093787669850414816097375056871011813210999786) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 37 +
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
  rw [recurrence5Scalar0Exceptional_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_126 :
    recurrence5Scalar0Exceptional.coeff 126 =
      (((((113604807578191660630902342103617802314 * 10 ^ 70 +
        9092956377486510419869255915482636705347342408777282770374105021090144) * 10 ^ 70 +
        9552893516412449198727713067110975138893779337967467506941824884070181) * 10 ^ 70 +
        3013082516273798348874486164056577802329862939173543397439891532283810) * 10 ^ 70 +
        8949274732738188317811004087485633264734682702497081721859925953328855) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 38 +
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
  rw [recurrence5Scalar0Exceptional_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_127 :
    recurrence5Scalar0Exceptional.coeff 127 =
      -(((((338743345484893889645178543321196697054 * 10 ^ 70 +
        4404675008955808039025450949614006332355717995839939503932162119747949) * 10 ^ 70 +
        5240769581298742853586002550259185034401872041366324842547351465515936) * 10 ^ 70 +
        3681878003979495380428878132042051811869997009486091604451051397862088) * 10 ^ 70 +
        0077195593014802253962314759553896987931734597244734700960224683660757) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 39 +
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
  rw [recurrence5Scalar0Exceptional_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_128 :
    recurrence5Scalar0Exceptional.coeff 128 =
      -(((((133503565551409458681214526741047078283 * 10 ^ 70 +
        4071805187288583010283542501267783445030404062292056283401599875863254) * 10 ^ 70 +
        1617060267199987515244949282455389328590760324783115890727735575665640) * 10 ^ 70 +
        8337719828171835184951086217672956053968944579584994232602248898331523) * 10 ^ 70 +
        1427917374952521188480173551295797941165632490996163946296960185466022) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 40 +
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
  rw [recurrence5Scalar0Exceptional_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_129 :
    recurrence5Scalar0Exceptional.coeff 129 =
      (((((10573213321558467658500218475448496726940 * 10 ^ 70 +
        3918003925869018515641816435843998920384889275646860691313212958888849) * 10 ^ 70 +
        7864231960065608311162926414227215876996351692840532877817828234431280) * 10 ^ 70 +
        9869023349036964215295319685382577817810750373085430440930821530456725) * 10 ^ 70 +
        9863928697941836859369231623590124060311620647092831428367761395665186) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 41 +
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
  rw [recurrence5Scalar0Exceptional_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_130 :
    recurrence5Scalar0Exceptional.coeff 130 =
      -(((((90930050871071634321962468066563477054503 * 10 ^ 70 +
        1488789167571382772784485893518020978474399637806264157415915210935499) * 10 ^ 70 +
        2764013215510983686021086388693808966397987694049999232927112362128878) * 10 ^ 70 +
        7066835651923875790012158945319462518771710058843336750649573872998734) * 10 ^ 70 +
        9060818077387483212820726098711764422214367547702134455403214717647761) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 42 +
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
  rw [recurrence5Scalar0Exceptional_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_131 :
    recurrence5Scalar0Exceptional.coeff 131 =
      (((((526348491439777504513919000761750152357460 * 10 ^ 70 +
        8096442514934612473863467076316125445591287833695572539681058572973635) * 10 ^ 70 +
        8141745922450482827777171463577129701335240648202566896311321998674168) * 10 ^ 70 +
        6483227120911636460981935409723117992566621298189430988149163681467063) * 10 ^ 70 +
        1990651594327377805273001266330778455767664766784482508713641554829515) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 43 +
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
  rw [recurrence5Scalar0Exceptional_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_132 :
    recurrence5Scalar0Exceptional.coeff 132 =
      -(((((2271142482640730410131208225951566968802072 * 10 ^ 70 +
        9057114815117080716104273780207567523188393445135136391366656506072691) * 10 ^ 70 +
        6564259493412037506885445510561678275172252075816389212109798654136249) * 10 ^ 70 +
        4822761637505880941441703476518102805074797381601027136277759540398657) * 10 ^ 70 +
        1544189575384869981642987582611128782088442586144486907089277291254271) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 44 +
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
  rw [recurrence5Scalar0Exceptional_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_133 :
    recurrence5Scalar0Exceptional.coeff 133 =
      (((((6433493684854417084826248361559165544154395 * 10 ^ 70 +
        3485392139113147972916215471696330695383869132020888457175861316294786) * 10 ^ 70 +
        1307511814740046234155410167053653059671798657206830022229038060518469) * 10 ^ 70 +
        1156609855516438990216759936317823695650447372845345202345852415459383) * 10 ^ 70 +
        8546906582852564875904500802739753334428733817656361344009075806359977) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 45 +
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
  rw [recurrence5Scalar0Exceptional_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_134 :
    recurrence5Scalar0Exceptional.coeff 134 =
      (((((1011951259214910584337073761131256443290788 * 10 ^ 70 +
        3730294774035908440652611997202534819380345895818179776024711553406678) * 10 ^ 70 +
        6152367424082239121441072688498939100387959961641406086474454182009395) * 10 ^ 70 +
        4204898030936236169912529363479704517853051168592159285782358999882285) * 10 ^ 70 +
        4079360118821031923110312681293700455582202829182724849033300931111820) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 46 +
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
  rw [recurrence5Scalar0Exceptional_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_135 :
    recurrence5Scalar0Exceptional.coeff 135 =
      -(((((167334732688652395230873110004624232449436838 * 10 ^ 70 +
        7134091279639842785270149645280263231190348242376527853336964300047021) * 10 ^ 70 +
        6037196503680204837848729414029419236656090782775186453238984111436217) * 10 ^ 70 +
        5043417280343223185459210916780634883431427933130347349503862252687280) * 10 ^ 70 +
        0442548811812774444836742079901341787211862756866666423421153183009885) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 47 +
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
  rw [recurrence5Scalar0Exceptional_coeff_135_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_136 :
    recurrence5Scalar0Exceptional.coeff 136 =
      (((((1415018711939226040194772028409440812260738085 * 10 ^ 70 +
        1075117670280321308288187237377145862719257800175483595087282176494024) * 10 ^ 70 +
        2873531362425776952160020825927827710242220334769569992483691026826975) * 10 ^ 70 +
        0517796994232295460143296239955891671563927457768043793517607311517560) * 10 ^ 70 +
        3614607090500284694209720390657609225719897904141406031385038473409579) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 48 +
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
  rw [recurrence5Scalar0Exceptional_coeff_136_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_137 :
    recurrence5Scalar0Exceptional.coeff 137 =
      -(((((8126309234369952038477011288252929362803203944 * 10 ^ 70 +
        6894393427157239293437402310961223241275184597877059986444422266171757) * 10 ^ 70 +
        9337878309238944841541287666500862692718904100640246675937714966472429) * 10 ^ 70 +
        3594817980156280835754682329448496180639495084647102898133690466986615) * 10 ^ 70 +
        0992621877821300237591713757850768321192448697096985505629615292447259) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 49 +
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
  rw [recurrence5Scalar0Exceptional_coeff_137_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_138 :
    recurrence5Scalar0Exceptional.coeff 138 =
      (((((36093836761652156229760399898655938744360303185 * 10 ^ 70 +
        5246502943910003876730723087130628385756704782335088524290045981014405) * 10 ^ 70 +
        7082579941833765398058224959042962692588147887940567828934135777327555) * 10 ^ 70 +
        6403461595490504230526838066004171670714194916442384716251868195318660) * 10 ^ 70 +
        2441249181605238519432395456073881062743587079586950135156723943338519) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 50 +
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
  rw [recurrence5Scalar0Exceptional_coeff_138_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_139 :
    recurrence5Scalar0Exceptional.coeff 139 =
      -(((((119065973921396929711923938347197565612754627519 * 10 ^ 70 +
        8569668511534196710042548726207718331033213116991237133357684690322353) * 10 ^ 70 +
        8678968086796375788764787539839452783653850208103545764065104880524284) * 10 ^ 70 +
        5949336849357809115256749104360735529092562071528037775645682534350608) * 10 ^ 70 +
        4974046247317058708363674478949953165450179359772417047834676975583219) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 51 +
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
  rw [recurrence5Scalar0Exceptional_coeff_139_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_140 :
    recurrence5Scalar0Exceptional.coeff 140 =
      (((((189457153594056564608977735758520534721893222335 * 10 ^ 70 +
        3972310349779186723697110556056255673836194850648690410779813812226704) * 10 ^ 70 +
        7242093798466208553314850486164817894757823706013170988996713728748166) * 10 ^ 70 +
        7756680451661534678744014241463484217156424721022429711614874506540014) * 10 ^ 70 +
        6241562569250823622657501495548899338936560622129076033509133340950238) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 52 +
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
  rw [recurrence5Scalar0Exceptional_coeff_140_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_141 :
    recurrence5Scalar0Exceptional.coeff 141 =
      (((((1044456211767639054107931508478307088982195544896 * 10 ^ 70 +
        9584841051454474928439464543611662780905418547578248388291889491377277) * 10 ^ 70 +
        7745686708802592000381369027216273488703353372358181161121810950840493) * 10 ^ 70 +
        1945824940330383293173044302965008091373891187711767121983719558760429) * 10 ^ 70 +
        4856330692034227597831616218787859313914513302744924363325295716370622) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 53 +
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
  rw [recurrence5Scalar0Exceptional_coeff_141_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_142 :
    recurrence5Scalar0Exceptional.coeff 142 =
      -(((((12787879059958233939913400243014811480468859696342 * 10 ^ 70 +
        0435108195113533079210445019508981022917206081218630756275788991078878) * 10 ^ 70 +
        2320103134484302844862006013687498709903643689406605198286514776511624) * 10 ^ 70 +
        3646981136321218484084738534222603839904628714947464120585922478381686) * 10 ^ 70 +
        0553611510847141480519357076957031224120331686152204754109277475235776) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 54 +
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
  rw [recurrence5Scalar0Exceptional_coeff_142_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_143 :
    recurrence5Scalar0Exceptional.coeff 143 =
      (((((83482148941455734061145958113069469229188714001113 * 10 ^ 70 +
        2838183183412045147500838167069615424598344286231601526287492561468139) * 10 ^ 70 +
        8040525865694820280709801945523485947092840508949506535460368410036278) * 10 ^ 70 +
        0083134370441136460798133921159344534163338488378194544798071172678232) * 10 ^ 70 +
        9301107070616782556990491164046841838325900114224347541155934641961242) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 55 +
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
  rw [recurrence5Scalar0Exceptional_coeff_143_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_144 :
    recurrence5Scalar0Exceptional.coeff 144 =
      -(((((419071096205044107623307026454397124018081517968020 * 10 ^ 70 +
        6508521231167292680525098383321534690869892781377802144713146106902327) * 10 ^ 70 +
        9266948543826801255287234300494232085294378409488716264408137083388538) * 10 ^ 70 +
        1108950461455994512839108636597355691584680357162473928177827556356354) * 10 ^ 70 +
        0435404865945810633731725983447130273562132523406270664812821809253928) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 56 +
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
  rw [recurrence5Scalar0Exceptional_coeff_144_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_145 :
    recurrence5Scalar0Exceptional.coeff 145 =
      (((((1713118177403843530162646415006599304054454812454720 * 10 ^ 70 +
        6412642361773187738029424042631108855648339835209443954929509316734100) * 10 ^ 70 +
        3175633475360692746681380757131753346176798495415107828737694475863022) * 10 ^ 70 +
        6365708587151342319459004910206737925079639131845890200190226211820658) * 10 ^ 70 +
        9704607087525138119695960659579532281648556872117420576759654675590154) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 57 +
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
  rw [recurrence5Scalar0Exceptional_coeff_145_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_146 :
    recurrence5Scalar0Exceptional.coeff 146 =
      -(((((5483520256161502296293233482780588549586807554639967 * 10 ^ 70 +
        9993696115497077006600914816210614923875183583778311862719117771877765) * 10 ^ 70 +
        8041717247050154300729841366194163323234377617942731340099684166891865) * 10 ^ 70 +
        1934444891839951934001681753115987035589788304467615726667778314033155) * 10 ^ 70 +
        4710155142612093495710700460174009212965669619869702147214587315693886) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 58 +
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
  rw [recurrence5Scalar0Exceptional_coeff_146_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_147 :
    recurrence5Scalar0Exceptional.coeff 147 =
      (((((10425486673945173634986981709561745187705025063223498 * 10 ^ 70 +
        5585175442397778284735761648612572657654062752403400703238679725503844) * 10 ^ 70 +
        6136370795936600513313442119925097642487003763218960054830044607102924) * 10 ^ 70 +
        6791185234360463460338298589771201195834055330001756242531315855172920) * 10 ^ 70 +
        2676956779855537801016054005378416280395954301776887193070892827573971) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 59 +
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
  rw [recurrence5Scalar0Exceptional_coeff_147_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_148 :
    recurrence5Scalar0Exceptional.coeff 148 =
      (((((22885884442987911215564246266432813753042453680975937 * 10 ^ 70 +
        8670482767643677585160815563930976118527095669170287123162650765237272) * 10 ^ 70 +
        3277875243707608168459640821451504284284844326809402854443871128946874) * 10 ^ 70 +
        5974327627233891165052182031779996360176712043452335228091243945703497) * 10 ^ 70 +
        0825914851368913278622045210698934981245228857016104024577467388710425) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 60 +
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
  rw [recurrence5Scalar0Exceptional_coeff_148_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
