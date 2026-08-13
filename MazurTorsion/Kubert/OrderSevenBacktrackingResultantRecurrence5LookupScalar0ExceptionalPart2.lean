/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0ExceptionalPart2Simp
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

private theorem recurrence5Scalar0Exceptional_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (394 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_394 :
    recurrence5Scalar0Exceptional.coeff 394 =
      -(((((77345270845855690155203 * 10 ^ 70 +
        9295557180695174398236922244471347645101385770742076768031037929080254) * 10 ^ 70 +
        8876654378213818432357119789763554329670381066986884780338370646350906) * 10 ^ 70 +
        6403973090574219220095171801042521765913412969149619478943159699024444) * 10 ^ 70 +
        2086275592096313350130131414124526887144969889552775676232792965894754) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 395 = 306 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 9 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_394_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (395 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_395 :
    recurrence5Scalar0Exceptional.coeff 395 =
      (((((18216491553304888315811 * 10 ^ 70 +
        8363266887892740334652424229203789027851519533476094854123761968052154) * 10 ^ 70 +
        7647820784561534008126098595398383125126300645887988710594501197097281) * 10 ^ 70 +
        0022883346265648168900092536501722798858413784571652589786623544401525) * 10 ^ 70 +
        3089457265919913549332060011948509957314610143313224919812618071281551) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 396 = 307 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 8 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_395_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (396 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_396 :
    recurrence5Scalar0Exceptional.coeff 396 =
      -(((((3947043134145662615037 * 10 ^ 70 +
        3467399555865388088696848135267694850810263866774469835103367003790870) * 10 ^ 70 +
        0776046625690072770467626957917733527901433677501908677821992364412721) * 10 ^ 70 +
        1237882730542570349965573846310158265575029858254810116170308259351926) * 10 ^ 70 +
        2860379928648044184954163626102149253925573588184877476223432466071794) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 397 = 308 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 7 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_396_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (397 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_397 :
    recurrence5Scalar0Exceptional.coeff 397 =
      (((((784890252251120680332 * 10 ^ 70 +
        5929692987552133768757799239042328306322407578627286525856803911713615) * 10 ^ 70 +
        0220061216569071603933498628728147687286467131863605014113783376163502) * 10 ^ 70 +
        4411601535374520411169492198426330797577732810667603652799414934687620) * 10 ^ 70 +
        2073308280373367400586410205219780330735224674557827237983491578787599) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 398 = 309 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 6 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (398 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_398 :
    recurrence5Scalar0Exceptional.coeff 398 =
      -(((((141874039109841500383 * 10 ^ 70 +
        2261727466544959764363144773916249794677609371393160696808093453730978) * 10 ^ 70 +
        0712395983692993646369114964938052256353134265972777183018076596163264) * 10 ^ 70 +
        2679889647331741308039541248568662884275452919741357257809426616478722) * 10 ^ 70 +
        1226543201500069104060573985105726913379875511459908873641929158941128) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 399 = 310 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 5 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (399 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_399 :
    recurrence5Scalar0Exceptional.coeff 399 =
      (((((22792143160350716220 * 10 ^ 70 +
        7743716172815101066012873838956053089181400955017493551424018109586680) * 10 ^ 70 +
        6238920102274352555159305596826294407427325807807501476242860519786215) * 10 ^ 70 +
        2331408426814071296250806431333340666916700085285744753847923644896940) * 10 ^ 70 +
        8143193773812571957027961807874047041793181676709259726980841649346847) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 400 = 311 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 4 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (400 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_400 :
    recurrence5Scalar0Exceptional.coeff 400 =
      -(((((3079160826700829944 * 10 ^ 70 +
        7925041956940244587444844571134665056624112085171358371538865066477479) * 10 ^ 70 +
        9584273840905957953219233293387332246192093766133999400244093182321465) * 10 ^ 70 +
        1512082698366058850369629976814671727715160418460741580689767454570878) * 10 ^ 70 +
        6947190200022156503097511174623044610800415098214477380183642780043246) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 401 = 312 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 3 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (401 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_401 :
    recurrence5Scalar0Exceptional.coeff 401 =
      (((((289648779165751908 * 10 ^ 70 +
        7177442380123217570512045090606172812870339676992117612160579560992567) * 10 ^ 70 +
        4456449494635999753700536304577282126680993176135643458877836287632337) * 10 ^ 70 +
        1853853348701449768499515097486887195627405815694140370666489957330018) * 10 ^ 70 +
        0211918647133150179773928065414560818646340904760656439384122974487305) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 402 = 313 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 2 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (402 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_402 :
    recurrence5Scalar0Exceptional.coeff 402 =
      (((((4389490972671374 * 10 ^ 70 +
        4284817293028042563832865931396469686071148350970962036353776557569652) * 10 ^ 70 +
        6756873611623659748591845912217347170774965655456333433561867216201860) * 10 ^ 70 +
        3598624699220745014742238213095696620227581136318588228463265547055280) * 10 ^ 70 +
        2747234117828037916310502824280611900086095885207280169496577505752907) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 403 = 314 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 1 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (403 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_403 :
    recurrence5Scalar0Exceptional.coeff 403 =
      -(((((11241903607761852 * 10 ^ 70 +
        4405210232693890484858960697152982885704359699493414799180017108212923) * 10 ^ 70 +
        8886242195632410505542594597830171125380842460332001054424733524329695) * 10 ^ 70 +
        6383098692949975821209802292811543215642666618127428106735515423236690) * 10 ^ 70 +
        3714025171403901815785401181628837204407672907682482207614010628006863) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 404 = 315 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (404 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_404 :
    recurrence5Scalar0Exceptional.coeff 404 =
      (((((3709823144195512 * 10 ^ 70 +
        0958391530352887730973837220073045853569932480643373185603126743572643) * 10 ^ 70 +
        0600434158768522000153583386625247738009520438474197432395780597985302) * 10 ^ 70 +
        5403224403101829092361138957677449182006014171240354322258358339483923) * 10 ^ 70 +
        4052003233596325556581378760392173025254401451618905908347157241720071) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 405 = 316 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 31 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (405 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_405 :
    recurrence5Scalar0Exceptional.coeff 405 =
      -(((((900198612061336 * 10 ^ 70 +
        1208091692674098392145888944592074277488388825525032478094864387943751) * 10 ^ 70 +
        6319994101031250831920962454119088353833399976875381420556997472330480) * 10 ^ 70 +
        9166635367286194892646794435345472307647931069446911013856503348573002) * 10 ^ 70 +
        6429207033272733780121189021464778230340893192181416242769181241429203) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 406 = 317 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 30 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (406 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_406 :
    recurrence5Scalar0Exceptional.coeff 406 =
      (((((187231429501605 * 10 ^ 70 +
        6315846815554847207835961148334784430737671199380537197855805748472586) * 10 ^ 70 +
        0282726214032120410014867203741800708652592700331926058176403216228999) * 10 ^ 70 +
        7166122027716649201289971171995554386185454259007765701144222024409684) * 10 ^ 70 +
        8507285385519161884114852824463477780704746833020736914219324232938031) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 407 = 318 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 29 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (407 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_407 :
    recurrence5Scalar0Exceptional.coeff 407 =
      -(((((35097816863408 * 10 ^ 70 +
        3419977986578310369004521187463638647629734416254207834424979942408057) * 10 ^ 70 +
        8623716063055324453287185760682335509777113051833066683385885379197999) * 10 ^ 70 +
        4753030223891673723992513013931393103946495559143005934549049447240260) * 10 ^ 70 +
        1839844881920623691638741418717977577391523834493113044312412709980628) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 408 = 319 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 28 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (408 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_408 :
    recurrence5Scalar0Exceptional.coeff 408 =
      (((((6065613611268 * 10 ^ 70 +
        5353418120535471077114631726975246759220209516219807059284369378426140) * 10 ^ 70 +
        0348661078635956730782765344488127047847168373283649449439211868461506) * 10 ^ 70 +
        5648292032591719449230199676338837093242870955448470051679901720898628) * 10 ^ 70 +
        0708995832669086775962446038001575103751902808227817020259285161766687) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 409 = 320 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 27 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (409 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_409 :
    recurrence5Scalar0Exceptional.coeff 409 =
      -(((((977749413082 * 10 ^ 70 +
        7519193203666010495583440190137415505921815684355800351066949309554832) * 10 ^ 70 +
        2308698006329106005577429250625562580775376230154900057825195659412938) * 10 ^ 70 +
        7893966918641514540796675636326866812799864983377309444099526150010111) * 10 ^ 70 +
        7194820008749022481433807002628689810314045940656440103567261968175097) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 410 = 321 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 26 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (410 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_410 :
    recurrence5Scalar0Exceptional.coeff 410 =
      (((((147897572442 * 10 ^ 70 +
        2514267155707562379222787452984845044180967610936512562524657478710352) * 10 ^ 70 +
        8225909805099659292042527140037299225182422537489520919125870099757018) * 10 ^ 70 +
        3322840580069327808243791764972102386632065664505033565149436864184980) * 10 ^ 70 +
        0501283182618183013157418943137149205743489960143445187473044080704685) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 411 = 322 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 25 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (411 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_411 :
    recurrence5Scalar0Exceptional.coeff 411 =
      -(((((21046343461 * 10 ^ 70 +
        3244501620952528309310243565309943051896488350572632694026760602725198) * 10 ^ 70 +
        4882426076286531233295032916160819181549979150896367152272541125160338) * 10 ^ 70 +
        3345600445398091781739820751087582117219127651133684454938189354408134) * 10 ^ 70 +
        3768744163751268353935784169928066619611346554991738108857333888470388) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 412 = 323 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 24 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (412 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_412 :
    recurrence5Scalar0Exceptional.coeff 412 =
      (((((2817587502 * 10 ^ 70 +
        5287048111378207078624664447343563155740524587803582344208364685323460) * 10 ^ 70 +
        5492854516698331462992742733404857290008520887297567771915903476483189) * 10 ^ 70 +
        8157863816168026767238520800129743827471668306895222257706726166796241) * 10 ^ 70 +
        9249596197630373582591654533539707302687268113525118489724627890937772) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 413 = 324 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 23 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (413 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_413 :
    recurrence5Scalar0Exceptional.coeff 413 =
      -(((((354147697 * 10 ^ 70 +
        1517999110721382039355229737775328051103654745727979619929545849208551) * 10 ^ 70 +
        1388646752775103097253028605521413692574078432108559183382491500989999) * 10 ^ 70 +
        3604644663768626334661173634235033287494215569339950073516435409658171) * 10 ^ 70 +
        8876694955940030257009144160853883682119170580397990923382009313966070) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 414 = 325 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 22 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (414 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_414 :
    recurrence5Scalar0Exceptional.coeff 414 =
      (((((41633493 * 10 ^ 70 +
        6018816414673958633250959422231598234522978771369146481364836643369269) * 10 ^ 70 +
        1800876562829783613835684754000493574024260547537441085871289282494961) * 10 ^ 70 +
        3379160518110002566034793969300584866270256330810635056962242992696247) * 10 ^ 70 +
        9142250750498308092389439561673844080791817693339159668440364550064381) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 415 = 326 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 21 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (415 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_415 :
    recurrence5Scalar0Exceptional.coeff 415 =
      -(((((4552280 * 10 ^ 70 +
        7890392241673387048773440158607059297474462051321275169560694137302318) * 10 ^ 70 +
        6199539464376756872575743055066477700328734559416619225763848845300023) * 10 ^ 70 +
        6106250491852403026009813600303828988421276022589809969567058293643465) * 10 ^ 70 +
        9446270339544846888715234094046284291992403066538825745205932461941373) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 416 = 327 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 20 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (416 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_416 :
    recurrence5Scalar0Exceptional.coeff 416 =
      (((((459426 * 10 ^ 70 +
        0927645754041850389569714600637964762771788213221734924028476622606489) * 10 ^ 70 +
        8115310851996514218093166248363635802517824464430969068371553434235819) * 10 ^ 70 +
        5148291176196323457297370174238106926165804626431404994949320832174977) * 10 ^ 70 +
        8848339227355423122614463757500016822248985501915922235975690881329705) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 417 = 328 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 19 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (417 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_417 :
    recurrence5Scalar0Exceptional.coeff 417 =
      -(((((42342 * 10 ^ 70 +
        5645723821521160647871282151228423279148356127686325316121962139117973) * 10 ^ 70 +
        3179684916752009347375469200126364833502243514652702115917776356423821) * 10 ^ 70 +
        6907322014090931543520362964005438250212083952310719775532941424491569) * 10 ^ 70 +
        5660878616555814853297705355584378483517127009094007164426574258760122) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 418 = 329 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 18 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (418 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_418 :
    recurrence5Scalar0Exceptional.coeff 418 =
      (((((3507 * 10 ^ 70 +
        7667033221750935751552120487065423469950401631938979617788728701786769) * 10 ^ 70 +
        5123726462210860560332635836757509902602972195659964361207908718118041) * 10 ^ 70 +
        0156101399916912201619170441433559437745478164440154770571390103383656) * 10 ^ 70 +
        1925876646137354139859330824632182912132400829058178947341889410631313) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 419 = 330 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 17 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (419 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_419 :
    recurrence5Scalar0Exceptional.coeff 419 =
      -(((((254 * 10 ^ 70 +
        3240513684944549739156763828610645256321833825294010116567170254194306) * 10 ^ 70 +
        5031878370170214456631252058581582386990644598584620734688383291574989) * 10 ^ 70 +
        8006110576749853355990397621497849365832438717873970810016355970024990) * 10 ^ 70 +
        0012581098008873545451759826969577766003455027577473405452122485330970) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 420 = 331 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 16 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (420 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_420 :
    recurrence5Scalar0Exceptional.coeff 420 =
      (((((15 * 10 ^ 70 +
        2757586973113462451913080227875802724207377378009140456292370962597648) * 10 ^ 70 +
        2032840759049644184992392226569722154219727456353755290169632926735147) * 10 ^ 70 +
        7842081119787319907143943768625995757874274118513316401566612568490263) * 10 ^ 70 +
        7315951585867174440016499771417713360228321413985816470657464819223767) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 421 = 332 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 15 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (421 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_421 :
    recurrence5Scalar0Exceptional.coeff 421 =
      -((((6458393964752461846182614682650238985746919289619752828934211145509127 * 10 ^ 70 +
        8296868051797651978760759767407262250321859853272351449385517653313976) * 10 ^ 70 +
        4596726027277134472327948644615837026718133133935067158450679322815402) * 10 ^ 70 +
        2153687198241620174665332312682602360744629587980543540606651297333514) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 422 = 333 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 14 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (422 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_422 :
    recurrence5Scalar0Exceptional.coeff 422 =
      ((((21972263267242765939765399118167753731120163925975021885401169351380 * 10 ^ 70 +
        9557697065675937845739758987280253483356538453447690644631988321751438) * 10 ^ 70 +
        8052204124426698138993613739313584382712156618192293530081327286048720) * 10 ^ 70 +
        3518141257588419908043788546977368022369875463652594702732218788126180) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 423 = 334 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 13 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (423 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_423 :
    recurrence5Scalar0Exceptional.coeff 423 =
      ((((31189460706433561446477340523414519890020289531547453062439669389546 * 10 ^ 70 +
        6533186413582320660391939230443796540775150695489252974951601014432402) * 10 ^ 70 +
        6037848437781127632024478475637078028068338194222137158445675356006848) * 10 ^ 70 +
        0052721419639735163028627431011369633825501411269701445001020950292334) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 424 = 335 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 12 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (424 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_424 :
    recurrence5Scalar0Exceptional.coeff 424 =
      -((((4058240137991758127049295553008089398043593134360808795233631582034 * 10 ^ 70 +
        0227843479896223299714290830452323111900744395091821800356960549954673) * 10 ^ 70 +
        7243820257712918980946947675093813876947970730598398223750876365033569) * 10 ^ 70 +
        3465485709003152150262308285006699264610450957669470092252654416256886) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 425 = 336 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 11 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (425 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_425 :
    recurrence5Scalar0Exceptional.coeff 425 =
      ((((352809428910882770601828339080716972383876172204306133561277383104 * 10 ^ 70 +
        9693176424924413462614424881285501566646223692868838078258923821725663) * 10 ^ 70 +
        1817516265645171498554048317669579304551575391529263502863537464801833) * 10 ^ 70 +
        9147047494397332194730533360432928533226132718739297208128375333537108) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 426 = 337 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 10 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (426 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_426 :
    recurrence5Scalar0Exceptional.coeff 426 =
      -((((24417314029753413105523991965794536163690931465341637440680840282 * 10 ^ 70 +
        6922747449673300436884963808901779530793679545107745731115327007972137) * 10 ^ 70 +
        1678511292640739390719204567005649410389558248810765528083460150545418) * 10 ^ 70 +
        0439157914496078831001556157945941573775913184572701099911697141204945) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 427 = 338 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 9 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (427 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_427 :
    recurrence5Scalar0Exceptional.coeff 427 =
      ((((1410646318062563624701640179132768862426212708352276600851651239 * 10 ^ 70 +
        5451668478483301771225594227845695659126457431692819704796504003385648) * 10 ^ 70 +
        9818921940625831329199747977364064652469780563769425780265671843496980) * 10 ^ 70 +
        0553343409028968872683110056063836511759811799903844631769234330530591) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 428 = 339 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 8 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (428 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_428 :
    recurrence5Scalar0Exceptional.coeff 428 =
      -((((69037327016417881879288696867664182322376289810388969616436863 * 10 ^ 70 +
        8355273991732298036207116850826724247550680203854547292092643482453750) * 10 ^ 70 +
        5946056234237558073602214553836406175359280570433713847129876492481481) * 10 ^ 70 +
        1283122453220502046429361215902648510101553750651564484212587052046444) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 429 = 340 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 7 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (429 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_429 :
    recurrence5Scalar0Exceptional.coeff 429 =
      ((((2864875860567224304795363636494033296599966419883617354857267 * 10 ^ 70 +
        0058726097831772892321248993881858686905310773293521054961535469490956) * 10 ^ 70 +
        1624343091026237423658208832482963736354209541171489361828496218567912) * 10 ^ 70 +
        3699262550145310121105697428863868954284947267227978848268333023674412) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 430 = 341 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 6 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (430 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_430 :
    recurrence5Scalar0Exceptional.coeff 430 =
      -((((100047007547755426768040253752781292075975520918255480510371 * 10 ^ 70 +
        8708813724620010973979301838005487161214332831063853506256761263265940) * 10 ^ 70 +
        6541975502646798513146955062141291986933284509617976664922737007953982) * 10 ^ 70 +
        1077067940275360130575715125499654577900122555503552970089203223585432) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 431 = 342 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 5 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (431 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_431 :
    recurrence5Scalar0Exceptional.coeff 431 =
      ((((2895621722588107632540237977524738588169081831048617239348 * 10 ^ 70 +
        8286600183857024165799508637263830026420226050406246414885845821903389) * 10 ^ 70 +
        3993837083573537665664332530018610047174451490587485396855176156185684) * 10 ^ 70 +
        8739767012348578257008408594986825846533374127462999379230495505045869) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 343 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 4 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (432 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_432 :
    recurrence5Scalar0Exceptional.coeff 432 =
      -((((67723325762516901317309524878412418554830972524292050152 * 10 ^ 70 +
        0448910771720027757778816333258212062337596736357357146429934189832038) * 10 ^ 70 +
        2144130464774463316834368563081040850446864975229573425901981610245993) * 10 ^ 70 +
        2320977690709834956402062770465220611929118103395963905568086908876693) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 344 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 3 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (433 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_433 :
    recurrence5Scalar0Exceptional.coeff 433 =
      ((((1226468562486913151125963944876964424441136950605747759 * 10 ^ 70 +
        3374283947477385437773088422055962160328906932104459225723041137228419) * 10 ^ 70 +
        1152435425530567250129638937987855887690200753981493656473258292612392) * 10 ^ 70 +
        1451307957028317992763258012677171829294826994503044588278589027613303) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 345 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 2 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (434 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_434 :
    recurrence5Scalar0Exceptional.coeff 434 =
      -((((15815743733639748879153168619000682208050191205414113 * 10 ^ 70 +
        3435293379191993978211032862822532773420517458409301648761846921128771) * 10 ^ 70 +
        6224647752913035985695781497692445786654024504929272387021454046925551) * 10 ^ 70 +
        0025871694934005571036488344883822459185218147136315756406516151445996) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 346 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 1 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (435 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_435 :
    recurrence5Scalar0Exceptional.coeff 435 =
      ((((113879284518893100437981005627191636252929967205103 * 10 ^ 70 +
        7754909742890847160976860661316832127791651217813866098133339135665991) * 10 ^ 70 +
        4259334087108345826408774682347428592939519769743740986766433122148004) * 10 ^ 70 +
        3771137784679222694089903403419244739947115408511400439647982598358021) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 347 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (436 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_436 :
    recurrence5Scalar0Exceptional.coeff 436 =
      ((((211464215646149084610429507201662640247937317504 * 10 ^ 70 +
        2265795328927797498017253506533599356704971898933497879784553537278693) * 10 ^ 70 +
        0767345573880216847253711353715755831463612181178656873811650995249730) * 10 ^ 70 +
        4421670946008758907316354797705871430673555604646939022890282589609837) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 348 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 31 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (437 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_437 :
    recurrence5Scalar0Exceptional.coeff 437 =
      -((((13703883830703199378155063544329234917762265519 * 10 ^ 70 +
        4740187139195993079308266609970745358634859021189236428354199932283919) * 10 ^ 70 +
        7306020617747882770949470403068205817496436403793561570491286311910885) * 10 ^ 70 +
        5084535056698858501994783351876878079547734157135033167302602729898006) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 349 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 30 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (438 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_438 :
    recurrence5Scalar0Exceptional.coeff 438 =
      ((((105518555566008737931821660833346037854165016 * 10 ^ 70 +
        3210228700625882280510427477152419574423271784891577607518974799126182) * 10 ^ 70 +
        3094688407844322897456086801802612800579644269953294160875490533076473) * 10 ^ 70 +
        0441230086409540804991112197915886547142646620659723495500082234880817) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 350 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 29 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (439 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_439 :
    recurrence5Scalar0Exceptional.coeff 439 =
      ((((179919303342914407979379007378192194989680 * 10 ^ 70 +
        2243393474160324309311155866254738881771774183752970227864044534496035) * 10 ^ 70 +
        0107664382467820458085995986874478651008947763922384923775653123539935) * 10 ^ 70 +
        0688025812298970870721894993240942053310087967469650716884816257089042) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 351 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 28 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (440 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_440 :
    recurrence5Scalar0Exceptional.coeff 440 =
      -((((6354605826086295156139353766567219242202 * 10 ^ 70 +
        1758680638844553480124789367460203568140634780533292657698399759708424) * 10 ^ 70 +
        5018479525764997542030882721765384498932090808919750061791938656556237) * 10 ^ 70 +
        4666599100572519808557057413474184063407218251124046610175649474908603) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 352 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 27 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (441 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_441 :
    recurrence5Scalar0Exceptional.coeff 441 =
      ((((16608772610862185415494673588344692180 * 10 ^ 70 +
        2299668985208263564465562017695496980003686565234006746804011700286931) * 10 ^ 70 +
        9326791845111053690098461743518339723211257472241181231943157719302398) * 10 ^ 70 +
        4179596399034506486030144650398328345147982037863445206079725959921828) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 353 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 26 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (442 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_442 :
    recurrence5Scalar0Exceptional.coeff 442 =
      ((((146377672064756283219632441166811737 * 10 ^ 70 +
        3586676604917758595610875572855405522034005945187528055506305135207191) * 10 ^ 70 +
        1038545657586618190303815204017753806857361861317899651211093966255953) * 10 ^ 70 +
        6611041171793419593425215509646721236283636330735689713146025308979279) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 354 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 25 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (443 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_443 :
    recurrence5Scalar0Exceptional.coeff 443 =
      -((((722290024759935906967926491445734 * 10 ^ 70 +
        9116182111853146532078231517728264493958082190913142118887599435999236) * 10 ^ 70 +
        9419238664651322305088739194659712810623590872714636609323185724796355) * 10 ^ 70 +
        9281478295143215507885552182729474813680841553644566248395763111359624) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 355 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 24 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (444 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_444 :
    recurrence5Scalar0Exceptional.coeff 444 =
      -((((1161105538746135323052826635326 * 10 ^ 70 +
        6635517623006908456981424187342750464304892397495920628773940747377419) * 10 ^ 70 +
        2828189887026586183427913996848800528670650924726963251253343611173989) * 10 ^ 70 +
        4478801185950566341153110185724842533769818234143961381123843237848263) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 356 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 23 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (445 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_445 :
    recurrence5Scalar0Exceptional.coeff 445 =
      ((((11851454516712315368264969156 * 10 ^ 70 +
        0402505160186993916691539645322906499888996983833008988203063276451169) * 10 ^ 70 +
        5031549418736322323150214355785565263511779066166119596545936977439287) * 10 ^ 70 +
        5067056289078467747494126384384661366464956730965275719747824387731266) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 357 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 22 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (446 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_446 :
    recurrence5Scalar0Exceptional.coeff 446 =
      -((((8691996386897663822817541 * 10 ^ 70 +
        3639373327948950236374723549411476227449038288193477497047518068813695) * 10 ^ 70 +
        0268221338108692070590023785196038330093598241584206968492943685985935) * 10 ^ 70 +
        1884437145128616417746208750818611229013812190383881043799667377664905) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 358 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 21 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (447 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_447 :
    recurrence5Scalar0Exceptional.coeff 447 =
      -((((79880556059040274065391 * 10 ^ 70 +
        6203838791566277132318901800557478547130095479970884333708908598393264) * 10 ^ 70 +
        5734821792419727423255725753919352260954509340199408828205142356890529) * 10 ^ 70 +
        6311579275391512300304551893015965582038241374255508776984212632612182) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 359 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 20 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (448 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_448 :
    recurrence5Scalar0Exceptional.coeff 448 =
      ((((195624897490888605134 * 10 ^ 70 +
        8614692398434515887889352907414380486615937622596941141113817540366052) * 10 ^ 70 +
        3898120789363128101850341904434887441408910315106032383852726277357556) * 10 ^ 70 +
        2280522381201180747757749476500003688268498290840077360035698566274444) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 360 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 19 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (449 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_449 :
    recurrence5Scalar0Exceptional.coeff 449 =
      ((((25507080927409965 * 10 ^ 70 +
        2956568837545899808800655688948655558093492623772900369912604649978257) * 10 ^ 70 +
        0419832197015624859659165791966547723634424782860816861253380618228587) * 10 ^ 70 +
        3113093351607827844541119697897560150953213123305103821670244878453308) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 361 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 18 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (450 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_450 :
    recurrence5Scalar0Exceptional.coeff 450 =
      -((((761808387235526 * 10 ^ 70 +
        8665136839635829914585058318965476750355680457665905855492253939912318) * 10 ^ 70 +
        7154227250607001285268659506658678287961197493697451722822741144420096) * 10 ^ 70 +
        8628949586214889994162413456611317828313149887419528969013245731047178) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 362 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 17 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (451 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_451 :
    recurrence5Scalar0Exceptional.coeff 451 =
      ((((1412362289790 * 10 ^ 70 +
        3697398449490295455768494217115081731426920378046349285116562983409117) * 10 ^ 70 +
        2787526472253215116684515635456200425309290183258474864566710822135999) * 10 ^ 70 +
        9249899044027173234021253085451056611826786829123543668302151616486069) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 363 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 16 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 364,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (452 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_452 :
    recurrence5Scalar0Exceptional.coeff 452 =
      -((((1309901266 * 10 ^ 70 +
        2757425126691154379158329611793608759917694242287763165629277591525932) * 10 ^ 70 +
        7740468113192184743803052548480296526130352099575027727776712409491698) * 10 ^ 70 +
        7588351067483841623540473308208531988374697849996043237995114842846078) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 364 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 15 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 365,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (453 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_453 :
    recurrence5Scalar0Exceptional.coeff 453 =
      ((((701402 * 10 ^ 70 +
        6457313357109956168280945548341760912179393390580169746461978042499701) * 10 ^ 70 +
        2788258228535505540164889141520951158435962730086098011531508868302922) * 10 ^ 70 +
        4045904179409285946283203877307645083242497072899145492054895291941352) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 365 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 14 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 366,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (454 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_454 :
    recurrence5Scalar0Exceptional.coeff 454 =
      -((((220 * 10 ^ 70 +
        9262003833149304907031495441353409150126726916419426927241056043728689) * 10 ^ 70 +
        4505992310364325816123633449369823419575453834832036230382079653181274) * 10 ^ 70 +
        8004496579212159732977622649670023427442987913430560243042699150366892) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 366 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 13 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 367,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (455 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_455 :
    recurrence5Scalar0Exceptional.coeff 455 =
      (((400985196213749386281352619888341707970171712439632813179282596502683 * 10 ^ 70 +
        0390971515980220488251525611688739251666178591891940363065344762412102) * 10 ^ 70 +
        5484899757726369993083537718086396041596419524989280549452188263341252) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 367 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 12 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 368,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (456 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_456 :
    recurrence5Scalar0Exceptional.coeff 456 =
      -(((40966765262073660205503412486518116854733386364127593815013556201 * 10 ^ 70 +
        2831642827569636698948951883213211007402776573784828005457749803495872) * 10 ^ 70 +
        3621804472839682614035771386517602738914033340601418884256558966713456) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 368 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 11 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 369,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (457 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_457 :
    recurrence5Scalar0Exceptional.coeff 457 =
      (((2292679868978536905215111610177241179173217317989518837561749 * 10 ^ 70 +
        9686158592692410657811504777350109150870448014852007348765227616116699) * 10 ^ 70 +
        8730683150083558763494731470293097351225577520637705884814799463655033) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 369 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 10 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 370,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (458 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_458 :
    recurrence5Scalar0Exceptional.coeff 458 =
      -(((69656923160593820468203547455194930224423503890638957514 * 10 ^ 70 +
        1465310990646597442657175138972377329510910707488292669885548116650100) * 10 ^ 70 +
        2483636461139647057776751136307548093443832286365052771413431680850114) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 370 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 9 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 371,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (459 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_459 :
    recurrence5Scalar0Exceptional.coeff 459 =
      (((1100470868207991767200736666855185568359796120058115 * 10 ^ 70 +
        1886324961286197071057208993546430391741411411658139929598312049025713) * 10 ^ 70 +
        5297268080018555180079345366705011003257391036440228372406599438790332) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 371 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 8 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 372,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (460 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_460 :
    recurrence5Scalar0Exceptional.coeff 460 =
      -(((8155907649470636635977609538894950026089419679 * 10 ^ 70 +
        3966671093218165939439381425166636686999847259677826557857603796153849) * 10 ^ 70 +
        9972806455284753078539972350179135493069347180358431628196736093939379) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 372 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 7 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 373,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (461 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_461 :
    recurrence5Scalar0Exceptional.coeff 461 =
      (((26145763272939291736779951504789362252905 * 10 ^ 70 +
        1265275138124940141509074631389973395286379361071432390597521594119483) * 10 ^ 70 +
        5283409568580949903907189610136028055163736800075473836765000399125391) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 373 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 6 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 374,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (462 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_462 :
    recurrence5Scalar0Exceptional.coeff 462 =
      -(((28677743464355975809049559315569646 * 10 ^ 70 +
        6917445187676667622265610195096641706728788574103741268812342765197736) * 10 ^ 70 +
        8968922041476258180169540852036255021872576485901455675381793298497691) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 374 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 5 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 375,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (463 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (463 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_463 :
    recurrence5Scalar0Exceptional.coeff 463 =
      (((12246368867813283130452395842 * 10 ^ 70 +
        0807078459696831126646293680222825160352363403348824182418715752425890) * 10 ^ 70 +
        0304291641517877090914739525020579196331826325808863517116896036690139) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 464 = 375 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 4 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 376,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (464 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (464 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_464 :
    recurrence5Scalar0Exceptional.coeff 464 =
      -(((1802902733143427314301 * 10 ^ 70 +
        2970968237575783973261419838497337835839810162561658307517857835158225) * 10 ^ 70 +
        6756302430673720143471511501312835298260225564020391356049379427516353) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 465 = 376 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 3 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 377,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (465 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (465 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_465 :
    recurrence5Scalar0Exceptional.coeff 465 =
      (((74602205091237 * 10 ^ 70 +
        4030664558963086751540129878869990068302577092880796181617632625561815) * 10 ^ 70 +
        9026749374745820750768953485355329046150385377810423809115835589857520) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 466 = 377 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 2 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 378,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (466 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (466 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_466 :
    recurrence5Scalar0Exceptional.coeff 466 =
      -(((927037 * 10 ^ 70 +
        4104281385090204337589455937976768067173631172597890319603141623827532) * 10 ^ 70 +
        2427124817368784950967216852004366970391858104331311383428698675793700) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 467 = 378 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 1 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
