/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Exceptional coefficient convolution

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
  recurrence5C1_coeff_0
  recurrence5C1_coeff_1
  recurrence5C1_coeff_2
  recurrence5C1_coeff_3
  recurrence5C1_coeff_4

attribute [local simp]
  recurrence5C1_coeff_5
  recurrence5C1_coeff_6
  recurrence5C1_coeff_7
  recurrence5C1_coeff_8
  recurrence5C1_coeff_9
  recurrence5C1_coeff_10
  recurrence5C1_coeff_11
  recurrence5C1_coeff_12
  recurrence5C1_coeff_13
  recurrence5C1_coeff_14
  recurrence5C1_coeff_15
  recurrence5C1_coeff_16
  recurrence5C1_coeff_17
  recurrence5C1_coeff_18
  recurrence5C1_coeff_19
  recurrence5C1_coeff_20
  recurrence5C1_coeff_21
  recurrence5C1_coeff_22
  recurrence5C1_coeff_23
  recurrence5C1_coeff_24
  recurrence5C1_coeff_25
  recurrence5C1_coeff_26
  recurrence5C1_coeff_27
  recurrence5C1_coeff_28
  recurrence5C1_coeff_29
  recurrence5C1_coeff_30
  recurrence5C1_coeff_31
  recurrence5C1_coeff_32
  recurrence5C1_coeff_33
  recurrence5C1_coeff_34
  recurrence5C1_coeff_35
  recurrence5C1_coeff_36
  recurrence5C1_coeff_37
  recurrence5C1_coeff_38
  recurrence5C1_coeff_39
  recurrence5C1_coeff_40
  recurrence5C1_coeff_41
  recurrence5C1_coeff_42
  recurrence5C1_coeff_43
  recurrence5C1_coeff_44
  recurrence5C1_coeff_45
  recurrence5C1_coeff_46
  recurrence5C1_coeff_47
  recurrence5C1_coeff_48
  recurrence5C1_coeff_49
  recurrence5C1_coeff_50
  recurrence5C1_coeff_51
  recurrence5C1_coeff_52
  recurrence5C1_coeff_53
  recurrence5C1_coeff_54
  recurrence5C1_coeff_55
  recurrence5C1_coeff_56
  recurrence5C1_coeff_57
  recurrence5C1_coeff_58
  recurrence5C1_coeff_59
  recurrence5C1_coeff_60
  recurrence5C1_coeff_61
  recurrence5C1_coeff_62
  recurrence5C1_coeff_63
  recurrence5C1_coeff_64
  recurrence5C1_coeff_65
  recurrence5C1_coeff_66
  recurrence5C1_coeff_67
  recurrence5C1_coeff_68

attribute [local simp]
  recurrence5C1_coeff_69
  recurrence5C1_coeff_70
  recurrence5C1_coeff_71
  recurrence5C1_coeff_72
  recurrence5C1_coeff_73
  recurrence5C1_coeff_74
  recurrence5C1_coeff_75
  recurrence5C1_coeff_76
  recurrence5C1_coeff_77
  recurrence5C1_coeff_78
  recurrence5C1_coeff_79
  recurrence5C1_coeff_80
  recurrence5C1_coeff_81
  recurrence5C1_coeff_82
  recurrence5C1_coeff_83
  recurrence5C1_coeff_84

private theorem recurrence5Scalar1Exceptional_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (394 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_394 :
    recurrence5Scalar1Exceptional.coeff 394 =
      (((((196849940859899234481 * 10 ^ 70 +
        5396784857078528379037819372671357105954178604582930804097319565890591) * 10 ^ 70 +
        6192540081841395974253971149074904720247702572201108782556784388760621) * 10 ^ 70 +
        7065951034279327664576157119873437297324553169320287521409474997586743) * 10 ^ 70 +
        0304293510373092569432819774393369397664765811771435813330617308497791) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 395 = 310 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 5 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_394_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (395 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_395 :
    recurrence5Scalar1Exceptional.coeff 395 =
      -(((((54312775460465151058 * 10 ^ 70 +
        8253453342632217094286554943010561263557005344229677511753864027498431) * 10 ^ 70 +
        3408216727437034930543334560453588501256540315701187855316774137393011) * 10 ^ 70 +
        2851580784204089596690515073645154758378883983214212394692188117731065) * 10 ^ 70 +
        1257598952689704480629310989476647722515115552169656650525494522456091) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 396 = 311 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 4 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_395_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (396 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_396 :
    recurrence5Scalar1Exceptional.coeff 396 =
      (((((12935324724062564639 * 10 ^ 70 +
        6710476439110080449369438408938999249371621801360803712636650916188851) * 10 ^ 70 +
        9450770647037552352564493457208087920268377719270159663794190712076322) * 10 ^ 70 +
        1116883179739226496327638892787230903348493387112140762746300611021544) * 10 ^ 70 +
        9230700564529706605200794496830457768193770708053026154122151755079470) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 397 = 312 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 3 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_396_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (397 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_397 :
    recurrence5Scalar1Exceptional.coeff 397 =
      -(((((2751586325529559556 * 10 ^ 70 +
        2817033397017171955218751321467246762306321621937006851479445649722371) * 10 ^ 70 +
        8133948478810136586015028026013683746398048244544895476358915806254801) * 10 ^ 70 +
        6459245491094514282527460922998925794419387469247404034566060002787317) * 10 ^ 70 +
        5656925496218895804715062425138145845758584028885994871174882376069053) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 398 = 313 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 2 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (398 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_398 :
    recurrence5Scalar1Exceptional.coeff 398 =
      (((((529381407114707807 * 10 ^ 70 +
        5181768141457726008680597976719299592640984133214211160614774425697873) * 10 ^ 70 +
        8216124190886005933195289538705570442938499900622411471288832121686102) * 10 ^ 70 +
        3644533546068901489790803126665061704632110728359146692317389328911722) * 10 ^ 70 +
        0784510669491816562413926400353860985803801104053587597151327030805474) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 399 = 314 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 1 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (399 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_399 :
    recurrence5Scalar1Exceptional.coeff 399 =
      -(((((92201989006430635 * 10 ^ 70 +
        2586378278591919367270016653449473224507401776713070471172046775943810) * 10 ^ 70 +
        8078143397203883019610346198872747498126914762145403828700032468115489) * 10 ^ 70 +
        4110890143965801737476506681049248653363280851617824786000847953682751) * 10 ^ 70 +
        2837483875368192242767608093792473703071415675857338470210222103587782) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 400 = 315 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (400 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_400 :
    recurrence5Scalar1Exceptional.coeff 400 =
      (((((14392106027209485 * 10 ^ 70 +
        2669685346972245927934180006814249619258064244450951670013443038043154) * 10 ^ 70 +
        1025883835544297751943292261778473021709534116980722786390553415414051) * 10 ^ 70 +
        7681086722190444629853237963843643163497961244376637452911224951552352) * 10 ^ 70 +
        7760372987966565525440616051512207184488431414858328266345780917791383) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 401 = 316 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 31 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (401 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_401 :
    recurrence5Scalar1Exceptional.coeff 401 =
      -(((((1956232004480918 * 10 ^ 70 +
        9090502724728832819723067383032473736794767734696590900016641957928221) * 10 ^ 70 +
        6047369417942110541347901359196385234408961311753017560135873826836449) * 10 ^ 70 +
        5351842577256571331362155593549490415448312469104947302184440834116550) * 10 ^ 70 +
        6067459001477081979760943611701761021907841811470319760625067965537001) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 402 = 317 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 30 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (402 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_402 :
    recurrence5Scalar1Exceptional.coeff 402 =
      (((((213584433886873 * 10 ^ 70 +
        0793926612334188486476854086283659553788889309262426867162000169361837) * 10 ^ 70 +
        6867049831340212301350973413936030462848175364317174853691084022940474) * 10 ^ 70 +
        5920346376744421835877198756781947991387407410613917072391517526409647) * 10 ^ 70 +
        4206752801967019050533451060377032642661388556704637785631893710783051) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 403 = 318 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 29 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (403 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_403 :
    recurrence5Scalar1Exceptional.coeff 403 =
      -(((((13022802360720 * 10 ^ 70 +
        3726592804540685913260377540801355266643093392610302842380510506649819) * 10 ^ 70 +
        6211303557226461654095758004639475304702454535871906618174053145135719) * 10 ^ 70 +
        6568071258674194057178209077994873257019996578382706097139406322444434) * 10 ^ 70 +
        2586549854464516458621151441539098782944615841879808955477903078545161) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 404 = 319 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 28 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (404 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_404 :
    recurrence5Scalar1Exceptional.coeff 404 =
      -(((((1675900249364 * 10 ^ 70 +
        7380941203543950349894243634322629730016883602441887294581515628569336) * 10 ^ 70 +
        0178829827671606380620284612026550658429773884176284491605450879159586) * 10 ^ 70 +
        7025807022546517242048446110968159967013263060716596152987881009021415) * 10 ^ 70 +
        6512875310242291833404917987526082732495371483512795166417990309048969) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 405 = 320 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 27 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (405 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_405 :
    recurrence5Scalar1Exceptional.coeff 405 =
      (((((843412169237 * 10 ^ 70 +
        6098717662776625248727637061652186981610318403703084793436240075562295) * 10 ^ 70 +
        6254685989380021403290224995329461245311772929439120436185953615433878) * 10 ^ 70 +
        6715320987782134356757164333224994063517466467246941341692580451731822) * 10 ^ 70 +
        0982371492646644824780254664164993869473328204591052427425101036735669) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 406 = 321 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 26 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (406 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_406 :
    recurrence5Scalar1Exceptional.coeff 406 =
      -(((((210118042494 * 10 ^ 70 +
        4361353518412167260933283652967517870199869378408630133845377878420299) * 10 ^ 70 +
        7085317849532369071962470325775093935142593449354862427879726800898082) * 10 ^ 70 +
        6982672128234832449118122960952048882273224423063291327451326784305927) * 10 ^ 70 +
        8269988486373199879298583078927921978562079150981537720590382726409365) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 407 = 322 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 25 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (407 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_407 :
    recurrence5Scalar1Exceptional.coeff 407 =
      (((((41528403746 * 10 ^ 70 +
        0595652948646438313907506046966354553881203989316901537641356138416541) * 10 ^ 70 +
        2696623575206595063455038088126680788421718473322930401522507917053716) * 10 ^ 70 +
        2053558109323571932136108892855423777161265893376067481124761050555454) * 10 ^ 70 +
        3666398420931876102648248191324630272350463362789935081199677201561029) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 408 = 323 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 24 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (408 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_408 :
    recurrence5Scalar1Exceptional.coeff 408 =
      -(((((7160322139 * 10 ^ 70 +
        9606060750208495547981106580307361733373738559590867621605237466200276) * 10 ^ 70 +
        4876204009228373012440732785607435310940530872192223351903556429810412) * 10 ^ 70 +
        1616594099442911989566583090411066202113459212370573736852672422803566) * 10 ^ 70 +
        9920029367278957465623610464890236736078058587331980545057875643069661) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 409 = 324 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 23 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (409 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_409 :
    recurrence5Scalar1Exceptional.coeff 409 =
      (((((1115780790 * 10 ^ 70 +
        7312234551655592750934794751505288731796961344854432295875185727593381) * 10 ^ 70 +
        1765501807636993537044481490984056212690719360930241060593366351807604) * 10 ^ 70 +
        1830612756220414044687919062855064891109173395670779221403592799092000) * 10 ^ 70 +
        8233327372193213266942303489155516127010613659748037898957664927302477) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 410 = 325 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 22 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (410 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_410 :
    recurrence5Scalar1Exceptional.coeff 410 =
      -(((((159730183 * 10 ^ 70 +
        6734403242366916262355860043321939880579073012094815654082755895265203) * 10 ^ 70 +
        1578654925031935076714115442182638080295247579948651205711277555005503) * 10 ^ 70 +
        2479016162185379744492331328521115480484866863432111858120414062743011) * 10 ^ 70 +
        3149858304333041246349337945751559855713166754308616664132645962129072) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 411 = 326 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 21 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (411 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_411 :
    recurrence5Scalar1Exceptional.coeff 411 =
      (((((21178575 * 10 ^ 70 +
        0619656954462669613367157650209908883848180295119176479689023280320127) * 10 ^ 70 +
        2066354191047756068745136336737409245531943036179514288681342175527596) * 10 ^ 70 +
        2106439942984139673950219805171440574272678905818814450868899471145481) * 10 ^ 70 +
        8116693291592125005829627797652975044438279132200586752596232936580569) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 412 = 327 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 20 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (412 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_412 :
    recurrence5Scalar1Exceptional.coeff 412 =
      -(((((2610890 * 10 ^ 70 +
        9075213916834241759759427829665884229841078933515230201111985028755862) * 10 ^ 70 +
        5675824007277612626115890826771217269341049767072380060859398475584093) * 10 ^ 70 +
        4277431922434390619811023306873379424609814442111066465162149596400668) * 10 ^ 70 +
        0205500257092936076973704716326893268573799684951829053518589409470285) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 413 = 328 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 19 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (413 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_413 :
    recurrence5Scalar1Exceptional.coeff 413 =
      (((((299664 * 10 ^ 70 +
        4863860173842658593981883907452577657361117930398557924392404849071535) * 10 ^ 70 +
        0895348784983101683264217766653136460331764297811823165436021101379225) * 10 ^ 70 +
        3677390021123984963739032254806258017477879803921472755710960961700075) * 10 ^ 70 +
        1447081721855352854685753680333162763046505138767468704980579660942909) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 414 = 329 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 18 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (414 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_414 :
    recurrence5Scalar1Exceptional.coeff 414 =
      -(((((32009 * 10 ^ 70 +
        5735034463910792703862345755373669648002980375507168070708528408062325) * 10 ^ 70 +
        1978936261776089433837400140065257211437962361188911360694432180933418) * 10 ^ 70 +
        4693177281539952134900405013036470233673210969979206263383277711394550) * 10 ^ 70 +
        8541089403310430792648592153637587977877414938726494982015632247514778) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 415 = 330 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 17 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (415 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_415 :
    recurrence5Scalar1Exceptional.coeff 415 =
      (((((3177 * 10 ^ 70 +
        2273564942621213390461414511930758184500424023489739803812761584324903) * 10 ^ 70 +
        6530610339132098051254576447340083579406853253946984378880349404389005) * 10 ^ 70 +
        3013573793209297951166859769855070614465232441763477763183832129824847) * 10 ^ 70 +
        3999523878186311917719338382142996984798082995981751145261258019735318) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 416 = 331 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 16 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (416 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_416 :
    recurrence5Scalar1Exceptional.coeff 416 =
      -(((((292 * 10 ^ 70 +
        3289373958751518024067923037699088740220319719171324011726050837793753) * 10 ^ 70 +
        6722596270164492906225419915089401391538429145782826625216855819022602) * 10 ^ 70 +
        8831147149785628740323653708999862130793880068255811346057544505197257) * 10 ^ 70 +
        6868101273411172887718948670320994903822943146747103783238195864855662) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 417 = 332 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 15 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (417 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_417 :
    recurrence5Scalar1Exceptional.coeff 417 =
      (((((24 * 10 ^ 70 +
        8518102622551082118087327740885929956043163996119211093454847464491153) * 10 ^ 70 +
        5976023699622781649355786258002790044510052044958309144016975090042256) * 10 ^ 70 +
        2739006517648229058645403710739202730549767026869315785341785006276123) * 10 ^ 70 +
        9755082188700075133491459332992603168295905080013134740632761038436246) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 418 = 333 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 14 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (418 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_418 :
    recurrence5Scalar1Exceptional.coeff 418 =
      -(((((1 * 10 ^ 70 +
        9445774123002058657232068122577932172696124769954601540198005802580376) * 10 ^ 70 +
        8460987723431310971254452192886709034410589773325211416842714862618735) * 10 ^ 70 +
        5136949692011743895737673562833421611893529641477384101759911174995673) * 10 ^ 70 +
        5488508544910325295442557728108851820134153747650797265283661568331915) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 419 = 334 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 13 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (419 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_419 :
    recurrence5Scalar1Exceptional.coeff 419 =
      ((((1394146035000477358413744045320420110712737872210986167339967225110179 * 10 ^ 70 +
        3510580045912399034216660299388824943559421004159228635329546024531269) * 10 ^ 70 +
        2283919425179846881075359261236196292571774654157720896813309635607679) * 10 ^ 70 +
        6148956367712141436171239579044316081404849334481535978705459759614478) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 420 = 335 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 12 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (420 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_420 :
    recurrence5Scalar1Exceptional.coeff 420 =
      -((((91104328510488706909566949779068242199830251311255926314863390846618 * 10 ^ 70 +
        9673736489159625478151491119902410449349876962150522346711866849909566) * 10 ^ 70 +
        9341554184565404318212648971981143133583916869137828593852717179841466) * 10 ^ 70 +
        8629820178087305064370907162106343375438017407086571990648157592396538) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 421 = 336 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 11 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (421 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_421 :
    recurrence5Scalar1Exceptional.coeff 421 =
      ((((5393878758625423059838039545063725154394096549195733326322394123102 * 10 ^ 70 +
        2535543960397246009467380161644676075589076840973367205852449779172129) * 10 ^ 70 +
        8583813768629795948602215574560565606727603667537327835904287593932265) * 10 ^ 70 +
        7252667404195029315387274840525195642517014723036525364364468732180582) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 422 = 337 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 10 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (422 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_422 :
    recurrence5Scalar1Exceptional.coeff 422 =
      -((((287312955677864788267426852092231151433155817410071916557699244958 * 10 ^ 70 +
        0522701351597631145815593027176542712913252961920917080863122195107645) * 10 ^ 70 +
        2619656761333614770152052694645589831011271657161934477398690529382973) * 10 ^ 70 +
        2097493196470242979408544737785242642306249045807708102219806278212432) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 423 = 338 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 9 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (423 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_423 :
    recurrence5Scalar1Exceptional.coeff 423 =
      ((((13656003650530221801954498469269370754434274790092179423257478450 * 10 ^ 70 +
        3830042547309504473019485101591992320726744730467703475789874260318493) * 10 ^ 70 +
        8188314361522008889755360921865773240930316669526602038045749570554955) * 10 ^ 70 +
        8554671923916897297823030138966821481355125242920914709401906603274053) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 424 = 339 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 8 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (424 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_424 :
    recurrence5Scalar1Exceptional.coeff 424 =
      -((((573479362738585737256572374165514465066045985720254701105929106 * 10 ^ 70 +
        0709594384284156564117413575515349327140489873340766897778407182685471) * 10 ^ 70 +
        3038193922739130581699627495767758109985364010719638158767764027429608) * 10 ^ 70 +
        2840317266256025053469796072235868224093429799405575186639825667028183) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 425 = 340 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 7 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (425 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_425 :
    recurrence5Scalar1Exceptional.coeff 425 =
      ((((21021747723805733264679558528061405500435179440953647241015726 * 10 ^ 70 +
        5729142252898181367823257439109245990939686549049956780262291422653128) * 10 ^ 70 +
        1392048521773113164656956307643111334461422290245308364637965724375691) * 10 ^ 70 +
        6622372735337957111227241131806552046345225304695938771280765180842726) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 426 = 341 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 6 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (426 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_426 :
    recurrence5Scalar1Exceptional.coeff 426 =
      -((((662347708251299237256503986327134044739873936575624537570109 * 10 ^ 70 +
        2481092259310237007851097769393329793470541530009037310248865254358490) * 10 ^ 70 +
        4431388633503676711076603624989320968667124373508299373678639281134050) * 10 ^ 70 +
        7513348658529511604922745094332349223608981619264944111640692082281071) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 427 = 342 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 5 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (427 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_427 :
    recurrence5Scalar1Exceptional.coeff 427 =
      ((((17574025693865214885648740446252893531562611901444933378137 * 10 ^ 70 +
        1821190106238326177672350195358948779206633691870243873747551877170865) * 10 ^ 70 +
        4702667185237705182863191364510569454162417063188894826094208194339105) * 10 ^ 70 +
        1999861744054816744283418450688232249482079343951238104907721085591663) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 428 = 343 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 4 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (428 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_428 :
    recurrence5Scalar1Exceptional.coeff 428 =
      -((((381371683474668249390112901780661450771939657109608665082 * 10 ^ 70 +
        1286031567438219405245284442796213208244957069766007715460180522325928) * 10 ^ 70 +
        7114337695752009477530193520697483505515306541919835801884731868613283) * 10 ^ 70 +
        8155853816393335835643951233857674994665713605783906745510525769938331) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 429 = 344 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 3 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (429 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_429 :
    recurrence5Scalar1Exceptional.coeff 429 =
      ((((6461719135853121415428134815734229875206493542629299134 * 10 ^ 70 +
        6964450176470379052745529314477795209695124782198416277961067845295988) * 10 ^ 70 +
        5227279864990158994169510603449223216997804363310703867112095021676359) * 10 ^ 70 +
        5046406377588641413640562454495861717590267418287273601674692842001136) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 430 = 345 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 2 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (430 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_430 :
    recurrence5Scalar1Exceptional.coeff 430 =
      -((((78112535311321023048838783488733539007312641134326990 * 10 ^ 70 +
        9939781179112801687067218862472541021590256886591664468247413057883147) * 10 ^ 70 +
        8853359755894543304051620414992377700048354225224654506594839036372303) * 10 ^ 70 +
        0505037770012689324443867717998645685557074956003748860308784589448650) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 431 = 346 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 1 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (431 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_431 :
    recurrence5Scalar1Exceptional.coeff 431 =
      ((((513449794554358213495947506460003667769235500414784 * 10 ^ 70 +
        6806987547625869006481238235041293150549360864846917516112269628005187) * 10 ^ 70 +
        7759893861263098160465168607296350663529220614740151317887261661062334) * 10 ^ 70 +
        8422439862037260697877102685018978985187284102061534127160721316838316) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 347 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (432 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_432 :
    recurrence5Scalar1Exceptional.coeff 432 =
      ((((1542117076717721994392715392394049504223227419466 * 10 ^ 70 +
        4818036585744465450262567184671609696003191233229337893421080391338181) * 10 ^ 70 +
        5810737889529726821593062460841041132032625175623013498660973773205448) * 10 ^ 70 +
        2980043480400424493174730081916888672459785125631158718934531463982433) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 348 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 31 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (433 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_433 :
    recurrence5Scalar1Exceptional.coeff 433 =
      -((((67265594469457044146613077453358690876452893900 * 10 ^ 70 +
        9465211750509646901641255089771113454723717337153796982253126607584079) * 10 ^ 70 +
        4316277360840255885127339224714218706989662767026791989938222895925751) * 10 ^ 70 +
        4582509301672197165247534277521936855929721283769897845743609905298217) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 349 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 30 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (434 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_434 :
    recurrence5Scalar1Exceptional.coeff 434 =
      ((((483668688545305238095768682146713851591224748 * 10 ^ 70 +
        6829413569220642128028289416547446748190805761633774966145218542102060) * 10 ^ 70 +
        1524474498929428419447737040566773748396265760815077462793676632209625) * 10 ^ 70 +
        4434036750459086006423477393218136605672913973536793860156306604421905) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 350 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 29 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (435 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_435 :
    recurrence5Scalar1Exceptional.coeff 435 =
      ((((1006102269967904529349652574459520224861226 * 10 ^ 70 +
        8795287446098781183756278063841186554242420826264704401287917389253605) * 10 ^ 70 +
        9152218080153865322388009119578093625039296631202970365588744537799384) * 10 ^ 70 +
        5922788712237074429917404706724328666080384271079796124195420667906998) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 351 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 28 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (436 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_436 :
    recurrence5Scalar1Exceptional.coeff 436 =
      -((((29972517692632766310539953621733934257597 * 10 ^ 70 +
        4381715457082271403009637418712108832796731542872010260957315544106293) * 10 ^ 70 +
        9812811944678125148328613541230505414897389928899819778638052013750826) * 10 ^ 70 +
        2607065500886655315765507675591020791937308755499617857676989361354154) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 352 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 27 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (437 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_437 :
    recurrence5Scalar1Exceptional.coeff 437 =
      ((((75761327042558431030553372990366806164 * 10 ^ 70 +
        7291993018219603854681797329300730523673117837707623533317095212685827) * 10 ^ 70 +
        9436760290558403580135418409475681276103887136452837108709525094131288) * 10 ^ 70 +
        7839267603482363922308916004995861406735983807002987071493832293825826) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 353 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 26 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (438 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_438 :
    recurrence5Scalar1Exceptional.coeff 438 =
      ((((690163300314249535888304674683480256 * 10 ^ 70 +
        8767609439837398253386822566164864368986957288051124548267594047014472) * 10 ^ 70 +
        6870101016079679470858209776649557588993807943306609411261995021228828) * 10 ^ 70 +
        4307350192433084552728133794787409603759692833571406513333005131465253) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 354 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 25 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (439 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_439 :
    recurrence5Scalar1Exceptional.coeff 439 =
      -((((3415546807382299664345730895756789 * 10 ^ 70 +
        9642503008581464690869416170696490748465481538975545561864609939376054) * 10 ^ 70 +
        7901006563335040638298927950510754412310522094052853359768063171450426) * 10 ^ 70 +
        7027513043072679691051464256342760862533176342931930645338413483379403) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 355 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 24 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (440 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_440 :
    recurrence5Scalar1Exceptional.coeff 440 =
      -((((5269576941943806669906997184918 * 10 ^ 70 +
        2271464907627377440620676224606650959735019517662361435477255525602804) * 10 ^ 70 +
        5137482594603408079175128365090367038223506985348427655658443404830679) * 10 ^ 70 +
        3791615506792111743775033239585856934710539046212688718240433322633428) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 356 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 23 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (441 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_441 :
    recurrence5Scalar1Exceptional.coeff 441 =
      ((((56412040484094917347316893840 * 10 ^ 70 +
        3851173870955892775470020864514336362300068932900365268660350198742686) * 10 ^ 70 +
        5259957531861035352253556014317074301321090996411042983730523447413393) * 10 ^ 70 +
        5959362657713408603372649217607922989289833781518002550594532143196326) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 357 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 22 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (442 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_442 :
    recurrence5Scalar1Exceptional.coeff 442 =
      -((((46415486788323260119780171 * 10 ^ 70 +
        3338414625958856022391742737594712607869769478815503887376892450093170) * 10 ^ 70 +
        9315948911451800214590948904935632676905531759110311129810352930772084) * 10 ^ 70 +
        7974022101303398149160236751641329480238010270284184916644261642466176) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 358 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 21 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (443 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_443 :
    recurrence5Scalar1Exceptional.coeff 443 =
      -((((375893133250859656838449 * 10 ^ 70 +
        2362562155997276685365364239891074780668884478556873591267564425640959) * 10 ^ 70 +
        9929928910288964044812343175460446208524415005642159620642948697929755) * 10 ^ 70 +
        9441951006763392785097441384869455958877345034721317444907317533579499) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 359 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 20 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (444 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_444 :
    recurrence5Scalar1Exceptional.coeff 444 =
      ((((973320091893049921767 * 10 ^ 70 +
        6273461853537445866277977118207367883661859765293939859057666492664151) * 10 ^ 70 +
        2436774044524663469715947728284367976134927277201842894863276671222107) * 10 ^ 70 +
        9963426054540668804390570350759878098063251274369203702068554395205004) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 360 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 19 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (445 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_445 :
    recurrence5Scalar1Exceptional.coeff 445 =
      ((((30455234186614615 * 10 ^ 70 +
        5714610268046135081243776058712656595162902379867500656856719998948001) * 10 ^ 70 +
        5825906110332186109176552304147362851014187798992436747358380824812429) * 10 ^ 70 +
        7672257032021936549504819774060070591284354683757247618780983448222319) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 361 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 18 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (446 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_446 :
    recurrence5Scalar1Exceptional.coeff 446 =
      -((((3688927933954559 * 10 ^ 70 +
        8382749918916126906587414405913195750145637645215440737835662731800238) * 10 ^ 70 +
        7421892550466926403687561842337510423194762379102045602822271826416937) * 10 ^ 70 +
        5421357485596575779613224570045577472100319651772073450642021141194070) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 362 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 17 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (447 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_447 :
    recurrence5Scalar1Exceptional.coeff 447 =
      ((((7157007646071 * 10 ^ 70 +
        8515025381682354008781897008712597576860131412178903637719883880198766) * 10 ^ 70 +
        4232576763656495825556400446089313191074048957227683785517769327671899) * 10 ^ 70 +
        4977042728809228410282425094491275050562737953549442734884618828318964) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 363 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 16 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 364,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (448 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_448 :
    recurrence5Scalar1Exceptional.coeff 448 =
      -((((6869641634 * 10 ^ 70 +
        6213602842968150527622465391479676796766826521348593043207777965427484) * 10 ^ 70 +
        1605332030306401887763937809860007472938103321270975514489265164533312) * 10 ^ 70 +
        8472795683122218863039294520052824412463327292193556587014753509867100) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 364 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 15 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 365,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (449 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_449 :
    recurrence5Scalar1Exceptional.coeff 449 =
      ((((3797666 * 10 ^ 70 +
        5053500151114181418545228874664541491995920912409834479153778389205830) * 10 ^ 70 +
        8553917310694906225068718419389199093223118266715347138673462689057814) * 10 ^ 70 +
        7994714535288317311080882240201366909985137519736206302484548677818687) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 365 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 14 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 366,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (450 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_450 :
    recurrence5Scalar1Exceptional.coeff 450 =
      -((((1235 * 10 ^ 70 +
        4323331985082886808029966715083131397690303478517512413094322588047865) * 10 ^ 70 +
        8065403829135094456922885855686884262379348402245535560816414935801119) * 10 ^ 70 +
        4452712770393319286567548605536560677896363170369908776780296380438224) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 366 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 13 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 367,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (451 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_451 :
    recurrence5Scalar1Exceptional.coeff 451 =
      (((2326118111785645068845755902445001283107155643979459540105159356024970 * 10 ^ 70 +
        6698297656299022141124024958954075976660822358125378979588599210145679) * 10 ^ 70 +
        6358600453424417012337709156996287628468372914449114398654282633455878) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 367 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 12 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 368,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (452 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_452 :
    recurrence5Scalar1Exceptional.coeff 452 =
      -(((249102391093272238847760416100462104642301485219373428023625220193 * 10 ^ 70 +
        1092139440795179895206858428808622693034038713823685779425276696140600) * 10 ^ 70 +
        3070846207857293789257687764125270924087692205465190008641125761635307) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 368 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 11 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 369,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (453 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_453 :
    recurrence5Scalar1Exceptional.coeff 453 =
      (((14838455848322358303239350432451239119630720157596484878356923 * 10 ^ 70 +
        2145004389864372349894635003841735222363125640549269372382897214436772) * 10 ^ 70 +
        5963013361839259453531280651276020530696004697059269957771357820516259) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 369 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 10 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 370,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (454 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_454 :
    recurrence5Scalar1Exceptional.coeff 454 =
      -(((483163844745023678880654088800515148104202526743498921496 * 10 ^ 70 +
        7480525982609224318043034440737238096465724845248031780237853332163412) * 10 ^ 70 +
        0250745920513330156097169738734661796370883302607524824383743105423373) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 370 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 9 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 371,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (455 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_455 :
    recurrence5Scalar1Exceptional.coeff 455 =
      (((8151018237763230148543508907983466348112742351720900 * 10 ^ 70 +
        8795440897910715287698876015229656469400204394094911929867668557313903) * 10 ^ 70 +
        4149511647036755290319942996224235160196280072325970011266145375422614) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 371 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 8 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 372,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (456 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_456 :
    recurrence5Scalar1Exceptional.coeff 456 =
      -(((63469863298521120654509302189020973229972233656 * 10 ^ 70 +
        7874310804001721872250857905777497300945327793538645426420902303388541) * 10 ^ 70 +
        8033050336414805922205521472335165203145134651027169341673725376216807) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 372 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 7 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 373,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (457 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_457 :
    recurrence5Scalar1Exceptional.coeff 457 =
      (((214512949338245299963502072741649601089226 * 10 ^ 70 +
        4635034263979135758415395600227832782920826050556672371035879506568317) * 10 ^ 70 +
        8248510020931792920943113633763472354410980054955004694944914206052352) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 373 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 6 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 374,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (458 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_458 :
    recurrence5Scalar1Exceptional.coeff 458 =
      -(((262439545093872638023980864575585633 * 10 ^ 70 +
        9689119238123673801869147082662381199068850690977845944576659776091061) * 10 ^ 70 +
        7121040025975994489879665065598051430971648610301199737237404555891672) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 374 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 5 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 375,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (459 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_459 :
    recurrence5Scalar1Exceptional.coeff 459 =
      (((134403311056012957935002703413 * 10 ^ 70 +
        3657895081284565498011329655019004460891388183399370547992851609153438) * 10 ^ 70 +
        0042662627317749720154097261433120442421533766623042659766462489519034) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 375 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 4 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 376,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (460 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_460 :
    recurrence5Scalar1Exceptional.coeff 460 =
      -(((26789945140665264304951 * 10 ^ 70 +
        5243994588142984379543003216011369295440994163145662426868610599592672) * 10 ^ 70 +
        0319035881236036310778198425563608714891945549942653056511315735895769) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 376 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 3 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 377,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (461 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_461 :
    recurrence5Scalar1Exceptional.coeff 461 =
      (((1206594858751736 * 10 ^ 70 +
        2947647089218822857402165253613240975249236535542383011859191532866338) * 10 ^ 70 +
        1922041351761218095272417446944724391679493508139315456635891434422060) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 377 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 2 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 378,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (462 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_462 :
    recurrence5Scalar1Exceptional.coeff 462 =
      -(((15574111 * 10 ^ 70 +
        9722266126802536741383677787954208286338905633087667473952093831708316) * 10 ^ 70 +
        2921568205678358405098446864079426408781113703694420237088677512308100) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 378 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 1 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
