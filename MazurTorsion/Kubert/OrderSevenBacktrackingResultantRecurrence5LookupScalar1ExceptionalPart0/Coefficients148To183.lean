/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart0Simp
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

private theorem recurrence5Scalar1Exceptional_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_148 :
    recurrence5Scalar1Exceptional.coeff 148 =
      (((((73120497141343503528729328383094504498271625412504651 * 10 ^ 70 +
        5530714805808321121010263689042470333986777441455317337773061974446650) * 10 ^ 70 +
        8176030446743644411204928632101755487111251043480681209265703328364510) * 10 ^ 70 +
        4682873522127976078469045140824388518897856678442917698948133253880554) * 10 ^ 70 +
        5878919606049278081692569633930182921547091381617148680781264997764034) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 64 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_148_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_149 :
    recurrence5Scalar1Exceptional.coeff 149 =
      -(((((507344527528632155426875745198264840511383958916765228 * 10 ^ 70 +
        5006094300261134017712418154579532380141611675284453855704169111757135) * 10 ^ 70 +
        2613946662934472037348609188470639077215120084533286139194493278633806) * 10 ^ 70 +
        8081036666093362880808558558718848248964157018471010743392929316569304) * 10 ^ 70 +
        2963833313860485204918275129692735906429560856042652447868310273609317) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 65 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_149_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_150 :
    recurrence5Scalar1Exceptional.coeff 150 =
      (((((2672464846921579199243478626810111019289904824395606777 * 10 ^ 70 +
        4326761391041632265849247378819402842397374728553345267069383948699122) * 10 ^ 70 +
        4665507669697260715729682294510161575573888992367240259994646537312205) * 10 ^ 70 +
        3355328081294776224410300442965248258388021996228549682779906602426962) * 10 ^ 70 +
        7994650719395694243577542119331370136239326276081530364660534461803634) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 66 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_150_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_151 :
    recurrence5Scalar1Exceptional.coeff 151 =
      -(((((11885347058193463765832162598056849832589169186535675253 * 10 ^ 70 +
        7456366098067984820083934295154448692517539966437308868021218860275935) * 10 ^ 70 +
        0363358127088881326830781102851396275229052989256201926391565562328086) * 10 ^ 70 +
        6421448624694335872307499439341521793246507709751859924822367115596780) * 10 ^ 70 +
        5308555586702277959600350425458431727004425043709199018491836133246992) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 67 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_151_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_152 :
    recurrence5Scalar1Exceptional.coeff 152 =
      (((((45711985406921201236572555505841889902885586378489886246 * 10 ^ 70 +
        7153562730326488328248591967838614862958792657549232517014060137695681) * 10 ^ 70 +
        8288193951145936570260082764308892615661915886992562516057014087050729) * 10 ^ 70 +
        2183505096627970862352953005126391622322073762836041729346458741835065) * 10 ^ 70 +
        2207156468880419360041895364012892182566482350105214600119350382456864) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 68 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_152_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_153 :
    recurrence5Scalar1Exceptional.coeff 153 =
      -(((((149161957867802388440795606429073938342399060694353490649 * 10 ^ 70 +
        1685835459835334451008140150765528359685573025248767864217889684278049) * 10 ^ 70 +
        8911070217515016533600018627288720009488991217140957912902510294602395) * 10 ^ 70 +
        2022354277698785991596017790047217050121083192958943829175835925615727) * 10 ^ 70 +
        5588026151883640785197593396112545698557397236897510400678527675587553) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 69 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_153_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_154 :
    recurrence5Scalar1Exceptional.coeff 154 =
      (((((373714003651970669272367413895451054027148262429310212965 * 10 ^ 70 +
        2003477988081774216171901985195148454841965352355103177780992873335613) * 10 ^ 70 +
        8233224929489165901277398274117895441143313964944626570249214718824789) * 10 ^ 70 +
        3762085090073260337278811510588438864217288132701530548262615686771138) * 10 ^ 70 +
        6521543990797567684703267089077153500200635724950703235705270686253245) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 70 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_154_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_155 :
    recurrence5Scalar1Exceptional.coeff 155 =
      -(((((370212288945477724096536165777926049687313380389528421113 * 10 ^ 70 +
        8665108625868319160878342967423720451101628545728750371482642540697295) * 10 ^ 70 +
        1270998170776395920114135694440428799144653849975871997921515506979355) * 10 ^ 70 +
        0138404941495369966507546613188804468910280028077966460141067501267160) * 10 ^ 70 +
        5396590514768351083743504517535803516663788027036086044853431369952640) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 71 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_155_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_156 :
    recurrence5Scalar1Exceptional.coeff 156 =
      -(((((3367774556381355677559577969757821315613399036643192748950 * 10 ^ 70 +
        5125608795108253277565821748221188531583386424696227632764351537236638) * 10 ^ 70 +
        0060951199676557791408486871038166062544257567746959807089537537559270) * 10 ^ 70 +
        4637942922089196273927242066265785183918628427157220395071877284823249) * 10 ^ 70 +
        2839252862585581189704344764143524172576037245826342742420287521093862) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 72 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_156_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_157 :
    recurrence5Scalar1Exceptional.coeff 157 =
      (((((31959998239370571973751142180011059984820368083979533389627 * 10 ^ 70 +
        5975860588328727724284393414382251701115836667211090217318705182688973) * 10 ^ 70 +
        4171911667482113290277275145438871735347045241896201854781439338198994) * 10 ^ 70 +
        4365347563122390166987850467825532337445440547384364314985052036355615) * 10 ^ 70 +
        2420956911054059550354025060865922547267240188751620571779210530091302) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 73 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_157_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_158 :
    recurrence5Scalar1Exceptional.coeff 158 =
      -(((((190489716596932693912215714836549957367401917259877666678244 * 10 ^ 70 +
        8108552638395172214971680819795149436133060644756432688220434252085274) * 10 ^ 70 +
        7218647639989719358145705388817113307375702039178131644303507405828031) * 10 ^ 70 +
        1858585710716581556593479315533849055723167581388858861235005962861761) * 10 ^ 70 +
        8210717223644144075979690817158841979176922673891280661784296200308056) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 74 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_158_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_159 :
    recurrence5Scalar1Exceptional.coeff 159 =
      (((((946567401161800367154762582412133133279621673608402887070477 * 10 ^ 70 +
        9503314574227638911968809511740449764432960860646346328481016426106459) * 10 ^ 70 +
        8965180764478236131443267587350146632043677332246442552658998681419444) * 10 ^ 70 +
        0607846031843919151486651014425835990312326336025415291510456292570409) * 10 ^ 70 +
        9088118865998239607122075121403574671261816400333470111354383711516813) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 75 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_159_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_160 :
    recurrence5Scalar1Exceptional.coeff 160 =
      -(((((4223232409159418673797094793917249843743310842977559913900517 * 10 ^ 70 +
        2635326121171235375339659717627809270468748928768318939508356086727728) * 10 ^ 70 +
        4294642623559687913904578185972758804480176467875742223802183205232222) * 10 ^ 70 +
        7755797475626781674871975454287088024559524777100599015256594964364972) * 10 ^ 70 +
        3841641228954499545390699264617042147965711334804049486602476788886030) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 76 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_160_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_161 :
    recurrence5Scalar1Exceptional.coeff 161 =
      (((((17455003766257720415318513258984552719792705680661598201207048 * 10 ^ 70 +
        1346386560316223943019736150763896343401391488224911905909133696905689) * 10 ^ 70 +
        9838819978112037947969971794964907931912916660561094434660979000086442) * 10 ^ 70 +
        4933383652394327267576308411380912444063910753801414669436857941836229) * 10 ^ 70 +
        1696324071647671187279415984869853160680452635224231619953917195879767) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 77 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_161_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_162 :
    recurrence5Scalar1Exceptional.coeff 162 =
      -(((((67937477369580076673101835256674731253755611251999800547237713 * 10 ^ 70 +
        1570696319605954439564000646535938362743210590006412402028123793263679) * 10 ^ 70 +
        9456140317147821131960172152273226032251691156061610185808578748350798) * 10 ^ 70 +
        5205375382105400399972710961031662407304024652459808830444802050596215) * 10 ^ 70 +
        6866811093579820707661396955769360949712758648070651284402006602325320) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 78 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_162_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_163 :
    recurrence5Scalar1Exceptional.coeff 163 =
      (((((251475765135721779869722472526939597307683331700472137303672915 * 10 ^ 70 +
        7810002191642661827160478440695237422283241742741598164606199407670974) * 10 ^ 70 +
        4434945994097610315200093863510694142091999653164192708472188774829227) * 10 ^ 70 +
        7610984530164730113769350504050277107295527125114577738646250958665485) * 10 ^ 70 +
        1790139210200791392708015102682539630803245014302238533645743075784743) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 79 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_163_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_164 :
    recurrence5Scalar1Exceptional.coeff 164 =
      -(((((891029703927312665144185529970060019858890769199692702473432291 * 10 ^ 70 +
        5010787901884475008419527716607496336507339479499066878844520073917842) * 10 ^ 70 +
        5461938384089440221517376776325614531164831637668587900888401182277502) * 10 ^ 70 +
        2758279282945174656136051085590259259610165637369065664271935186331574) * 10 ^ 70 +
        3777026412542461395358768233226026217086733642198190351304407724426481) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 80 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_164_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_165 :
    recurrence5Scalar1Exceptional.coeff 165 =
      (((((3035755352348885111445231149527783531419803330901388685043365691 * 10 ^ 70 +
        9833134551320859537158655075346801407558056997610339573726129962315942) * 10 ^ 70 +
        6067370804136844311610160180792547776612518448829337781247976514985706) * 10 ^ 70 +
        0207792376182894582381224310735243775614887047023672154208517270412623) * 10 ^ 70 +
        7728973811848199538652042650803437122545733334912469094092617251346720) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 81 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_165_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_166 :
    recurrence5Scalar1Exceptional.coeff 166 =
      -(((((9978547471045936163364077527751305807676571378853848370487997038 * 10 ^ 70 +
        0474018159361219651809516825866927794216875279919505577672210354395974) * 10 ^ 70 +
        9538640636236247494646056131997923995624264753688275359468581974274890) * 10 ^ 70 +
        3125602186959889154490973159320183495675261998814009874456323282158460) * 10 ^ 70 +
        0187662048796793856267059479632852705591162586648525009803548929831966) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 82 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_166_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_167 :
    recurrence5Scalar1Exceptional.coeff 167 =
      (((((31724772326062056621900053719835193701489947784530160868049277778 * 10 ^ 70 +
        5010393407720049552711441860237850396086444475318927069150394445513476) * 10 ^ 70 +
        2724102627606072564433852152768648743055572001203109280560011969978410) * 10 ^ 70 +
        4798403653496998471363605326657222318149894453058422520009223285115277) * 10 ^ 70 +
        7314484330630192154116663151010803109016944473612574772193158750191317) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 83 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_167_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_168 :
    recurrence5Scalar1Exceptional.coeff 168 =
      -(((((97752744378769880280174591115630759624614964712778450510635168230 * 10 ^ 70 +
        8027886937357073304551209255637211503597117277665901286497357265656830) * 10 ^ 70 +
        9844959780845921327086163361526441011186574038880482409672667331023087) * 10 ^ 70 +
        6847657999398798303898230617233772258826511206255331018686366513428339) * 10 ^ 70 +
        9932388262664688060195283562800999792417347755551600527710139885293255) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 84 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_168_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_169 :
    recurrence5Scalar1Exceptional.coeff 169 =
      (((((292387242862147321602838791440187272328215288720040210352151177090 * 10 ^ 70 +
        5143547060411376910559913637168038359382523084744171894643250377440749) * 10 ^ 70 +
        9315742982355493675058945959663249763696583355235511312377936686558296) * 10 ^ 70 +
        4621923137572215112075989385230802308859162969221197874513928241851375) * 10 ^ 70 +
        2820156521241143431980515869928106808767464125091712554284952801761559) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 85 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_169_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_170 :
    recurrence5Scalar1Exceptional.coeff 170 =
      -(((((850084157748609814291284626280131641697304458980184386613694477311 * 10 ^ 70 +
        1173081668671421985985983533796384345430369154231345131443984815620797) * 10 ^ 70 +
        3147802162384198051324444307636221355818138015163662975901179569994285) * 10 ^ 70 +
        3656786188894672988752684239132545243930223228348742189241019107400226) * 10 ^ 70 +
        2457063746045785694804354217939996500489806960095584086732248765827387) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 86 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_170_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_171 :
    recurrence5Scalar1Exceptional.coeff 171 =
      (((((2405026438771586786322459653974849873194979024664112696176649103045 * 10 ^ 70 +
        1816037935907700554551610669048109584965406971176362901860768002046582) * 10 ^ 70 +
        0019831211836723780300309174106686970314049392362666708402266434237477) * 10 ^ 70 +
        8820124393740952810573942113217248769151061291829310210093824487990022) * 10 ^ 70 +
        4196195252297952674431089578979473147795298202939632586469437213681541) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 87 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_171_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_172 :
    recurrence5Scalar1Exceptional.coeff 172 =
      -(((((6627338152177715746793333376062474820802737212296663011874884315881 * 10 ^ 70 +
        8460927121875015650164967620028202393401788366733214043475684275550910) * 10 ^ 70 +
        0867081022448958938158619024212456801513205321722479657022434014103295) * 10 ^ 70 +
        4752439852483471596613784929013795606212205680297922358203164399061014) * 10 ^ 70 +
        9879681310245115509211465535968605907261422908517351391856749577179661) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 88 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_172_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_173 :
    recurrence5Scalar1Exceptional.coeff 173 =
      (((((17801986597955322595662379797863605563710328681405279417677146296261 * 10 ^ 70 +
        7341140447481818387298219404806074312246429016706838558743985237015518) * 10 ^ 70 +
        6002740137430906251200721694472349839597221706564206189629840718813782) * 10 ^ 70 +
        6686816562627575065874927230904609990627633243194217415045587951207454) * 10 ^ 70 +
        5500421265734333949213855302966445873220301100117245370455929237199085) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 89 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_173_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_174 :
    recurrence5Scalar1Exceptional.coeff 174 =
      -(((((46645493182039411774555315397230913628388373162616743701553298689492 * 10 ^ 70 +
        3468331154379239039379045904551992282031159859255128612495871324361125) * 10 ^ 70 +
        0080369879284109503899578008860221997298935958424173580924194316104184) * 10 ^ 70 +
        3536577528828631485531544265689605552439526788863986041285483889189401) * 10 ^ 70 +
        2258727957615894780819811776112159205203463527787137275834689811561881) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 90 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_174_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_175 :
    recurrence5Scalar1Exceptional.coeff 175 =
      (((((119296089943780062139684917303323820482589216370489740782766846440650 * 10 ^ 70 +
        8146955571262488955988938743799581486039279774221432770982954422879793) * 10 ^ 70 +
        0409588947883897453409486433306121090957156293070388524323712718559840) * 10 ^ 70 +
        2926505040431089133102408873653130330959939422338755057327731424812015) * 10 ^ 70 +
        3984328252176237624542971833054534934778862879882553010771156415385516) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 91 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_175_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_176 :
    recurrence5Scalar1Exceptional.coeff 176 =
      -(((((297954246191970249508661664009403865029465298812460466305412446125419 * 10 ^ 70 +
        4449571357957619185987181874518602441633727916117477494099721576184902) * 10 ^ 70 +
        0986567972390660761541640997377003130295485576258558996450208742070462) * 10 ^ 70 +
        6607840945076820555754134330597230905233413905958096115684442413210336) * 10 ^ 70 +
        9637804010024002061168521147963021530023498861031082009404441461275294) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 92 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_176_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_177 :
    recurrence5Scalar1Exceptional.coeff 177 =
      (((((727083944754561568782022119897428175251335987662720797367478598000656 * 10 ^ 70 +
        6845926228650335963626333652858190119676875718832357631882752771276374) * 10 ^ 70 +
        3885594236340955167185758720383367465132702975229155309762153289425796) * 10 ^ 70 +
        6645506624224962055800369395050042698055053692894663007623236765238763) * 10 ^ 70 +
        0820406096911525909184986381642296959182058342568559626200329156843366) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 93 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_177_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_178 :
    recurrence5Scalar1Exceptional.coeff 178 =
      -(((((1734255622348950184755197491230693406315128752018057941885553901854316 * 10 ^ 70 +
        4985667183303131171798125324806529666080830401685681434312265129885948) * 10 ^ 70 +
        0186016214387800664003442228696945779435497278539473845279923368878133) * 10 ^ 70 +
        3158177916136663271573362416529783976182900146856985121689964489577493) * 10 ^ 70 +
        8553351440255619743100905645180777860411265932640531811964494545413556) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 94 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_178_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_179 :
    recurrence5Scalar1Exceptional.coeff 179 =
      (((((4044805485272234556236673798635583637030127926377807924403428882639997 * 10 ^ 70 +
        4661865531041034254686045083304504074473780623957783212729538142014307) * 10 ^ 70 +
        0221142987919542871204779169860561106036933826780294494405566976670213) * 10 ^ 70 +
        0807822694833063523738035007196454466214254228710279813282467254719188) * 10 ^ 70 +
        9013463228294509538513849648783721667163713295124815728687200444108780) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 95 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_179_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_180 :
    recurrence5Scalar1Exceptional.coeff 180 =
      -(((((9227489081157192701628315811787861194243493255384896640337848481200968 * 10 ^ 70 +
        5485763760543104639737797228063932350315707240745745728761033648256513) * 10 ^ 70 +
        7240692591220754731160919551698652529329294702425042191071033496987176) * 10 ^ 70 +
        9098529570025528265627448784415844342440376126139083953682904097215518) * 10 ^ 70 +
        0409009498345447401064941609785225981410758850518831813042185906175907) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 96 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_180_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_181 :
    recurrence5Scalar1Exceptional.coeff 181 =
      ((((((2 * 10 ^ 70 +
        0596873707598737395394650936768891395521014531991471292561423639544724) * 10 ^ 70 +
        1208156956722214568443115079973867385474116356892777491119033857578077) * 10 ^ 70 +
        5542004576566186536068205290788190733933868097942900871292877791181933) * 10 ^ 70 +
        7780761269824625999969832162381757231090175530994825894985506284348538) * 10 ^ 70 +
        3809854997572179258683594999675629619235358634691026507986939519868713) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 97 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_181_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_182 :
    recurrence5Scalar1Exceptional.coeff 182 =
      -((((((4 * 10 ^ 70 +
        4995415408176041509369056361683851033527604032530986217296614659334313) * 10 ^ 70 +
        6521590938288046194074855712251738948643649056481725336052577704573175) * 10 ^ 70 +
        7976043550674875842004973983379979777056933549414485516477367420600461) * 10 ^ 70 +
        2075928831209580622137745810853678676139258211525712733236543575372801) * 10 ^ 70 +
        6721093270750026109426913083945264843537559843555316904835670452195298) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 98 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_182_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_183 :
    recurrence5Scalar1Exceptional.coeff 183 =
      ((((((9 * 10 ^ 70 +
        6225459599434800207346291486965029088596909136346975661250313202669438) * 10 ^ 70 +
        5224980505766828990532362407539865661662859541535832817414406650405811) * 10 ^ 70 +
        7293675610329536077737125497312037221606697980063854155356400333403288) * 10 ^ 70 +
        5948644366699160008845540860606183430137063901968343250451710699024981) * 10 ^ 70 +
        3384965588184238107006792003321785410977103673690242984818599339228957) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 99 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_183_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
