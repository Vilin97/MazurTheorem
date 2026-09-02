/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart1Simp
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

private theorem recurrence5Scalar1Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_289 :
    recurrence5Scalar1Exceptional.coeff 289 =
      (((((1126920359717776092364791829531483248474718526965067897516993229654 * 10 ^ 70 +
        8684478484624365037398148017428237455384110387328935815501369157361933) * 10 ^ 70 +
        9596426036535089309006058964485147932482643091074866566990528172530912) * 10 ^ 70 +
        4480160271884543329528727430294746508342398700844612833061562549845964) * 10 ^ 70 +
        3961639848524069796190938584689523677158119589591294162729982021745865) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 205 +
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
  rw [recurrence5Scalar1Exceptional_coeff_289_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_290 :
    recurrence5Scalar1Exceptional.coeff 290 =
      -(((((700309192372967424136672233668596061520603581378535395712778140688 * 10 ^ 70 +
        7832341333447232482448271909699579227739080229591843277271226223708087) * 10 ^ 70 +
        5284400362513471125290383369355902725445893270972301658142091343596365) * 10 ^ 70 +
        5446978716636706048735404174401226123219728929939586468398424690598361) * 10 ^ 70 +
        2575155494576906377897728705678368376299277254557526938235151729048378) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 206 +
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
  rw [recurrence5Scalar1Exceptional_coeff_290_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_291 :
    recurrence5Scalar1Exceptional.coeff 291 =
      (((((422707146352813457411582646968096183697211226477430331882083764254 * 10 ^ 70 +
        9337503952098291278463034261669348912304826526759564937128222927800012) * 10 ^ 70 +
        2514621042369659455541850040969991324892991584949653239100000551032585) * 10 ^ 70 +
        2331468147811496301997110272561835302699456361579837548016998502684576) * 10 ^ 70 +
        7752910578909472744544768365520437630627743445723237960947758731540888) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 207 +
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
  rw [recurrence5Scalar1Exceptional_coeff_291_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_292 :
    recurrence5Scalar1Exceptional.coeff 292 =
      -(((((249048945321933622904556455401838952274574021792027803641952813584 * 10 ^ 70 +
        3919074639826473508712642455837494137323624127147576778022018436774995) * 10 ^ 70 +
        4432461278563538121114712525681140840392733120941101742690548897025396) * 10 ^ 70 +
        5593354577023353626213104192216549118349793175869324310403292580631378) * 10 ^ 70 +
        6989723383842340470707088755665653067885681016226597425824901685761337) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 208 +
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
  rw [recurrence5Scalar1Exceptional_coeff_292_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_293 :
    recurrence5Scalar1Exceptional.coeff 293 =
      (((((143559295241178716370997752070255028645579608029687877579766515455 * 10 ^ 70 +
        4123373848104207071975371634984410716775591876670222323660530190956839) * 10 ^ 70 +
        4327184145513201354649590782452396100650721028930607159262132007631968) * 10 ^ 70 +
        8819589628282459528098580383244897049302565896941533718708334654212803) * 10 ^ 70 +
        9163510660564756118876124273526121541621921283438039440547269088102890) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 209 +
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
  rw [recurrence5Scalar1Exceptional_coeff_293_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_294 :
    recurrence5Scalar1Exceptional.coeff 294 =
      -(((((81014700941398686643115076613041978651450120580342159917332032180 * 10 ^ 70 +
        0370382678512783664551595261287690140700359718705244672839710980164035) * 10 ^ 70 +
        7762546155515291028567676570685775849992919032167966498488629176119500) * 10 ^ 70 +
        3146721806944048961182190205710584794168438812003452109083248083617652) * 10 ^ 70 +
        9043848889582829359687665604977135956090649868973871388125385474992732) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 210 +
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
  rw [recurrence5Scalar1Exceptional_coeff_294_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_295 :
    recurrence5Scalar1Exceptional.coeff 295 =
      (((((44737214888195433375844382558115462062682923888655022167414437531 * 10 ^ 70 +
        0935751859280249778838443829633444202315430105785229696226875018002561) * 10 ^ 70 +
        2618716182273658297763613110334852884867946697612419821994049685995974) * 10 ^ 70 +
        1451367218476107758355856440749551340318179549082223020766205095126112) * 10 ^ 70 +
        0804111138444916056897702076342592855373514077521728565032971727454546) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 211 +
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
  rw [recurrence5Scalar1Exceptional_coeff_295_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_296 :
    recurrence5Scalar1Exceptional.coeff 296 =
      -(((((24140551260659466405337096351251385689697611674696638167616187971 * 10 ^ 70 +
        1401085163227175466445142408849679077350301517704560643886784303812691) * 10 ^ 70 +
        0799002680067595931720609489538323560395937328456419995400178413676829) * 10 ^ 70 +
        2325681194511401533278140641829371904110064150221513137209589427535932) * 10 ^ 70 +
        9254179273361564490275066434076060081194012127072667435388937898450436) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 212 +
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
  rw [recurrence5Scalar1Exceptional_coeff_296_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_297 :
    recurrence5Scalar1Exceptional.coeff 297 =
      (((((12701029380673908567340318717811883335552741738803266146585792709 * 10 ^ 70 +
        6848670174466895841101786219066782354350306127706484983122767042514293) * 10 ^ 70 +
        6322087126892743335296869724536637655365059946829988344770975955904354) * 10 ^ 70 +
        3298909839348158388245384374131700414363095487613922420176821893695061) * 10 ^ 70 +
        4545420130486502578921451535925669249402978402047671848320560395201852) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 213 +
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
  rw [recurrence5Scalar1Exceptional_coeff_297_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_298 :
    recurrence5Scalar1Exceptional.coeff 298 =
      -(((((6494772724580509527742592353082935289915772905786959960219937961 * 10 ^ 70 +
        8608797602064270489052636137023950231252787459239300039381675084005294) * 10 ^ 70 +
        7781038551764243150128850985774774422262587541289631942171266838421099) * 10 ^ 70 +
        9067024890466019149203546685338580655635732625283100370640172463147339) * 10 ^ 70 +
        7598986458905817798780799306024987754938297986479729621983175440181276) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 214 +
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
  rw [recurrence5Scalar1Exceptional_coeff_298_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_299 :
    recurrence5Scalar1Exceptional.coeff 299 =
      (((((3213250764829968046303606268714000685622917332212059002935039025 * 10 ^ 70 +
        7257411597474384635868948691675217767750697218450111591553029749236118) * 10 ^ 70 +
        9738368156292703929615596255663682869539665886222457038736907902230865) * 10 ^ 70 +
        8256337168346305998384588870926225020671898611844664778584250760250163) * 10 ^ 70 +
        9241767588319661745614816469660641259873603203841019037954929873133280) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 215 +
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
  rw [recurrence5Scalar1Exceptional_coeff_299_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_300 :
    recurrence5Scalar1Exceptional.coeff 300 =
      -(((((1527658688003420857396102851302646980041534524140732852748088066 * 10 ^ 70 +
        7456067226664367248968407320298101519470427734906843760450035597844835) * 10 ^ 70 +
        7154133602038056762808501739860741979257701895911563205278602784430447) * 10 ^ 70 +
        4223438796688683235554895447694705321303637468065991743135968022061865) * 10 ^ 70 +
        1138381549009354223871372110868194939718936149937837050473593621753199) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 216 +
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
  rw [recurrence5Scalar1Exceptional_coeff_300_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_301 :
    recurrence5Scalar1Exceptional.coeff 301 =
      (((((690346564080703499814216122451484325990890555578340415086519979 * 10 ^ 70 +
        9471972765221721620494446042377108532024182861069311695846941722825528) * 10 ^ 70 +
        1555585622779707058423040089878698936593354629799288886961095387707166) * 10 ^ 70 +
        2054292450408563243275198492374003991463147301977902782835682919281226) * 10 ^ 70 +
        9303339334298708527779693940301218021832543554503778290107474945549712) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 217 +
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
  rw [recurrence5Scalar1Exceptional_coeff_301_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_302 :
    recurrence5Scalar1Exceptional.coeff 302 =
      -(((((290819452319497025838076509066354566015313999126408685221050628 * 10 ^ 70 +
        5112531292258470156009028610321922144746973905391207808138443454046253) * 10 ^ 70 +
        4892149571846710792181562964592315499141038451003161908773100533375094) * 10 ^ 70 +
        8200196507877484488819867656015115765710838878581223339882229990042445) * 10 ^ 70 +
        5790892151414085068480459836594089857900722213615561786543393938281586) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 218 +
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
  rw [recurrence5Scalar1Exceptional_coeff_302_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_303 :
    recurrence5Scalar1Exceptional.coeff 303 =
      (((((109672142904181138309257819685256655756962377484509594090786395 * 10 ^ 70 +
        6395176052588623273330154571244951004076604080146179863221763767551272) * 10 ^ 70 +
        6361954484347247885033984893482923637481066757577225642026146699806988) * 10 ^ 70 +
        3992341427747413441936691158602303676782572216256110475770695230253539) * 10 ^ 70 +
        5345658903576518752210917277357567523905401800620723674662094502010083) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 219 +
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
  rw [recurrence5Scalar1Exceptional_coeff_303_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_304 :
    recurrence5Scalar1Exceptional.coeff 304 =
      -(((((33113397774776162323384964863658748880335831316466196626355215 * 10 ^ 70 +
        2030245820197745037408267804193472334940003979815600664143044661570438) * 10 ^ 70 +
        7731948841090363990311577718554002089952746212325631462850963857478055) * 10 ^ 70 +
        3321408817935811388929074108168489821498497453768008659689291967650184) * 10 ^ 70 +
        8962513833021348295446192374472320426637694169306153050569189019880779) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 220 +
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
  rw [recurrence5Scalar1Exceptional_coeff_304_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_305 :
    recurrence5Scalar1Exceptional.coeff 305 =
      (((((4134647600920763657998087823270746013026158781131251033030323 * 10 ^ 70 +
        5211885157299677213954107800025786079790806686650601309867603524112830) * 10 ^ 70 +
        7372007289550291051137652388601305693454841164326168292665199685129666) * 10 ^ 70 +
        8168392890217541563617503016130114199551669461686245024123047423883623) * 10 ^ 70 +
        6973806495136521976788535896330107316019086699391966063193335561203039) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 221 +
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
  rw [recurrence5Scalar1Exceptional_coeff_305_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_306 :
    recurrence5Scalar1Exceptional.coeff 306 =
      (((((4671002347151380607114671083781042100036079228390287179990141 * 10 ^ 70 +
        9202065832472447395923740236353358338417086060525732807764012114499807) * 10 ^ 70 +
        5647398076141802624426274310845307394666113020924801559107709698694797) * 10 ^ 70 +
        1700301185950951919436992392596129747193412426880062590919775365100334) * 10 ^ 70 +
        7038830585227667618938497558154649178676469914840334026370951222694104) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 222 +
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
  rw [recurrence5Scalar1Exceptional_coeff_306_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_307 :
    recurrence5Scalar1Exceptional.coeff 307 =
      -(((((5813728130110272618222105728943630989872726793015110987663092 * 10 ^ 70 +
        1579621654521322291115104786674013133393136498858877513522180996194387) * 10 ^ 70 +
        8374398058926257655142400581557089721897387385489663160174410629384484) * 10 ^ 70 +
        2262797158667108006742941193467096653464609957753476728565443710694580) * 10 ^ 70 +
        6615725550427358301724608944295625508160650951551570917606866351687580) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 223 +
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
  rw [recurrence5Scalar1Exceptional_coeff_307_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_308 :
    recurrence5Scalar1Exceptional.coeff 308 =
      (((((4614304016100351155646169826445587172779229360677608044563906 * 10 ^ 70 +
        7316503006402655925793535342247106727468778623022994576608850837193821) * 10 ^ 70 +
        3211495373044170213436699483543432238780573455691939124735689448654862) * 10 ^ 70 +
        2097324796465829756999802138319455968572947913112266444685021617293094) * 10 ^ 70 +
        8294217612681322853237723162259892220281511769090284511042589525345852) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 224 +
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
  rw [recurrence5Scalar1Exceptional_coeff_308_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_309 :
    recurrence5Scalar1Exceptional.coeff 309 =
      -(((((3100683764175250952654110830580852981718419003445726520567389 * 10 ^ 70 +
        1014756951098591845617728313687176945683480425943347274251327928988998) * 10 ^ 70 +
        7135368946934172743139455704299352145547958457592108186397223051094321) * 10 ^ 70 +
        7066906143528747670294237786786453951119475519712148173655915319975186) * 10 ^ 70 +
        5520875679646292069861754336020785706918394841508575328504944827636465) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 225 +
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
  rw [recurrence5Scalar1Exceptional_coeff_309_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_310 :
    recurrence5Scalar1Exceptional.coeff 310 =
      (((((1896002549101735379835126613184426389938564871269551131163401 * 10 ^ 70 +
        6452937209023383590679481440801245467549180558483521831929592162971259) * 10 ^ 70 +
        1581944443225961064415511243271762803646085179075431947822698204640702) * 10 ^ 70 +
        9168016695323793865925000078635943015393097198940055881895110064013839) * 10 ^ 70 +
        6127711425110286108451148433747655515804115868047437686555287307775544) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 226 +
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
  rw [recurrence5Scalar1Exceptional_coeff_310_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_311 :
    recurrence5Scalar1Exceptional.coeff 311 =
      -(((((1086253637747435428092287765832583154912074506207486458159428 * 10 ^ 70 +
        8738754363248345660637910009216002035256572950610888500502854748757612) * 10 ^ 70 +
        7980916617328176377624000583664959409910163037161950468565309801212946) * 10 ^ 70 +
        1267120070751279701720559188110384733754387436586893065202713912727225) * 10 ^ 70 +
        4444473879957238848652286800638643357497436406012703473740348454982578) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 227 +
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
  rw [recurrence5Scalar1Exceptional_coeff_311_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_312 :
    recurrence5Scalar1Exceptional.coeff 312 =
      (((((591592078862754005774636869730402648189737602241727542022603 * 10 ^ 70 +
        2480684555672352392757487070987289789962571414503070424242799762416144) * 10 ^ 70 +
        8247460172782960513721843330588404728870155264127353308199750216027840) * 10 ^ 70 +
        5548687099684080796710968704563661244457038844568901733110826464437888) * 10 ^ 70 +
        8007290087827811187951509822475001517596153976171294970964572239128334) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 228 +
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
  rw [recurrence5Scalar1Exceptional_coeff_312_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_313 :
    recurrence5Scalar1Exceptional.coeff 313 =
      -(((((308734310422887587166239735704371038369313990622565140269504 * 10 ^ 70 +
        1120427714595969136705262202608106172420820933888822620287716438458754) * 10 ^ 70 +
        0231946716888885635136042418756191554988570985169952019674878082752406) * 10 ^ 70 +
        7562482797679991392922325709541253989876399852752305773646919831352342) * 10 ^ 70 +
        7325797459352441828825602491340694325600786863419390827448566526958970) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 229 +
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
  rw [recurrence5Scalar1Exceptional_coeff_313_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_314 :
    recurrence5Scalar1Exceptional.coeff 314 =
      (((((155109588914338751015361291217210627261121725835541085227408 * 10 ^ 70 +
        5969450583176196471892732959280059836462503435802714595250364046388881) * 10 ^ 70 +
        5124922530344770396606501288015294803676409746426052149964343127230583) * 10 ^ 70 +
        6586601272797775075821796152680510645248782348030372666026918859103777) * 10 ^ 70 +
        8512299441899321498810653141761551369269903375866119554722458665459702) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 230 +
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
  rw [recurrence5Scalar1Exceptional_coeff_314_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_315 :
    recurrence5Scalar1Exceptional.coeff 315 =
      -(((((75224456430485938957412291209310093188778988032263248083291 * 10 ^ 70 +
        7022991064830233405701581542818718181277742497084720659904193671546060) * 10 ^ 70 +
        6834608422447775168812335256178251489304811605220581039108711424162529) * 10 ^ 70 +
        3483309636688810351144890434525649029761296026832940424649850867781802) * 10 ^ 70 +
        3162182423418177375177557748160351368916134373083829546702481611172379) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 231 +
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
  rw [recurrence5Scalar1Exceptional_coeff_315_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_316 :
    recurrence5Scalar1Exceptional.coeff 316 =
      (((((35267701362564890166330323073760119169227118611558610769749 * 10 ^ 70 +
        3822792400449621848013063148671723138198260511291523228561175765351802) * 10 ^ 70 +
        4402486656264557369939472708996161391824092967335426722915439918123554) * 10 ^ 70 +
        0207406942721322696663991677851393037800185046749215148848437972079876) * 10 ^ 70 +
        8368188127475707522119804599722728104325405668808537787228498860876845) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 232 +
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
  rw [recurrence5Scalar1Exceptional_coeff_316_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_317 :
    recurrence5Scalar1Exceptional.coeff 317 =
      -(((((15993131249662743488641521959438521920580288705661011301158 * 10 ^ 70 +
        1716244486000171418084351733081113523429650806044909118625487631306952) * 10 ^ 70 +
        6570042249275407145980334006895948228998828725253970240975915104416637) * 10 ^ 70 +
        4571636536734256621103770925084091966336402634964243266205401533079964) * 10 ^ 70 +
        8106702835842227386085488216605836784271078350660931760052914484886250) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 233 +
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
  rw [recurrence5Scalar1Exceptional_coeff_317_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_318 :
    recurrence5Scalar1Exceptional.coeff 318 =
      (((((7013790966318288712463876735681971304931098541926183623548 * 10 ^ 70 +
        7677049879396178030856348132601614415463897077244417978499527426695060) * 10 ^ 70 +
        1158857347672944339843171032548403379777388292789994441966571716596914) * 10 ^ 70 +
        7161186112997905583954177680460161705492863179562399194290871015798888) * 10 ^ 70 +
        9550486145593604471419583035407546504867000415212675153205939588135677) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 234 +
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
  rw [recurrence5Scalar1Exceptional_coeff_318_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_319 :
    recurrence5Scalar1Exceptional.coeff 319 =
      -(((((2972123167155310182917980212662442403192674113224712824011 * 10 ^ 70 +
        6681925540004757555865206726908434457063462497021941476049483949395772) * 10 ^ 70 +
        8318939879639737641183119818110285429600816318060785310815392829724798) * 10 ^ 70 +
        7692019987367384320233774642862947369514521367422291375698430088302941) * 10 ^ 70 +
        2413927870265725000603307628995416258613677327970183381029602545294429) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 235 +
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
  rw [recurrence5Scalar1Exceptional_coeff_319_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_320 :
    recurrence5Scalar1Exceptional.coeff 320 =
      (((((1215047027753551584257597064479728000235608424355844315366 * 10 ^ 70 +
        1848215654257238522991243520960266835605604514522919251243644053773134) * 10 ^ 70 +
        3780906420273782787732917189200877611574559217785839304062841587162126) * 10 ^ 70 +
        8743186807356808355609731788612874723195023568037873675929883788630502) * 10 ^ 70 +
        7787938588465998377119817424191618405263636232704999682040932641763580) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 236 +
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
  rw [recurrence5Scalar1Exceptional_coeff_320_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_321 :
    recurrence5Scalar1Exceptional.coeff 321 =
      -(((((478039282776086856618740498993125595380931511756233849138 * 10 ^ 70 +
        5637059842954079145833172069281328476623728694141618127773784601443400) * 10 ^ 70 +
        5809548147360626780136648205991348859417024707118102631354046179937864) * 10 ^ 70 +
        8185342466405765308279844764886535904349564886756860991712108286805056) * 10 ^ 70 +
        0859416933651363700206483970492122788506535994695808029687593003221841) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 237 +
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
  rw [recurrence5Scalar1Exceptional_coeff_321_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_322 :
    recurrence5Scalar1Exceptional.coeff 322 =
      (((((180333602683926411622602327681303131179307260611981103476 * 10 ^ 70 +
        4165927478334100717001854570395666135674894688327838073618988153541134) * 10 ^ 70 +
        4952572159526558636913667027877043992921782024828113985327506815962413) * 10 ^ 70 +
        5017561889848859904376708259530697182341855669330329500642730044841206) * 10 ^ 70 +
        3813411691817927782819269562480796871483262593761036854425122025317335) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 238 +
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
  rw [recurrence5Scalar1Exceptional_coeff_322_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_323 :
    recurrence5Scalar1Exceptional.coeff 323 =
      -(((((64865099787098036885468831982206842004882760471774892329 * 10 ^ 70 +
        2344067815364828908897580512753268128341299978092932657733526383330833) * 10 ^ 70 +
        3313978899076186803850838635386369412274424379764882917298228818842460) * 10 ^ 70 +
        9215776413256651281728957815474588840145243601226904156697368115647089) * 10 ^ 70 +
        8482361915133668913866176953750623199244577529181944745301861819811441) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 239 +
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
  rw [recurrence5Scalar1Exceptional_coeff_323_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_324 :
    recurrence5Scalar1Exceptional.coeff 324 =
      (((((22052171747652819730084084327156419324728406674009530090 * 10 ^ 70 +
        0855347826189440143303222277969553218555243959049741823132764780245702) * 10 ^ 70 +
        7370667966585193078133254468470435804009735752394205584541233679236910) * 10 ^ 70 +
        3959164971770834002782618082678762001710082918635994163980169343374383) * 10 ^ 70 +
        8188893097391620836580527758357817571200437152373348226351392579413047) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 240 +
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
  rw [recurrence5Scalar1Exceptional_coeff_324_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
