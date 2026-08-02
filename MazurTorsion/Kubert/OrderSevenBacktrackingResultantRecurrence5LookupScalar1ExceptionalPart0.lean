/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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

theorem recurrence5Scalar1Exceptional_coeff_0 :
    recurrence5Scalar1Exceptional.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_1 :
    recurrence5Scalar1Exceptional.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_2 :
    recurrence5Scalar1Exceptional.coeff 2 =
      -((10894519662754506151967774734172362220584558254107437249534 * 10 ^ 70 +
        4772046049730844186273172193872310484161507650597956845500697779079168) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_3 :
    recurrence5Scalar1Exceptional.coeff 3 =
      ((10198913780440620770934351803995867465003443809336852969334366 * 10 ^ 70 +
        1304737692458152534916226369704539198160190692517885252317672486458368) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_4 :
    recurrence5Scalar1Exceptional.coeff 4 =
      ((162024111890492585271086119774228107383163939858126947727306241022 * 10 ^ 70 +
        5229975448203379172819247344917005120986841885850097631473603044739200) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_5 :
    recurrence5Scalar1Exceptional.coeff 5 =
      -((652494466932545007473537052105138792326445741383741926814268606115167 * 10 ^ 70 +
        7768973454101862987007283112291571735333116116886882173434399728489024) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_6 :
    recurrence5Scalar1Exceptional.coeff 6 =
      (((117 * 10 ^ 70 +
        5316073276814783507880275406569344352080577708837684071560773315674248) * 10 ^ 70 +
        4753524630262961001657920963557443526517318194090112339834229235102968) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_7 :
    recurrence5Scalar1Exceptional.coeff 7 =
      -(((118513 * 10 ^ 70 +
        2379229961078945556403891069670570030155261132631369536913577875457062) * 10 ^ 70 +
        3044295800847054550190016119087845478163093799135709575064606876330280) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_8 :
    recurrence5Scalar1Exceptional.coeff 8 =
      (((66766824 * 10 ^ 70 +
        2371699361904219633999243919949110464683247501015392081310450034653336) * 10 ^ 70 +
        3286453050087492190918867495033582390456661249919672279514034815612200) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_9 :
    recurrence5Scalar1Exceptional.coeff 9 =
      -(((16494570845 * 10 ^ 70 +
        8180210241861236128752551788324026387033697726444860588463323267688480) * 10 ^ 70 +
        4056591601179722657580307604373729873921111934210897094624006560038504) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_10 :
    recurrence5Scalar1Exceptional.coeff 10 =
      -(((2514376176787 * 10 ^ 70 +
        3735527785672164033609368874264920426684958751263428064566482014480501) * 10 ^ 70 +
        9203061411240477284607127532336805585247156147494256197159308805541136) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_11 :
    recurrence5Scalar1Exceptional.coeff 11 =
      (((4345089432211474 * 10 ^ 70 +
        4993926018881855416151295593566232665738794374974474883844628195622162) * 10 ^ 70 +
        1164625336434418460696518100517567845887924287592666735707110817749380) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_12 :
    recurrence5Scalar1Exceptional.coeff 12 =
      -(((3755964721648322398 * 10 ^ 70 +
        6468689462002463355027022049719211267113921469691224445518579689752923) * 10 ^ 70 +
        3815751315868907974664641664920800149156382081120464320928838621648188) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_13 :
    recurrence5Scalar1Exceptional.coeff 13 =
      (((2888568891570882497207 * 10 ^ 70 +
        7476225444541703925446680340601152797084240473888684956256435822337343) * 10 ^ 70 +
        7498346682781378578448471363960234496223667809086669741632116467167584) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_14 :
    recurrence5Scalar1Exceptional.coeff 14 =
      -(((1550198847765902025003165 * 10 ^ 70 +
        1317016759428783366025470782436378883088923250317544257546700432893403) * 10 ^ 70 +
        9950801451776800696354966900868330881852860576967855095575726351727028) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_15 :
    recurrence5Scalar1Exceptional.coeff 15 =
      (((518169089322160884278809626 * 10 ^ 70 +
        4110423519832765199181202047184910538273099312486298969274330554308653) * 10 ^ 70 +
        4088478401248504503180766356603486613373634974450588501574089489061312) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_16 :
    recurrence5Scalar1Exceptional.coeff 16 =
      -(((81929109562076777929898939958 * 10 ^ 70 +
        1550360315462593373932017863560963428196618340236531021943100849307339) * 10 ^ 70 +
        4594627548379796641066363429503621320243993037107259692754866222875698) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_17 :
    recurrence5Scalar1Exceptional.coeff 17 =
      -(((20173316549545489671544516903179 * 10 ^ 70 +
        1603434121896604184413056186602720568395940635902304922643057775852150) * 10 ^ 70 +
        8728924056159053987006637373442223517890433723230108407939801897223306) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_18 :
    recurrence5Scalar1Exceptional.coeff 18 =
      (((25711387740008204552892154807690531 * 10 ^ 70 +
        4131895006395837913009159519541450079332751722386222104412551876238851) * 10 ^ 70 +
        2317919566349434350393549649035306654477935809261967184388993642139210) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_19 :
    recurrence5Scalar1Exceptional.coeff 19 =
      -(((16497695465747676858972886739863771821 * 10 ^ 70 +
        8147915630128171480602814877890167297901652235834895691039379625677261) * 10 ^ 70 +
        0404735029903425929934001349838592261507765856394974452022389424045002) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_20 :
    recurrence5Scalar1Exceptional.coeff 20 =
      (((8038513165637626503757802613404564849637 * 10 ^ 70 +
        9987584218741491667724031703301523809696361519686877421598471764890569) * 10 ^ 70 +
        3266358431585858064254662216337929294186767326264837045217185510797838) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_21 :
    recurrence5Scalar1Exceptional.coeff 21 =
      -(((2837689181344277645855480909073241206944286 * 10 ^ 70 +
        2298483211973705229933293457079420208265459238177277312759513114901524) * 10 ^ 70 +
        5901023497128659240041458700679263129154666557398662702291601568490183) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_22 :
    recurrence5Scalar1Exceptional.coeff 22 =
      (((602017819780523096440710190261071322459374215 * 10 ^ 70 +
        8210243471380467589142075085564049060311848859753819074909281408152169) * 10 ^ 70 +
        2213613465881885891321389102364490415315539506174845913973635338870847) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_23 :
    recurrence5Scalar1Exceptional.coeff 23 =
      (((11946826472035223595764565629598145997549170790 * 10 ^ 70 +
        5552304383482691248228633274782171319909775834107720006398894614272325) * 10 ^ 70 +
        2793478192473809729256455468145120646004871106862162677688566159432802) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_24 :
    recurrence5Scalar1Exceptional.coeff 24 =
      -(((71885396042580577427065851653480143466543450279188 * 10 ^ 70 +
        8998745843390845499924714672838891680478010654035270464113598502228461) * 10 ^ 70 +
        7308804793340069688455619886057539536016616797278797784752953742645623) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_25 :
    recurrence5Scalar1Exceptional.coeff 25 =
      (((35380984947570002317349085612038878799080673643414618 * 10 ^ 70 +
        3650866480467185330289310877736072294423116675025648817330198589330214) * 10 ^ 70 +
        8002489151179182774319455918692044413109157404601268609741497147939485) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_26 :
    recurrence5Scalar1Exceptional.coeff 26 =
      -(((11273849908061492176078090336691747013817463589209481853 * 10 ^ 70 +
        0976171650217381617914815387371403316841981694657648405788066148057785) * 10 ^ 70 +
        6767822816942147115934464208607369811724643033193924020596508924758208) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_27 :
    recurrence5Scalar1Exceptional.coeff 27 =
      (((2729988578219384084836336413881375299636760970208688978198 * 10 ^ 70 +
        9943497572361651965495026294614135893408290284798726816421337889688305) * 10 ^ 70 +
        2570685899635655279149733186579328264691696021939621941397703386503706) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_28 :
    recurrence5Scalar1Exceptional.coeff 28 =
      -(((526869518189337795012066808961376577682901548152447215488912 * 10 ^ 70 +
        9499858516970184426856455474103782743240636530772523984796865223513716) * 10 ^ 70 +
        6614720336272108088045049411385224621282804497028116838608610014218396) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_29 :
    recurrence5Scalar1Exceptional.coeff 29 =
      (((81848942867239401391115119706334308289811840072079991790105384 * 10 ^ 70 +
        6895961213717715054697409220311190636488566251977521791370227929745633) * 10 ^ 70 +
        4428672708356406095980197252445188884036744149198400277350506051078348) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_30 :
    recurrence5Scalar1Exceptional.coeff 30 =
      -(((10012916951760002664423394212911200336335992985864339693963901523 * 10 ^ 70 +
        8108855580906379272149221595785566766725593547485756253457995475174634) * 10 ^ 70 +
        0017648441695488598234166129254490785656277100747796012012774107848357) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_31 :
    recurrence5Scalar1Exceptional.coeff 31 =
      (((878677852897942490012548054127223419077514955378700987661640435791 * 10 ^ 70 +
        1776190979992089577675564253468928694751765780893776313842217195844363) * 10 ^ 70 +
        4001825409839212281359284154536385391493148972905487653474546280840073) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_32 :
    recurrence5Scalar1Exceptional.coeff 32 =
      -(((31897893760569272838940805507973547531339364518636270541248032259408 * 10 ^ 70 +
        6804896570425920021301275401812479487248797388978491150525616977946933) * 10 ^ 70 +
        1261633732169688539310663303935332930785396166059634258453802132254186) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_33 :
    recurrence5Scalar1Exceptional.coeff 33 =
      -(((6172544094048521010455654873646980547831785084890728291348785497659804 * 10 ^ 70 +
        8291641837355809406866448355938196250839096986383638180325053238769857) * 10 ^ 70 +
        1343278908978456867387033291088613655682250953938635008142964464802459) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_34 :
    recurrence5Scalar1Exceptional.coeff 34 =
      ((((164 * 10 ^ 70 +
        1931065860204952550646567083322998607313640435704603986370356338650970) * 10 ^ 70 +
        4518513855181700788383232229219567988070286576229709578826548021329246) * 10 ^ 70 +
        9475206564918707628511029060948546038112198759794748120774585781236127) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_35 :
    recurrence5Scalar1Exceptional.coeff 35 =
      -((((23543 * 10 ^ 70 +
        0364714808116329457023133812117925789230766248216688478867505023767587) * 10 ^ 70 +
        0866491885012070086754133105189782738543234688814037228512028056331808) * 10 ^ 70 +
        0221720784320770616162224923121520208271662217969868308434246887796018) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_36 :
    recurrence5Scalar1Exceptional.coeff 36 =
      ((((2450806 * 10 ^ 70 +
        2575739331026541201109302920137312629490245160417052000756829210331753) * 10 ^ 70 +
        8988421905161955727119494461600179489254808776906730742760301626588259) * 10 ^ 70 +
        5489120690211460857997682413243730043854614943418417001380666742204474) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_37 :
    recurrence5Scalar1Exceptional.coeff 37 =
      -((((189141483 * 10 ^ 70 +
        6277928830913882309014331153392070150475045639439030587860644264486532) * 10 ^ 70 +
        0384943833170921884068150053937006857902495153135954140037135262696547) * 10 ^ 70 +
        3533117261622520507439210280234939325166891888835864507999122584514413) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_38 :
    recurrence5Scalar1Exceptional.coeff 38 =
      ((((9108683662 * 10 ^ 70 +
        0506434450672552443988422015949998182636937816011881774530008563568701) * 10 ^ 70 +
        8901560923252047862848572913744105606640616847540504995292462522170794) * 10 ^ 70 +
        7731013153249786368952226911480883292938148867464626385596850903803879) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_39 :
    recurrence5Scalar1Exceptional.coeff 39 =
      ((((122264952651 * 10 ^ 70 +
        3220143279547943004159695670353293415576163135881958661611142253998343) * 10 ^ 70 +
        9253632177895006975857588705454849375632340898027392143489952047397249) * 10 ^ 70 +
        0189509487564486251290661628084457507160427905293004081177050719018046) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_40 :
    recurrence5Scalar1Exceptional.coeff 40 =
      -((((89370713729305 * 10 ^ 70 +
        7684623404538774196548736542743912641156998569621064273709209360439626) * 10 ^ 70 +
        4471814364629016557882753540551262959719178038406132798574979822013765) * 10 ^ 70 +
        7908709628941252034409659222962435853168521480503625762477244510950923) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_41 :
    recurrence5Scalar1Exceptional.coeff 41 =
      ((((12627457669523575 * 10 ^ 70 +
        6890169424436404645621200915298639644529329418482915812137477476640553) * 10 ^ 70 +
        1990880991728078828253649467535440443073949000402245622039239133043780) * 10 ^ 70 +
        7667534042888474073812180553307999214965483665201982734810934581301573) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_42 :
    recurrence5Scalar1Exceptional.coeff 42 =
      -((((1266533530870250790 * 10 ^ 70 +
        4758604067740150156121367827350459448811919711812175946765147091975822) * 10 ^ 70 +
        5365717706555517427558745578980821834407021024506108812407475751040480) * 10 ^ 70 +
        7599684694033095641526510221334746357007541296766689638595311824463748) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_43 :
    recurrence5Scalar1Exceptional.coeff 43 =
      ((((104350864072617224713 * 10 ^ 70 +
        3975531475041354206156098954350898048236109245666655583193895676690371) * 10 ^ 70 +
        5891953140661146280786474175513389455231601111753116424182388403808373) * 10 ^ 70 +
        4157063480050694933499431245127435298014936154487692224571292352539141) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_44 :
    recurrence5Scalar1Exceptional.coeff 44 =
      -((((7428719402797795941942 * 10 ^ 70 +
        3499396605959968321068932261175892833103863415742877784077766632308888) * 10 ^ 70 +
        9946100838354975907615487293349943053660007690216528576567654771576896) * 10 ^ 70 +
        7990107213303654008731618743117255154120686307828720839589405902269478) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_45 :
    recurrence5Scalar1Exceptional.coeff 45 =
      ((((468145607876251498600698 * 10 ^ 70 +
        0968997237166432555688397777815322019550213523424492415963927024455058) * 10 ^ 70 +
        8521139878303165555171343654575745461886433493540260370122029907456126) * 10 ^ 70 +
        9101340608787002267717990070418372357581636323697103080771565188996667) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_46 :
    recurrence5Scalar1Exceptional.coeff 46 =
      -((((26475282844423789330241543 * 10 ^ 70 +
        7539878309606214044716867843103223668155098147184093235030141838784196) * 10 ^ 70 +
        0477776103079876238427527095327407525484713921732609809143953020469871) * 10 ^ 70 +
        6513599030523582698747027688156639656376234037365679427996289012631902) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_47 :
    recurrence5Scalar1Exceptional.coeff 47 =
      ((((1355143346697588439693431819 * 10 ^ 70 +
        7737976990951950136548059755804809512970762114434098313433032914212766) * 10 ^ 70 +
        1979750922310879847057673483097528035850393746816968793172052680894161) * 10 ^ 70 +
        9126621908769128867803220026796277073540154661598982300921564830115198) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_48 :
    recurrence5Scalar1Exceptional.coeff 48 =
      -((((63126582246030965601527094839 * 10 ^ 70 +
        7940926294800288397621424586963827946864038875316873959079462193179894) * 10 ^ 70 +
        6907274834267276417165612932838883324050936174282433227472733251088385) * 10 ^ 70 +
        5540052903278683622458368174576521689809715992368136699481438375327335) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_49 :
    recurrence5Scalar1Exceptional.coeff 49 =
      ((((2685749929254192887988419576022 * 10 ^ 70 +
        3269414163568420777297995128536469444400214901233446646851833348563331) * 10 ^ 70 +
        2450274481645794852160377534748545858804325868539779199537484307816091) * 10 ^ 70 +
        2550952646298562650569596794482753512558482975665464161596430361921666) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_50 :
    recurrence5Scalar1Exceptional.coeff 50 =
      -((((104578154822153463646294711954530 * 10 ^ 70 +
        8159374973325097364491966278785261104094588727949745496134332303810880) * 10 ^ 70 +
        0892549157845072829493294736395063951531770096043560543907830467814527) * 10 ^ 70 +
        6263809144686132485538619214716690791604092768901448536906859981516246) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_51 :
    recurrence5Scalar1Exceptional.coeff 51 =
      ((((3729569970356592748431717891910120 * 10 ^ 70 +
        6489320628831398626021970531406368743992652173487156477698021422387622) * 10 ^ 70 +
        3716449700977117623140398048006290244763050588792571811451579351786362) * 10 ^ 70 +
        7640687889227319768786832061893120160053499021601029996769688867324900) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_52 :
    recurrence5Scalar1Exceptional.coeff 52 =
      -((((121740119220318113708673889079466035 * 10 ^ 70 +
        7385209205401598819662287204428237352322469845615878396510622307998831) * 10 ^ 70 +
        9765123662287525212100361726053813336304442550203314184900634257115560) * 10 ^ 70 +
        0855313398201346060284378992928268360279331158632575396460636589593835) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_53 :
    recurrence5Scalar1Exceptional.coeff 53 =
      ((((3628510776944220289975023015404402543 * 10 ^ 70 +
        6950718097250451431872394191204661092170863794257064212830899382370450) * 10 ^ 70 +
        0898986833264966696116042101383945055004987301825662369125783103785860) * 10 ^ 70 +
        3900630078768730476269439676959927075053706747659452219845464856384815) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_54 :
    recurrence5Scalar1Exceptional.coeff 54 =
      -((((98269144873504334708927547105715907297 * 10 ^ 70 +
        6933163792319247328631039192066191776685522463984834813863091438009898) * 10 ^ 70 +
        8597029515299098722469733781885206127871034442911998509408939116144576) * 10 ^ 70 +
        5775046512418294948497384500644726745403495867754174234114058673326817) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_55 :
    recurrence5Scalar1Exceptional.coeff 55 =
      ((((2396409252292415356563166934944077465850 * 10 ^ 70 +
        7125029575305691303754916350039139998739258638967664351540751319376622) * 10 ^ 70 +
        1197948847025029898385725197598225569773407172241738873596420720248097) * 10 ^ 70 +
        8917595220959398244150971059709271373730992726403844951495776097109496) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_56 :
    recurrence5Scalar1Exceptional.coeff 56 =
      -((((51726782628379434669304924149264262918736 * 10 ^ 70 +
        9429012575510929059241283403901640057817899863588466674014954550227805) * 10 ^ 70 +
        1890422589988891104974976189745367295760967013645760408843479487825411) * 10 ^ 70 +
        4260189714025244208468316012773432207001912418250442683467821318013607) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_57 :
    recurrence5Scalar1Exceptional.coeff 57 =
      ((((953361913923807204559852118737389916345931 * 10 ^ 70 +
        6460182290167280871273053280431666658048742789482498248523694799780086) * 10 ^ 70 +
        2387326486024385458981450378545930070311341384553427890039596421732834) * 10 ^ 70 +
        6090258004260627647741226223273963552915781624752906459296726516797366) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_58 :
    recurrence5Scalar1Exceptional.coeff 58 =
      -((((13642172034956923104429173023555135841349755 * 10 ^ 70 +
        9164053778958512157006737512393420867988498623647530122277945436141041) * 10 ^ 70 +
        4839635278742515169285696712206258432011393893207108328099177244012362) * 10 ^ 70 +
        8029341199047198170789236041277556339684469262069677157771553544610300) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_59 :
    recurrence5Scalar1Exceptional.coeff 59 =
      ((((95177647179320824176706298336510361327323247 * 10 ^ 70 +
        5812284900759048595557049628323227219293139324882194670436413233830327) * 10 ^ 70 +
        9387532508346202665152822303844804149361479506064193509443790036809946) * 10 ^ 70 +
        6454512856727748154181620024641259844850564695641568101396383392698591) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_60 :
    recurrence5Scalar1Exceptional.coeff 60 =
      ((((2436919287616497360108869498818626867334437328 * 10 ^ 70 +
        4042796511715603647696244249229233976768342966250630486841438655264340) * 10 ^ 70 +
        7872093549063459173256820376890255620327210697040029717128927966050694) * 10 ^ 70 +
        2988487030703515494437132286569845428438196516353971524939985041096235) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_61 :
    recurrence5Scalar1Exceptional.coeff 61 =
      -((((132655784884349315378011770703094618654796414898 * 10 ^ 70 +
        0282928453793050405664966649359842089993775536595789283092600181486483) * 10 ^ 70 +
        7007891665708904009587862669227632135069810768030131715259490173481978) * 10 ^ 70 +
        6658287938466780848424244441841965048689021534284314520128137083844945) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_62 :
    recurrence5Scalar1Exceptional.coeff 62 =
      ((((3879670551452050306128808276712678112002753686517 * 10 ^ 70 +
        2307630021442423126973000434222793756702650120839772727349748234163760) * 10 ^ 70 +
        5968767742432121844677353661412943646461822312594322097877894015729689) * 10 ^ 70 +
        4566233538841903204826508204769029230220192339718723944885950279012230) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_63 :
    recurrence5Scalar1Exceptional.coeff 63 =
      -((((87459964361950641790797103701622289150235361956632 * 10 ^ 70 +
        9733383062579695496376282053386917117598905347612425766755333012087195) * 10 ^ 70 +
        4613045756346461509329899823992157716248847859997896058840288045650941) * 10 ^ 70 +
        1055298717249188339610087103147753419842500957107247866353559742930394) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_64 :
    recurrence5Scalar1Exceptional.coeff 64 =
      ((((1624320708114726815976543741335626420308250987469165 * 10 ^ 70 +
        6257208192887081257560733766588371978152056063131317480146865596837658) * 10 ^ 70 +
        5999656070158648703824176516978002195456195795203869746566410704533643) * 10 ^ 70 +
        2949584948377290198515527976008039622696765418075926106938088908133036) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_65 :
    recurrence5Scalar1Exceptional.coeff 65 =
      -((((24773089587797529258768393110475027163305612393726156 * 10 ^ 70 +
        4182938348589769126854115778366544894047444890506871248728753712511511) * 10 ^ 70 +
        2404039206879914259350505781499202999005960114459648067146198173606231) * 10 ^ 70 +
        1005800990478964345029516002604943510924835434169876870143091516995913) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_66 :
    recurrence5Scalar1Exceptional.coeff 66 =
      ((((286700849181475830348246233615021422844449943531218971 * 10 ^ 70 +
        2234282766294891012158763128367858779617977172434420819751938170713412) * 10 ^ 70 +
        7690711205143153991242561165669758730719166021517136851203439046222252) * 10 ^ 70 +
        9014313350426818725474332690388205725811138217016164059619108690839257) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_67 :
    recurrence5Scalar1Exceptional.coeff 67 =
      -((((1591876492347799294261870128760213108583749184277385354 * 10 ^ 70 +
        1814745701912100808020531015618892551855381550228903553622630216922293) * 10 ^ 70 +
        0716842898820011236045118998056540791373922112258362338588310746434268) * 10 ^ 70 +
        8084508471424176947526757516773203283193854352157275083005723760120681) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_68 :
    recurrence5Scalar1Exceptional.coeff 68 =
      -((((32700736823989292671628911927329542816298137187156281822 * 10 ^ 70 +
        0824340296406357620565176400023672491948916575368181940347179461126637) * 10 ^ 70 +
        9559828681585896160524140597384817584919601036805348467014218993976779) * 10 ^ 70 +
        9091391588752309700341491888413902125257397739644688696510008168571496) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_69 :
    recurrence5Scalar1Exceptional.coeff 69 =
      ((((1407613398297249233794312520592396518118234445229911486940 * 10 ^ 70 +
        3917052920367013334809404835679655421797200905869777792356894847255288) * 10 ^ 70 +
        7145512739149371132812200686715296714095713048761511564598174335918666) * 10 ^ 70 +
        2130199546501426360687713988344339291339384392599333964418277119074667) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_70 :
    recurrence5Scalar1Exceptional.coeff 70 =
      -((((32770567214861415127870976708981821691145751236398464851939 * 10 ^ 70 +
        6571143695654959567329515530079071274853873025317606689981232973193075) * 10 ^ 70 +
        6613029287461221584925672726110332543200835291017225894440869755406587) * 10 ^ 70 +
        8834246719423663872684232013301623991281880527762829491545032285313156) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_71 :
    recurrence5Scalar1Exceptional.coeff 71 =
      ((((595005966879994277414201258238337710830648872076143281524870 * 10 ^ 70 +
        1369862019987742169809815161028244214052748851085952538749127548413558) * 10 ^ 70 +
        0986503599688145046862778365071778272565197295460185680268937522961630) * 10 ^ 70 +
        7665182951190264482593832238719683471648799066831938797661838862103354) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_72 :
    recurrence5Scalar1Exceptional.coeff 72 =
      -((((9111871454999654793732638558602536148246109658415650541248184 * 10 ^ 70 +
        4913858002820397498232895966271503032609171991739604977584972281061320) * 10 ^ 70 +
        6467136969030960032184663306895368546050193269348407649898357211142851) * 10 ^ 70 +
        9808551687766091073310302653476703426217994836683484769216668679036265) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_73 :
    recurrence5Scalar1Exceptional.coeff 73 =
      ((((120395864107752178829493663986296976740319344980413079436271939 * 10 ^ 70 +
        8864489705454567321536900175051837140364433327221446529227022354557829) * 10 ^ 70 +
        8760078334644740738963732979724190088288174095276466900510162785055861) * 10 ^ 70 +
        0359991094871642069162931996881883011419442883462855856508767597030537) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_74 :
    recurrence5Scalar1Exceptional.coeff 74 =
      -((((1368807890722192713124317018962530682832924260499101381179352791 * 10 ^ 70 +
        4908414333698085601796815214425555995232136216954345543019052061624448) * 10 ^ 70 +
        8261031715394363612769738220501285316329469157724859248459055856096676) * 10 ^ 70 +
        3499658923106636375886021979218077433960167565711647878706463502428041) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_75 :
    recurrence5Scalar1Exceptional.coeff 75 =
      ((((12988430382333403469331436378028222572929919025587223587764223205 * 10 ^ 70 +
        6783481211122049037823984767933841884629748981019602932714460330237620) * 10 ^ 70 +
        4703317688098507580742662259654488851222517497970102798076097465593420) * 10 ^ 70 +
        1096700500200223498976643838767467009547875618506507689675994050226097) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_76 :
    recurrence5Scalar1Exceptional.coeff 76 =
      -((((93033855934839639938618695869396585065083653692824698099387892870 * 10 ^ 70 +
        4128007420695922829043831002346250423084295045528405254414842294864824) * 10 ^ 70 +
        2779527667049118538780553411791793475387318099200826947704210966200953) * 10 ^ 70 +
        4293687200173551664717423006294013163026647095600258137225005163148624) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_77 :
    recurrence5Scalar1Exceptional.coeff 77 =
      ((((286495173233444817893884600406184097989938463114397071468811062255 * 10 ^ 70 +
        4284241126507628747508632823752483885974107855330655865660022368040892) * 10 ^ 70 +
        2727237866782912260470940856476153341055600179814245806621817392030288) * 10 ^ 70 +
        3168607164528525481115621466695881138230824619144990328194669243693197) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_78 :
    recurrence5Scalar1Exceptional.coeff 78 =
      ((((5042742815698174498974596087699408816598513968262890339132401604605 * 10 ^ 70 +
        2626874099757417921553444523074725100199748522861412497605638451009245) * 10 ^ 70 +
        7784031623629964045821388868601125252874192778579047301928913473753644) * 10 ^ 70 +
        0595797974581885683916000811669314277890405450285508809294789014071055) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_79 :
    recurrence5Scalar1Exceptional.coeff 79 =
      -((((123326240875527218484854311363762663460414794734162475422027368430236 * 10 ^ 70 +
        7396879610722475293556587258838294904965831441823783815714138623643386) * 10 ^ 70 +
        9150846128195083320747972488058865652864642697553577559999866538924784) * 10 ^ 70 +
        2744495938381316349353327221084041284812106282715762493083780933745806) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_80 :
    recurrence5Scalar1Exceptional.coeff 80 =
      ((((1678816512432407676833413995363229594325824163396115990887914025708428 * 10 ^ 70 +
        7532429431027276230806921515959244627574338500808660004553336077183511) * 10 ^ 70 +
        8592196417946892410088722190775917895467569649798902839264258435644898) * 10 ^ 70 +
        7280155433542121235823990587409024524228169124314066201707089567475728) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_81 :
    recurrence5Scalar1Exceptional.coeff 81 =
      -(((((1 * 10 ^ 70 +
        6922695535470573150576803878301889797705085222176418850924433181558350) * 10 ^ 70 +
        9082749168681117002316584645718998428078176284392412730428743689795090) * 10 ^ 70 +
        3341533166404576089738735663121481133007867001319658854228366017683758) * 10 ^ 70 +
        3297128547012616400878456102865122098571710227806266852893065272509199) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_82 :
    recurrence5Scalar1Exceptional.coeff 82 =
      (((((12 * 10 ^ 70 +
        6405973664441033968533242787365113227394014324147252375737060832516092) * 10 ^ 70 +
        2878721086862123380619702871725868909723134446179160594773070844075493) * 10 ^ 70 +
        9820845201780734356002088364244312206270963362413483132278448877729481) * 10 ^ 70 +
        8154964054779450721428030042292507196035875863158383499568009085110760) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_83 :
    recurrence5Scalar1Exceptional.coeff 83 =
      -(((((53 * 10 ^ 70 +
        6110934701900878355548094033025372362080096039560223114966954668973732) * 10 ^ 70 +
        3506246564173129977085196875017081229693203406283485006407474317825825) * 10 ^ 70 +
        5922039873913385521463656925114104457317854445809207149020400019451230) * 10 ^ 70 +
        4780703414641513812741708473362967853858693631957263454391299591989449) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Exceptional_coeff_84 :
    recurrence5Scalar1Exceptional.coeff 84 =
      -(((((249 * 10 ^ 70 +
        7096699009128036354368223486575326625226163761934286976936865541400335) * 10 ^ 70 +
        7670918457830566620079956962588849317028866971858457456445053261099428) * 10 ^ 70 +
        9691111593772565693138984598817911902968519340945298615278111885382726) * 10 ^ 70 +
        9622314267299172639063019640499973841855466333989664213363790952943461) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 85 = 0 +
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
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (85 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_85 :
    recurrence5Scalar1Exceptional.coeff 85 =
      (((((8458 * 10 ^ 70 +
        6741081266654961401048323632681740060234110897390588031228717386389839) * 10 ^ 70 +
        0121143892840510675964160382273742140135812082137642881217244292631075) * 10 ^ 70 +
        5231446099038627944902434728216613588211863363574479412985029709719962) * 10 ^ 70 +
        6604835031728876097405312628391128214293299800368980899040737949689774) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 86 = 1 +
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
  rw [recurrence5Scalar1Exceptional_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (86 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_86 :
    recurrence5Scalar1Exceptional.coeff 86 =
      -(((((109332 * 10 ^ 70 +
        7302755125102849499176220526181899303670646704248587920752170257778446) * 10 ^ 70 +
        1865640763689585331590369568209014929651545298761728199931143861390770) * 10 ^ 70 +
        2962821445065095185482277982892536859574194794941937210458181166015512) * 10 ^ 70 +
        6908213230452842893920250248761258338101205930646866833151363997296637) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 87 = 2 +
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
  rw [recurrence5Scalar1Exceptional_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (87 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_87 :
    recurrence5Scalar1Exceptional.coeff 87 =
      (((((973286 * 10 ^ 70 +
        2511835452023303555653359269675757889131796520391437871402932826269566) * 10 ^ 70 +
        2140224398903429693515253821545462473978236124788590128387799538727192) * 10 ^ 70 +
        2853165376650027867100001734920902155231859358482870737340627963239846) * 10 ^ 70 +
        3224468263593498564241639426558500352382650202938772475460120410233479) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 88 = 3 +
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
  rw [recurrence5Scalar1Exceptional_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (88 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_88 :
    recurrence5Scalar1Exceptional.coeff 88 =
      -(((((5964603 * 10 ^ 70 +
        3923350988528435030256034863496550378531799434341694975571227186629840) * 10 ^ 70 +
        3719038678198772847258540097545204264412272942671506110026472103448093) * 10 ^ 70 +
        6129018055008642895374480926363253007475228647642740279369884598344599) * 10 ^ 70 +
        5926973027072459141999888893284484753126959724616231237492576836790416) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 89 = 4 +
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
  rw [recurrence5Scalar1Exceptional_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (89 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_89 :
    recurrence5Scalar1Exceptional.coeff 89 =
      (((((14109451 * 10 ^ 70 +
        2981999984193036973911131628450996819467020023928985992994134197152261) * 10 ^ 70 +
        4652774288835937508051053866365890290170307486541315404911352144051659) * 10 ^ 70 +
        1556052152157953313258226822249476119376295681149568378182505924820824) * 10 ^ 70 +
        5694440931730115848554690083681088846970996226041563012912896064819151) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 90 = 5 +
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
  rw [recurrence5Scalar1Exceptional_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (90 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_90 :
    recurrence5Scalar1Exceptional.coeff 90 =
      (((((226387168 * 10 ^ 70 +
        4557612000503431930310285303931637722121661141512921750198422783739286) * 10 ^ 70 +
        5434761709745553356925299393801221318321166008565492104378572485336383) * 10 ^ 70 +
        9580197180440932411894271478946939349453319899623572614774957629416427) * 10 ^ 70 +
        8664700929759834811293117333751797840432313747304687856070845135798650) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 91 = 6 +
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
  rw [recurrence5Scalar1Exceptional_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (91 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_91 :
    recurrence5Scalar1Exceptional.coeff 91 =
      -(((((4109652410 * 10 ^ 70 +
        9714157789385574494356873103613924907729689290188704592408255229397663) * 10 ^ 70 +
        6378295624259598077079618404140319576226936795920035959662362538034483) * 10 ^ 70 +
        6210240290667766039083975586874174322717824775463055886868942893013474) * 10 ^ 70 +
        7145505117265532863080135614016869865950746661233112555898433125476750) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 92 = 7 +
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
  rw [recurrence5Scalar1Exceptional_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (92 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_92 :
    recurrence5Scalar1Exceptional.coeff 92 =
      (((((40713204613 * 10 ^ 70 +
        8054031082145168995325073245672242878719228926117554978738473237303488) * 10 ^ 70 +
        4305776593337356165805330999075675259265599402955839623046367813277512) * 10 ^ 70 +
        7638812957799528196994588890921142662079980549337091837504449191716249) * 10 ^ 70 +
        4118491435999260158494831283768504945977833574476766811424633977272410) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 93 = 8 +
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
  rw [recurrence5Scalar1Exceptional_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (93 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_93 :
    recurrence5Scalar1Exceptional.coeff 93 =
      -(((((276949623163 * 10 ^ 70 +
        8228276995753063155083044238874070370410146065012758604376253671233366) * 10 ^ 70 +
        5577245193064919940822476770626304875383155959378775159860844614890690) * 10 ^ 70 +
        0480980054574944606292359804963032505720595732949376587938065479269325) * 10 ^ 70 +
        6123304851496563660489478883337047752801456959649583374987899687002357) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 94 = 9 +
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
  rw [recurrence5Scalar1Exceptional_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (94 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_94 :
    recurrence5Scalar1Exceptional.coeff 94 =
      (((((1071754145272 * 10 ^ 70 +
        6985150094018692393299081766800252105656272371381106475018268735840401) * 10 ^ 70 +
        2946003004304434476291357945829804138637645753765724706154679051602407) * 10 ^ 70 +
        8566822056876807124988006807439093322965458155746303496202057227748357) * 10 ^ 70 +
        0323295377299481263112844899774348932278108098510725287864135341808281) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 95 = 10 +
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
  rw [recurrence5Scalar1Exceptional_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (95 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_95 :
    recurrence5Scalar1Exceptional.coeff 95 =
      (((((3087363972821 * 10 ^ 70 +
        6290082649221992685129823910319950715250256566507996350631119729988888) * 10 ^ 70 +
        7739239657597311834748201234266860597898951460323932006216485426719861) * 10 ^ 70 +
        9274147647895431373562994535786246447796762564792886342151371076007670) * 10 ^ 70 +
        3011370695823736670620648999712446862421255655369123151392871320128004) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 96 = 11 +
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
  rw [recurrence5Scalar1Exceptional_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_96 :
    recurrence5Scalar1Exceptional.coeff 96 =
      -(((((102747967806281 * 10 ^ 70 +
        7162303153994085005510014008917102072841233864263852723879952358919450) * 10 ^ 70 +
        7880022029969355518294833308256254658211408483010127705694811447749363) * 10 ^ 70 +
        0228561620189296311521731590349584221382309912452651425071838249802391) * 10 ^ 70 +
        5956183394998156053995194556335801942774419762324346510441328194427381) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 97 = 12 +
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
  rw [recurrence5Scalar1Exceptional_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_97 :
    recurrence5Scalar1Exceptional.coeff 97 =
      (((((1105774593345501 * 10 ^ 70 +
        2611325167549942691471405870589223859965590890268133368604476702823476) * 10 ^ 70 +
        3986048180560811799040631279243241387034309484287682086196086088479721) * 10 ^ 70 +
        3271786262235452040165874398364332307950070251688970525879124271275978) * 10 ^ 70 +
        1351663208352625852496686241021717792044523449307954506521238033273072) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 98 = 13 +
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
  rw [recurrence5Scalar1Exceptional_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_98 :
    recurrence5Scalar1Exceptional.coeff 98 =
      -(((((7850380673104022 * 10 ^ 70 +
        1611781734708190504324165683986276842415795041115959992763763029424484) * 10 ^ 70 +
        3854887245008001227777793810442033951887148158962182603772630661996330) * 10 ^ 70 +
        0025013627727812867553964528265778901647441481003363666923985701796709) * 10 ^ 70 +
        4024488292116142363403666975283058976873428137368268049946795803032925) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 99 = 14 +
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
  rw [recurrence5Scalar1Exceptional_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_99 :
    recurrence5Scalar1Exceptional.coeff 99 =
      (((((34943391097874687 * 10 ^ 70 +
        8881835443300563031568508906528444708436988281628738443348442058247567) * 10 ^ 70 +
        7781451673680303725728942331835245578135556041971732456110042202023680) * 10 ^ 70 +
        0074217865641774504925822021713026463314125129977197309373514967458274) * 10 ^ 70 +
        9543229406030538932617652825029916614102470818885121040473387806299278) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 100 = 15 +
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
  rw [recurrence5Scalar1Exceptional_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_100 :
    recurrence5Scalar1Exceptional.coeff 100 =
      -(((((1675270252282687 * 10 ^ 70 +
        5689279696054932901033208827129000913789127054677362635435967473955027) * 10 ^ 70 +
        1656817322080374171467416526455609891541095197917302759106056070523629) * 10 ^ 70 +
        8695746513737243071491042054035709648137340689300253531983166816186037) * 10 ^ 70 +
        8361531663040156384005491431735523705470449879484145477354484943705822) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 101 = 16 +
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
  rw [recurrence5Scalar1Exceptional_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_101 :
    recurrence5Scalar1Exceptional.coeff 101 =
      -(((((1780755560767344350 * 10 ^ 70 +
        3675719837619351817858971998898777001337569092103885033412375281255132) * 10 ^ 70 +
        4247975687738813258163113981609632255486001144199459088943024733530380) * 10 ^ 70 +
        6692898708014362121554918174414178272996637834440108441492636600202620) * 10 ^ 70 +
        0002852471057866316800691285771274778136043971745428431069984766625295) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 102 = 17 +
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
  rw [recurrence5Scalar1Exceptional_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_102 :
    recurrence5Scalar1Exceptional.coeff 102 =
      (((((20767756480648525422 * 10 ^ 70 +
        8871809616449855039402547928929038448140093087855127601230873266757679) * 10 ^ 70 +
        7715315101314024934928879539999207072010910174719310916306270874097007) * 10 ^ 70 +
        6625785260297921962356638441057238245632292453605095477554318144594581) * 10 ^ 70 +
        6166884293647070563119115296421748847031996794312553949862009824504548) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 103 = 18 +
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
  rw [recurrence5Scalar1Exceptional_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_103 :
    recurrence5Scalar1Exceptional.coeff 103 =
      -(((((151030719449605047852 * 10 ^ 70 +
        6188484942030357625175269894023908398380645678787203420986875344984564) * 10 ^ 70 +
        8057855525891529420680722983894437802026002910934685758144646616159095) * 10 ^ 70 +
        7760254176776570456717099685851719594195128195863829172813488291776340) * 10 ^ 70 +
        5461475852905925635101182338135767002804888228837235944407656090877504) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 104 = 19 +
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
  rw [recurrence5Scalar1Exceptional_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_104 :
    recurrence5Scalar1Exceptional.coeff 104 =
      (((((720286034819177011780 * 10 ^ 70 +
        1563788726014345126932206891053321268931546241463388226980127962671165) * 10 ^ 70 +
        0549567122280016608929334797521728500675267100346114247732562390212082) * 10 ^ 70 +
        9481722423901429196577481669372092154012001628786478108691471767275164) * 10 ^ 70 +
        9529873908999145400780120025728364379994502398011920157664329866429640) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 105 = 20 +
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
  rw [recurrence5Scalar1Exceptional_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_105 :
    recurrence5Scalar1Exceptional.coeff 105 =
      -(((((1041665827222959649853 * 10 ^ 70 +
        0817323699610949924514261489533606773442990382449641101582222869635821) * 10 ^ 70 +
        1971579144412820390970523907485391906381596326851346605600612056998132) * 10 ^ 70 +
        9725733821076060180489275246542202033002492820830278827074398408239674) * 10 ^ 70 +
        2858039058105128395541069852706627494599656184994140738054341869703759) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 106 = 21 +
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
  rw [recurrence5Scalar1Exceptional_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_106 :
    recurrence5Scalar1Exceptional.coeff 106 =
      -(((((21072083493031114678477 * 10 ^ 70 +
        3085738915650387846483567375658721168352963714489055365427002162372244) * 10 ^ 70 +
        2635588003294260585722578122167516746879869196046269172626566252020025) * 10 ^ 70 +
        9716643479772337473914260020792069446011645106703051113913489432187737) * 10 ^ 70 +
        7021203714792257172222589297685488795966651733409527867162798032624641) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 107 = 22 +
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
  rw [recurrence5Scalar1Exceptional_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_107 :
    recurrence5Scalar1Exceptional.coeff 107 =
      (((((275664257371584778877742 * 10 ^ 70 +
        8082574692273968980403144905935008049433540444227615267881028420827203) * 10 ^ 70 +
        8634748894910759819984844472592205538369849288826080575537208642828912) * 10 ^ 70 +
        9087339131680461725504045280003067459415681622064403950583706229020906) * 10 ^ 70 +
        2511738340454421986367670960045384150745900389057115631793365123852560) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 108 = 23 +
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
  rw [recurrence5Scalar1Exceptional_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_108 :
    recurrence5Scalar1Exceptional.coeff 108 =
      -(((((2064169865066398360915621 * 10 ^ 70 +
        9478974075216908378837795968545700052633673315768764943062669731157797) * 10 ^ 70 +
        8028844273084661745264257098154698473092076269261530579262590934139552) * 10 ^ 70 +
        5549025594648614032517639375177595551237452334798739933030328506631204) * 10 ^ 70 +
        5920242615711156227645714455437518187978499569527517107301768132775615) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 109 = 24 +
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
  rw [recurrence5Scalar1Exceptional_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_109 :
    recurrence5Scalar1Exceptional.coeff 109 =
      (((((10421537672600118215204653 * 10 ^ 70 +
        0467846866782045192818007912526373944476739066278028325551580333947845) * 10 ^ 70 +
        7745542627082822771944293491374614148501711992514194127446274507787229) * 10 ^ 70 +
        7866261360161836495422003992927879306610465327758995020001287232350394) * 10 ^ 70 +
        9978778132787709026859692814721564052983912346196786664966848367045159) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 110 = 25 +
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
  rw [recurrence5Scalar1Exceptional_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_110 :
    recurrence5Scalar1Exceptional.coeff 110 =
      -(((((25239293514665926681132550 * 10 ^ 70 +
        6184572951211572853797436765553374797443503098801940583304620191400102) * 10 ^ 70 +
        4823511441702880213696138904550550067537474219568395914118692423935659) * 10 ^ 70 +
        3618621939886756459391046601660121429684346598731938089846858971497600) * 10 ^ 70 +
        8471673899870159259802815291173454485051903698945281760671897472204683) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 111 = 26 +
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
  rw [recurrence5Scalar1Exceptional_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_111 :
    recurrence5Scalar1Exceptional.coeff 111 =
      -(((((153822198687088056604876491 * 10 ^ 70 +
        6327978720447095961792814706809897364144104544581359175666495588412941) * 10 ^ 70 +
        5798191190067308101801928100622992615733352517480946906252037865635437) * 10 ^ 70 +
        6903677189161880327523908299895544332518983525638899905070488235495791) * 10 ^ 70 +
        6328898033227677707891508425151085797658199406442462901654959450737518) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 112 = 27 +
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
  rw [recurrence5Scalar1Exceptional_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_112 :
    recurrence5Scalar1Exceptional.coeff 112 =
      (((((2572851457612651340066347305 * 10 ^ 70 +
        8113135131426644419995422783050982621771348241783706460866436969893175) * 10 ^ 70 +
        1823223871088678920231714614609593076841795655176345461127291894352110) * 10 ^ 70 +
        7618605021515568330502295430147267195513858891175932426595788651654294) * 10 ^ 70 +
        8766977634017066075386908123374192491658062081237125769419730243553096) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 28 +
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
  rw [recurrence5Scalar1Exceptional_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_113 :
    recurrence5Scalar1Exceptional.coeff 113 =
      -(((((20396769437179821754317177969 * 10 ^ 70 +
        2119055351806283680305502047163594936318236839665954907857800095334779) * 10 ^ 70 +
        8858633481894704629572376531887710420070638927586819842912254066976376) * 10 ^ 70 +
        4620438267306112124421270551467906290078200560409947257421512578673427) * 10 ^ 70 +
        8020244072698270086949031114477564560194060621816995371785254361114405) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 29 +
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
  rw [recurrence5Scalar1Exceptional_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_114 :
    recurrence5Scalar1Exceptional.coeff 114 =
      (((((110203563311769230938806089602 * 10 ^ 70 +
        2910374503816196671218253085961247828888330014421146370581004342662993) * 10 ^ 70 +
        2738990341899341225752759997836137932157508699591990077094691601578658) * 10 ^ 70 +
        7197218689263660828805707062068307660883044587704092081960217561808902) * 10 ^ 70 +
        8512126682873621192232702578257965418538245112472265713411539531424561) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 30 +
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
  rw [recurrence5Scalar1Exceptional_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_115 :
    recurrence5Scalar1Exceptional.coeff 115 =
      -(((((359452146661195945470244090450 * 10 ^ 70 +
        6756551886071619542498936536023427818228019459678151603734450811338563) * 10 ^ 70 +
        3762839764557463678010683677601460893933999172162759936118711985411152) * 10 ^ 70 +
        8717331898607526616837760965860210307691589680175943895834870350146922) * 10 ^ 70 +
        1242312414205535154342769495398342704659448211204150499801228794497869) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 31 +
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
  rw [recurrence5Scalar1Exceptional_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_116 :
    recurrence5Scalar1Exceptional.coeff 116 =
      -(((((364688049177329766932389076269 * 10 ^ 70 +
        8155374513706599179342042155380429821194737814665685519456230354165170) * 10 ^ 70 +
        7719031751010739203623717836417433037966339480828698467608932843477586) * 10 ^ 70 +
        1028657397658126994375896812886102229085883626880204538930368586891830) * 10 ^ 70 +
        3465721877235702131918999783170491021544149152923089077569305663838991) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 32 +
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
  rw [recurrence5Scalar1Exceptional_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_117 :
    recurrence5Scalar1Exceptional.coeff 117 =
      (((((16116023543728134545094576098448 * 10 ^ 70 +
        5467364107493009718479817186318391383843319669224363706792031504920586) * 10 ^ 70 +
        5910249634538236685533558712214378209967017210388090865412671333603820) * 10 ^ 70 +
        0029534278793199953800307856946687561121385906781585098007359646208915) * 10 ^ 70 +
        7942421646475550430603794313072834906996176056491080122113449028511019) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 33 +
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
  rw [recurrence5Scalar1Exceptional_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_118 :
    recurrence5Scalar1Exceptional.coeff 118 =
      -(((((144470379258433059024894046298854 * 10 ^ 70 +
        8855100592676405111904913297925359624894568897033212138910991876187333) * 10 ^ 70 +
        2359132490809165948845412207296442853316714423033782570996171969484984) * 10 ^ 70 +
        5586245593726983189853108018274840845514470509717185460678194122340045) * 10 ^ 70 +
        1529423318094183809461984224507880556241437098606395669933560073332082) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 34 +
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
  rw [recurrence5Scalar1Exceptional_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_119 :
    recurrence5Scalar1Exceptional.coeff 119 =
      (((((856414687105059767591500012605172 * 10 ^ 70 +
        9659318072718201181506081390873167649930288976542038365386018027677884) * 10 ^ 70 +
        0005609790600397789194675052880438676843300853328668439727012553643672) * 10 ^ 70 +
        8429546527815175959663582191124575340641752805422100187620547981262142) * 10 ^ 70 +
        7233215770800720946396427900573437041904293909996785772259498998257025) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 35 +
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
  rw [recurrence5Scalar1Exceptional_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_120 :
    recurrence5Scalar1Exceptional.coeff 120 =
      -(((((3475739936214307324165877268089393 * 10 ^ 70 +
        5017359915207607530304012232710370919710804344265231928978519237046994) * 10 ^ 70 +
        7689914908241865867849662016569509093988157534641085099298762351628611) * 10 ^ 70 +
        7863931662231624662079324025083930076909668864387284906744401977147590) * 10 ^ 70 +
        3658320303821349546707658479223726693768946441887229172833977470427657) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 36 +
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
  rw [recurrence5Scalar1Exceptional_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_121 :
    recurrence5Scalar1Exceptional.coeff 121 =
      (((((5597707418334473735472584486410607 * 10 ^ 70 +
        7336053701186740392719612560630795606856892337427806691889771953049351) * 10 ^ 70 +
        9749730272570398355435084001119789874510913094402399574268788216106864) * 10 ^ 70 +
        9863327209434807477713220422697762633915325560635263031475610082179335) * 10 ^ 70 +
        6214093532136946741546871303011991940838579269262915037116442476715224) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 37 +
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
  rw [recurrence5Scalar1Exceptional_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_122 :
    recurrence5Scalar1Exceptional.coeff 122 =
      (((((56118925490995753875947032047725600 * 10 ^ 70 +
        7011196903180109281768626491157840990045131599940112673579378980155093) * 10 ^ 70 +
        0476215230817546216407882935145050466807067323295316899582966711108363) * 10 ^ 70 +
        8627564843937388738846346214943964348127999762188412069279263681944729) * 10 ^ 70 +
        9731005445223862184496449226459289443772896562543433187829760686402750) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 38 +
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
  rw [recurrence5Scalar1Exceptional_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_123 :
    recurrence5Scalar1Exceptional.coeff 123 =
      -(((((695454622774855008116944774888909059 * 10 ^ 70 +
        5287042540415300527692104770053167282250349510997954756743053004897145) * 10 ^ 70 +
        1200388345397980035115475332502993654842620245700729256659629408200283) * 10 ^ 70 +
        7450377231153707241522782390869977220152756805444858350918642986641303) * 10 ^ 70 +
        1656114442815836035729715698786621153403336223093570944773877925524722) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 39 +
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
  rw [recurrence5Scalar1Exceptional_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_124 :
    recurrence5Scalar1Exceptional.coeff 124 =
      (((((4756471398499278460496064375217305006 * 10 ^ 70 +
        7917357031937934203053684863688626723090907705435773244219428424322845) * 10 ^ 70 +
        0096776616711330840131380108013099727404089106440132821240711723085060) * 10 ^ 70 +
        9781692279856632083400519991798281646869475314192236264105779152281404) * 10 ^ 70 +
        4494983309713473048421200333392865606241594339082188097733777869501829) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 40 +
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
  rw [recurrence5Scalar1Exceptional_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_125 :
    recurrence5Scalar1Exceptional.coeff 125 =
      -(((((23263016354632531722857249053013075650 * 10 ^ 70 +
        3388711847071852738839458828314451660454853361727231860788089265339410) * 10 ^ 70 +
        6985056742418555755813190357511385396397800657544550050336762838017737) * 10 ^ 70 +
        9113723507538633612737190382637224973988060431244280907685260171468173) * 10 ^ 70 +
        4890161198387238309593896800170818460523316256195299167830354230976986) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 41 +
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
  rw [recurrence5Scalar1Exceptional_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_126 :
    recurrence5Scalar1Exceptional.coeff 126 =
      (((((75139192589802430420926885511415880322 * 10 ^ 70 +
        9343972390860326833517446803737132146282245564907249277992704393300389) * 10 ^ 70 +
        9623202420590691516180697362333310910083044618732651612984279861949818) * 10 ^ 70 +
        6210753837409233776414367372166380154031498490136151769596834359555658) * 10 ^ 70 +
        7873928649625685169525844362979357459073194670349627171826974730830840) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 42 +
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
  rw [recurrence5Scalar1Exceptional_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_127 :
    recurrence5Scalar1Exceptional.coeff 127 =
      -(((((23411604634051737028834461034463845370 * 10 ^ 70 +
        7123986310780850101930078767731994947940507499578008732691062096073053) * 10 ^ 70 +
        4345002068103261001577025947977662006224049664421910878245091946295925) * 10 ^ 70 +
        2123483692528533990362818340544864611178358079927234416664951717208803) * 10 ^ 70 +
        7013127751519736459698252678467759672992057121134754155715515888759688) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 43 +
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
  rw [recurrence5Scalar1Exceptional_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_128 :
    recurrence5Scalar1Exceptional.coeff 128 =
      -(((((1869766042594343286339473917659486694123 * 10 ^ 70 +
        9929472474403486985953394435436301639901628241857780133056363730330848) * 10 ^ 70 +
        2954478574701130912658119961614737439243630212772358851339983958078961) * 10 ^ 70 +
        7638501075876379337639395595852094081396773089748415104175276580688875) * 10 ^ 70 +
        4108972228597162913228634802644322868450336340615415518669008477540276) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 44 +
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
  rw [recurrence5Scalar1Exceptional_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_129 :
    recurrence5Scalar1Exceptional.coeff 129 =
      (((((17329848844166565282516397364142787028390 * 10 ^ 70 +
        9879046555193680787479906551070815206071032103175177390384212595994454) * 10 ^ 70 +
        9540419685177343562579131540988600889415938840845917221687451610155771) * 10 ^ 70 +
        0711336008414642071722760800068940312081931747937240073881489672420999) * 10 ^ 70 +
        7528550012328951205666241671713708732012498886836617852106204333864035) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 45 +
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
  rw [recurrence5Scalar1Exceptional_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_130 :
    recurrence5Scalar1Exceptional.coeff 130 =
      -(((((103911987218010750096468178882389929013926 * 10 ^ 70 +
        7055245543648549463324380153511840655199748634301453424101112064955165) * 10 ^ 70 +
        9267579818269553173581907428943810504601047034304930286875158927629749) * 10 ^ 70 +
        5980001645086985362064465558152864783538146119969442887626310360797346) * 10 ^ 70 +
        2526694514777034259462548651371789333916033807995210566380623979019041) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 46 +
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
  rw [recurrence5Scalar1Exceptional_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_131 :
    recurrence5Scalar1Exceptional.coeff 131 =
      (((((462972728182337582501443041964675317688639 * 10 ^ 70 +
        7050290466462163963311560490785301421016103838286798533288823844812172) * 10 ^ 70 +
        6246251595195987779512751752496812845952473803793884130589206429878097) * 10 ^ 70 +
        6141717598619069095861023180056333131870406279616978710891499132540891) * 10 ^ 70 +
        8369497226548099887346082751275973732771212216147485467944226765066164) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 47 +
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
  rw [recurrence5Scalar1Exceptional_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_132 :
    recurrence5Scalar1Exceptional.coeff 132 =
      -(((((1391118406794693419782016961116393257072256 * 10 ^ 70 +
        3727223792381636488571020175186064206057594210638087231771072257491255) * 10 ^ 70 +
        6252726845876760727332057451088428395460202189465031254553505624428610) * 10 ^ 70 +
        3154879838967356107191251780496859810760012706514677260462813744186880) * 10 ^ 70 +
        5532448814096559065615952682473237635227136012664727079827106533672402) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 48 +
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
  rw [recurrence5Scalar1Exceptional_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_133 :
    recurrence5Scalar1Exceptional.coeff 133 =
      (((((468246950476744962823470894500824857983240 * 10 ^ 70 +
        7787158255469628501588967143992987775907590961423954508746698877321015) * 10 ^ 70 +
        4275311428433691589489068733828198712144031792781439975692355681611884) * 10 ^ 70 +
        6119414391633012422715579831907603943908890106958791056762939740407462) * 10 ^ 70 +
        6615712987764523540185195656304214964184289114772152972678909047464089) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 49 +
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
  rw [recurrence5Scalar1Exceptional_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_134 :
    recurrence5Scalar1Exceptional.coeff 134 =
      (((((30229808038361437264038151694852037289768981 * 10 ^ 70 +
        7679491219908734054385889435191173525639889568592326431646225641084855) * 10 ^ 70 +
        7019362703904452550902935765858135600582561173228520056760419044764953) * 10 ^ 70 +
        0136847449811126368303788388300479413693823386193458740566914601016908) * 10 ^ 70 +
        7618510590967515349860497508698879121436019168791459051054831430927830) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 50 +
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
  rw [recurrence5Scalar1Exceptional_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_135 :
    recurrence5Scalar1Exceptional.coeff 135 =
      -(((((270882609984981242780711579507452156975963132 * 10 ^ 70 +
        5586194458952401519962329079616664658970613849565765070748651066159969) * 10 ^ 70 +
        6474575529705775333879781528024130152243317465649528035929519442375376) * 10 ^ 70 +
        1865701498719709207648738074791194093755202081712634399395674371531426) * 10 ^ 70 +
        1598625204312291408458263859555839543203567781170776991280973432535305) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 51 +
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
  rw [recurrence5Scalar1Exceptional_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_136 :
    recurrence5Scalar1Exceptional.coeff 136 =
      (((((1594558631468542782796564327990757800883820529 * 10 ^ 70 +
        3381272893899730657877417059590853721359941919856618430990512549368782) * 10 ^ 70 +
        4734523882752011402826530802877598578058897180091124076885561890506013) * 10 ^ 70 +
        2797887504880767880910132322500649091437938086756737609692939299510845) * 10 ^ 70 +
        9984065455322204955015474852884808589092975911547912345187219035984324) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 52 +
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
  rw [recurrence5Scalar1Exceptional_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_137 :
    recurrence5Scalar1Exceptional.coeff 137 =
      -(((((7219530210115395154209018051081520132647675259 * 10 ^ 70 +
        3021396147387584865882446465844730579339909766002794160734297009173555) * 10 ^ 70 +
        2070542865216716828549985225112540331417388571390838918645502871324806) * 10 ^ 70 +
        8968108491259964162487103276536700510282658238268210872274141438354565) * 10 ^ 70 +
        8748397254601665156900216436489324120058893017320431055577304454704641) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 53 +
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
  rw [recurrence5Scalar1Exceptional_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_138 :
    recurrence5Scalar1Exceptional.coeff 138 =
      (((((24440296184131000751000120334392122469624394787 * 10 ^ 70 +
        4663734668785266920727395484188368763810070131632299919925984989083836) * 10 ^ 70 +
        1875444106338107242020321102814816696777594757660239933764164110725015) * 10 ^ 70 +
        1767806437438945686132283023876332863981302567207230682074348820015575) * 10 ^ 70 +
        7020052024049953299156210643443025458728316787431843725230502045394008) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 54 +
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
  rw [recurrence5Scalar1Exceptional_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_139 :
    recurrence5Scalar1Exceptional.coeff 139 =
      -(((((42932330898107862752545613677817533996112432384 * 10 ^ 70 +
        6114411451830263582438476519518418256389175985335672839356886420801691) * 10 ^ 70 +
        4041907352827216512090267260764468518009534881961098154834404765465253) * 10 ^ 70 +
        8051310901672741206365098916777709255898357892412777748013407793455345) * 10 ^ 70 +
        8081111294465436571913823069266711662770014952771291648601704860611608) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 55 +
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
  rw [recurrence5Scalar1Exceptional_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_140 :
    recurrence5Scalar1Exceptional.coeff 140 =
      -(((((180565488435272113167212258743914576046161406177 * 10 ^ 70 +
        4815143500915684512860747875134082541660712092297201092276646530214789) * 10 ^ 70 +
        6640666617106254516862059165802965856050586024977364724122859711426509) * 10 ^ 70 +
        3448616858967461702963183790698952737481528847107771666827741314871873) * 10 ^ 70 +
        5299881050529031630341025354765640655481259778254414162150043185385575) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 56 +
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
  rw [recurrence5Scalar1Exceptional_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_141 :
    recurrence5Scalar1Exceptional.coeff 141 =
      (((((2426715772676617578460289887342821409893998420090 * 10 ^ 70 +
        4279376018316288944958536991344282009692907704787062444610733177639007) * 10 ^ 70 +
        9442604826089467632457281251204735628355249100588815906170709472317116) * 10 ^ 70 +
        1893095887386382293923158526466557441777594797245289833676317304733596) * 10 ^ 70 +
        1843023698532168085689058820394875006884744343866122350893799140270450) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 57 +
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
  rw [recurrence5Scalar1Exceptional_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_142 :
    recurrence5Scalar1Exceptional.coeff 142 =
      -(((((16181401796362481844724366002556163353930428716900 * 10 ^ 70 +
        0062861596785611890456587969844449147712156804958240221501728553701571) * 10 ^ 70 +
        0285697906888949055018837595027776382134555156686591938849527566829466) * 10 ^ 70 +
        2845537826974026341967863577685374843374152166598107660961332199232609) * 10 ^ 70 +
        0898194046034953618723744793788520649893871503790734717878898559740425) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 58 +
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
  rw [recurrence5Scalar1Exceptional_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_143 :
    recurrence5Scalar1Exceptional.coeff 143 =
      (((((82124577804129974010445626967325298844602210606260 * 10 ^ 70 +
        7300667378799914197633969686782135270664182809645005165360734805339577) * 10 ^ 70 +
        9454355029735461814823422100433525386575724870776815392650882676491335) * 10 ^ 70 +
        8205503073013624627953387224995713223768360256172259932135910422241712) * 10 ^ 70 +
        7783359902308656952289113039812569513638728111788245585036420035664748) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 59 +
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
  rw [recurrence5Scalar1Exceptional_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_144 :
    recurrence5Scalar1Exceptional.coeff 144 =
      -(((((338600760921516425243011804463752961910518149965724 * 10 ^ 70 +
        9850333568512471129121665289784750733718760677077264352898846890894551) * 10 ^ 70 +
        6297883667400588407970593400527701760928832903618360642531718635012687) * 10 ^ 70 +
        3645574856894904779287731571050799087536633442934124645328022078679226) * 10 ^ 70 +
        0193702535671923315411846014147554393382620915333169159837566670529468) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 60 +
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
  rw [recurrence5Scalar1Exceptional_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_145 :
    recurrence5Scalar1Exceptional.coeff 145 =
      (((((1095671296117036691410085960358284322827958509583594 * 10 ^ 70 +
        7765661042041980108204857650090383659385848014707740323497810685848841) * 10 ^ 70 +
        1838834709017858655823954490266566528396277734797589777510883801420773) * 10 ^ 70 +
        5394740695182241188695688822695858690734717738171708575999108588156791) * 10 ^ 70 +
        1982339929414085867620264266308606144950501009794565251840835273643618) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 61 +
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
  rw [recurrence5Scalar1Exceptional_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_146 :
    recurrence5Scalar1Exceptional.coeff 146 =
      -(((((2152765761604474215106468498815452501518074056621400 * 10 ^ 70 +
        8072276207685851869855670170003624015726307661359289807145306661596626) * 10 ^ 70 +
        5493786649752687470457517339788595078075214211498508914147005630660336) * 10 ^ 70 +
        1232648183200384082067049293245979315653770101022089402574643850070140) * 10 ^ 70 +
        9062888759660060215656994971365402170159432838876068654789934190983588) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 62 +
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
  rw [recurrence5Scalar1Exceptional_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_147 :
    recurrence5Scalar1Exceptional.coeff 147 =
      -(((((3996210869093637265073907343330120448168225572507200 * 10 ^ 70 +
        9015012373421944834023855274864165477520066351463493828611015685951931) * 10 ^ 70 +
        3212671537985891333201302509595909486584538763647777894313825637492733) * 10 ^ 70 +
        3242240914044944248357238715999093753774553394919636701525656954406771) * 10 ^ 70 +
        0211032975073265495730126183295612349954249669483289559734501470430452) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 63 +
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
  rw [recurrence5Scalar1Exceptional_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_184 :
    recurrence5Scalar1Exceptional.coeff 184 =
      -((((((20 * 10 ^ 70 +
        1493710036384431599993728027222943617578802059473791310627126483867120) * 10 ^ 70 +
        4721080494327208318523038551654143855701197177939531917743585844230034) * 10 ^ 70 +
        8775589366569001837047316362521957686067874787042047548262648712472348) * 10 ^ 70 +
        0849521383414667776094171131989650177358488480678318219767409722370609) * 10 ^ 70 +
        2010266951709773598405495265793340761175598403417078646738991204642660) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 100 +
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
  rw [recurrence5Scalar1Exceptional_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_185 :
    recurrence5Scalar1Exceptional.coeff 185 =
      ((((((41 * 10 ^ 70 +
        3207476595610219266479412801899790445665658423063685513211467221032979) * 10 ^ 70 +
        2382927677680313732495115028575088435589968588778811504884418103990744) * 10 ^ 70 +
        2064202933888008838903880200783956084924336520316090017043489043056835) * 10 ^ 70 +
        3746145157978691655205609509112162719028880666982902240108969311488889) * 10 ^ 70 +
        7766041370222369072023185957025388266613137612079650232643934133740347) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 101 +
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
  rw [recurrence5Scalar1Exceptional_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_186 :
    recurrence5Scalar1Exceptional.coeff 186 =
      -((((((83 * 10 ^ 70 +
        0016358798468660960547586812968523043048609496896229905967839969158955) * 10 ^ 70 +
        9336097821079437583484865355536943990210675765578791411654640014180041) * 10 ^ 70 +
        6023299691266062347242915382468816631220489572916916786758362770681269) * 10 ^ 70 +
        9220861194692317979628340853477230884517671376405255508070510849698548) * 10 ^ 70 +
        5216949598973076655866648464809885102904576998395789861828194955460917) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 102 +
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
  rw [recurrence5Scalar1Exceptional_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_187 :
    recurrence5Scalar1Exceptional.coeff 187 =
      ((((((163 * 10 ^ 70 +
        3373302592487073045486097385974366849256731602494259354057718828561049) * 10 ^ 70 +
        1475732826134819320288870018696787977474793016095134989857950484873261) * 10 ^ 70 +
        1535932577727659420439345068946962428885153528211239788344636322266613) * 10 ^ 70 +
        8977230792421900310184729555006170838935055684810834070011930162988205) * 10 ^ 70 +
        4737129171194499590325321018485854925526556992160304290189410103867221) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 103 +
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
  rw [recurrence5Scalar1Exceptional_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_188 :
    recurrence5Scalar1Exceptional.coeff 188 =
      -((((((314 * 10 ^ 70 +
        9383419133539407301872178605974030473075605401038091951171554092989950) * 10 ^ 70 +
        3402165999497190926793706687082619060832141149000569891953554507316265) * 10 ^ 70 +
        1109589632910696971938777985513772474641686834211208082044585500906992) * 10 ^ 70 +
        4600603879194558742010836995831773559057036945760029141054289349774836) * 10 ^ 70 +
        5358431215384844077842755754459881580796133625477979245717844451700717) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 104 +
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
  rw [recurrence5Scalar1Exceptional_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_189 :
    recurrence5Scalar1Exceptional.coeff 189 =
      ((((((595 * 10 ^ 70 +
        0600104530547616137388358848553084893015838541820004194890154343176118) * 10 ^ 70 +
        9847311763833236256877095194395435025804302247108458587881414098330420) * 10 ^ 70 +
        4023094076695877903906525453449372999357740812201566322205129153961202) * 10 ^ 70 +
        2578547302973329471464787925142981284643057545637821761216511051049529) * 10 ^ 70 +
        0270822106219165318191303528015211480032614748789626346368697787859304) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 105 +
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
  rw [recurrence5Scalar1Exceptional_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_190 :
    recurrence5Scalar1Exceptional.coeff 190 =
      -((((((1101 * 10 ^ 70 +
        8900492465722292656043667164619004779568347780347916165478379991716702) * 10 ^ 70 +
        8781337028137160865751691712860878638848133682467133350797066062173522) * 10 ^ 70 +
        4662087263766668084501810719264085314274527947502437020968846874858118) * 10 ^ 70 +
        3824621101314864576414610841323151456608965961854388342309036328814743) * 10 ^ 70 +
        9986670448036473894964603556248653662019028806896565131220490575903298) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 106 +
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
  rw [recurrence5Scalar1Exceptional_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_191 :
    recurrence5Scalar1Exceptional.coeff 191 =
      ((((((1999 * 10 ^ 70 +
        8558099402946077926202297787838182468681520865395287498672185731392655) * 10 ^ 70 +
        4073464445585956099132043861482681151967773903778945294041821163083066) * 10 ^ 70 +
        3923424987445699499909963925715166427355928701599931061174260086914093) * 10 ^ 70 +
        6997750475482321667364045279682194374859266995853540929317539356551598) * 10 ^ 70 +
        6019583639221107882453539771571541803285189632513122296149874325139962) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 107 +
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
  rw [recurrence5Scalar1Exceptional_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_192 :
    recurrence5Scalar1Exceptional.coeff 192 =
      -((((((3557 * 10 ^ 70 +
        7582710116460236724391411058550273217948305849357962857760612388937203) * 10 ^ 70 +
        0982553009484198270566518920001404201692155050989871268783815842407817) * 10 ^ 70 +
        0030450251191633463874839542026274941289332646406821604520832685752742) * 10 ^ 70 +
        9739367713815950151082990604003977662958850263375470672737764839249388) * 10 ^ 70 +
        4759755514684168175327067033911919006705620870089974584723395977130892) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 108 +
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
  rw [recurrence5Scalar1Exceptional_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_193 :
    recurrence5Scalar1Exceptional.coeff 193 =
      ((((((6204 * 10 ^ 70 +
        4000914906373869491331573076191547932942451397137200506257500894033599) * 10 ^ 70 +
        3952913810800650182957498460269468451215986709852296851824288738574199) * 10 ^ 70 +
        1219342811570311614099244157104546945237991812269172264505099879075826) * 10 ^ 70 +
        1701257029511279021383223327963983475193610864775764455933604721123915) * 10 ^ 70 +
        9229470858035446665005701682610346564306469190813263472022426410678927) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 109 +
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
  rw [recurrence5Scalar1Exceptional_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_194 :
    recurrence5Scalar1Exceptional.coeff 194 =
      -((((((10606 * 10 ^ 70 +
        9609404580104410791912154723838163847059652430485253111836165968373395) * 10 ^ 70 +
        7710344489880801603102648478630084369682803349164058955662649581542891) * 10 ^ 70 +
        1922539158092018346362745197120708090158706844785993432724678695760530) * 10 ^ 70 +
        1423908909116706650340585139932910969934592906183572780851141109281560) * 10 ^ 70 +
        8439420376174381591969707245643827275865695081493796775336680209847967) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 110 +
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
  rw [recurrence5Scalar1Exceptional_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_195 :
    recurrence5Scalar1Exceptional.coeff 195 =
      ((((((17777 * 10 ^ 70 +
        3119341982389037011730281403860353839217293562869852322460670928478239) * 10 ^ 70 +
        2711075225174372255698140084011662532287749108342892449054238697934458) * 10 ^ 70 +
        6177399984087838085261277730531714166503535768360379737848652023249568) * 10 ^ 70 +
        5546578287038025019171528855005057980743430865633124544107024053019564) * 10 ^ 70 +
        1547846519092621071833339844997916466215628830887106676107431204377359) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 111 +
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
  rw [recurrence5Scalar1Exceptional_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_196 :
    recurrence5Scalar1Exceptional.coeff 196 =
      -((((((29210 * 10 ^ 70 +
        2410633914904294221697974442167198297010786746852334014089684462662752) * 10 ^ 70 +
        7861647057225598395060353289268344477381626434360959629828281427652941) * 10 ^ 70 +
        5204539562166252044002553418034005180703669125824812361877256700174583) * 10 ^ 70 +
        9162664423596947100481864819956751550158675761482365566639560142778236) * 10 ^ 70 +
        9968567965203029073149180828145635523811283143765235213628454400642468) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 112 +
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
  rw [recurrence5Scalar1Exceptional_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_197 :
    recurrence5Scalar1Exceptional.coeff 197 =
      ((((((47054 * 10 ^ 70 +
        5658185025423555060423494957756171634597731343319089368098272758544442) * 10 ^ 70 +
        2469369592254520170615612621476269322953102081928425052187905041428067) * 10 ^ 70 +
        7196611162535038404631400231870842375855770258963153826193246411122067) * 10 ^ 70 +
        3286836275326000877262680161947351726785225314748144395589072506785563) * 10 ^ 70 +
        3428084874843879221701482769814618660447257963677791293131741833945545) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 113 +
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
  rw [recurrence5Scalar1Exceptional_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_198 :
    recurrence5Scalar1Exceptional.coeff 198 =
      -((((((74312 * 10 ^ 70 +
        7054648776645295179024274829156907456929581488271344879140069911435800) * 10 ^ 70 +
        7449346326756563838683438308547816352988895859217830557423964163924692) * 10 ^ 70 +
        8763168492647249426699933928176383144105972908837057080336216556079412) * 10 ^ 70 +
        8334191623203138402352135596006041916976736777208437923733313123839410) * 10 ^ 70 +
        5320065599299704926925786175307958536076553172661376357941499426461122) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 114 +
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
  rw [recurrence5Scalar1Exceptional_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_199 :
    recurrence5Scalar1Exceptional.coeff 199 =
      ((((((115055 * 10 ^ 70 +
        9899704046968097270073650299556049005508910311010541143592053683341114) * 10 ^ 70 +
        4374685134603882064042509321581891960641145719001732640507260863446223) * 10 ^ 70 +
        3662564076883126213051117049189679990897145631654713508342141381928286) * 10 ^ 70 +
        9441429871820206133334154830064899505083471895198264751832448051439594) * 10 ^ 70 +
        0245712081025738731254387679181399858748233858651404314155464846040343) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 115 +
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
  rw [recurrence5Scalar1Exceptional_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_200 :
    recurrence5Scalar1Exceptional.coeff 200 =
      -((((((174631 * 10 ^ 70 +
        6997704423708731524255054822671524453404896064440594922111727943417708) * 10 ^ 70 +
        9955246283119005053318380170966583520491964383515979617204808767116841) * 10 ^ 70 +
        9522775321292044269115200051867010571095997703510492675363915016665392) * 10 ^ 70 +
        2783035391419489219810904609786413763465777699248660361598631276964401) * 10 ^ 70 +
        3684650181192711415566617706324682364736185505731254895561528862694864) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 116 +
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
  rw [recurrence5Scalar1Exceptional_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_201 :
    recurrence5Scalar1Exceptional.coeff 201 =
      ((((((259824 * 10 ^ 70 +
        1448141196418539706283790018964254890584886339898263933767630835081751) * 10 ^ 70 +
        4763737682329010022252218391750510995264459159212903238687563069986858) * 10 ^ 70 +
        5846762708598048527788405389945542720068738772295861021036011808551862) * 10 ^ 70 +
        9046725206037107928451728043195598559858372958676173248960731959148840) * 10 ^ 70 +
        0739664899241546603366238062918660351125462842764586855722779867537103) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 117 +
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
  rw [recurrence5Scalar1Exceptional_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_202 :
    recurrence5Scalar1Exceptional.coeff 202 =
      -((((((378917 * 10 ^ 70 +
        5569724906710821121841007950164273332202447230239392707912836961040070) * 10 ^ 70 +
        1494571827644451665041204290226952560652310580916306737914518856076422) * 10 ^ 70 +
        2153234075200920547632009724347507722649462342486240144243993657765630) * 10 ^ 70 +
        3458981472876541992249067341099624403000105251083746930621829470346273) * 10 ^ 70 +
        4161818637236128040309387152644079393879563939845685544642629423247076) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 118 +
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
  rw [recurrence5Scalar1Exceptional_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_203 :
    recurrence5Scalar1Exceptional.coeff 203 =
      ((((((541595 * 10 ^ 70 +
        9066892360149501099609454267417769499245666854898295704056400857589768) * 10 ^ 70 +
        5817757761405496757655810542161034242505088499489340820830077716824957) * 10 ^ 70 +
        5846775196871530269131097362489296562583134027411735087613976193873269) * 10 ^ 70 +
        6626014932827211872549566135576832583908709499312030850754250555713789) * 10 ^ 70 +
        1985559716464144156962189811410689360690796239251433341019775075740019) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 119 +
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
  rw [recurrence5Scalar1Exceptional_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_204 :
    recurrence5Scalar1Exceptional.coeff 204 =
      -((((((758607 * 10 ^ 70 +
        8303923149065897226761362089544824429169494160047997274127476013355512) * 10 ^ 70 +
        6037076882988351514024932078777251647169158152403514745862909754730141) * 10 ^ 70 +
        3751744241848769117970954074150257249564907523902521146947906677057423) * 10 ^ 70 +
        1646638379246005650449542676452450087066590489005111199235298719024223) * 10 ^ 70 +
        2522864788260560592002624451539093980444718763621184079458988420955722) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 120 +
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
  rw [recurrence5Scalar1Exceptional_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_205 :
    recurrence5Scalar1Exceptional.coeff 205 =
      ((((((1041128 * 10 ^ 70 +
        3320133901702435543611961288376010615975337213970959974692952370664001) * 10 ^ 70 +
        0515500778128537435149833696753869293066120435248090532634706115691677) * 10 ^ 70 +
        7815267257473140079880983064246271633306063853712691810182483435939010) * 10 ^ 70 +
        2114385103417934553533840401550689198017284662402479588986967787764279) * 10 ^ 70 +
        8464653426631436062402375952198707545115649430545085968947564800832615) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 121 +
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
  rw [recurrence5Scalar1Exceptional_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_206 :
    recurrence5Scalar1Exceptional.coeff 206 =
      -((((((1399767 * 10 ^ 70 +
        4828316440833415866835732692335470658400997189645287520463285056566745) * 10 ^ 70 +
        1885887710241313076264667751464481193463914921905749907986786705335588) * 10 ^ 70 +
        4793632862409358549842449909968132838531738083865347935358601904331620) * 10 ^ 70 +
        6727688569482013577058158421896732857081950710503462460510671821859952) * 10 ^ 70 +
        2628178412744915130705068308407162643672165350994787398886931167523336) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 122 +
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
  rw [recurrence5Scalar1Exceptional_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_207 :
    recurrence5Scalar1Exceptional.coeff 207 =
      ((((((1843213 * 10 ^ 70 +
        4988176712731375519100745986137026616792667793757095230554082765211260) * 10 ^ 70 +
        0585154781133712685442042092619770476762474263430527062468952751001242) * 10 ^ 70 +
        4339134527066794470940076794493885527003457317653161431439825551591835) * 10 ^ 70 +
        5768895920177516022250008900480789311898135688479938950745622642749719) * 10 ^ 70 +
        4769068580861156556834263640520783001184392361752802916552120471575447) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 123 +
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
  rw [recurrence5Scalar1Exceptional_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_208 :
    recurrence5Scalar1Exceptional.coeff 208 =
      -((((((2376554 * 10 ^ 70 +
        1844142685132333836062780051361469404256827934480183860094489302570200) * 10 ^ 70 +
        7416038129509175715655429970088266575521021852453662369973549233321568) * 10 ^ 70 +
        6049899838865504202825148588411586012740465920212492303773548602327347) * 10 ^ 70 +
        8487546969972971703411847850970214553368181042342855405277149878623807) * 10 ^ 70 +
        2051171976064852588132653278842899547327602834442085364887654794306098) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 124 +
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
  rw [recurrence5Scalar1Exceptional_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_209 :
    recurrence5Scalar1Exceptional.coeff 209 =
      ((((((2999393 * 10 ^ 70 +
        5417171742845252838611228041492131787719075894118297508965579551970548) * 10 ^ 70 +
        6859421965027921551714410368252710748607775313993165358337066681754204) * 10 ^ 70 +
        7147631251356299082475045967394312896120766737192534134624911082873808) * 10 ^ 70 +
        4081436642409857666508180893169315136406775178911508120377838648573653) * 10 ^ 70 +
        1193162843196296092389007478153076138957163003952686564500943587533404) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 125 +
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
  rw [recurrence5Scalar1Exceptional_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_210 :
    recurrence5Scalar1Exceptional.coeff 210 =
      -((((((3703960 * 10 ^ 70 +
        9613739927548736655157561138513783835265768612702807849257030694821880) * 10 ^ 70 +
        7185453904262816073431966525471270246029671631113711365382540356700749) * 10 ^ 70 +
        8814350206170910626174696105404484352580310152456722681522983595126544) * 10 ^ 70 +
        0445304936205970614894077536902034553807131698791832793483397429947524) * 10 ^ 70 +
        4352911025572405311166298663411205768834143577053861760023978357059282) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 126 +
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
  rw [recurrence5Scalar1Exceptional_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_211 :
    recurrence5Scalar1Exceptional.coeff 211 =
      ((((((4473485 * 10 ^ 70 +
        2175053111058518505544141342002074244525629738967552843071308863035697) * 10 ^ 70 +
        6054828288564307933220092992604148515160997661671265128128605215656176) * 10 ^ 70 +
        0228243839316417621010007300883114921103977672673862922412538406633509) * 10 ^ 70 +
        6649134320730850061590160128292828132464366585467206640587506041506116) * 10 ^ 70 +
        6373154859598183108875622965285529531513857449705708390871127819290681) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 127 +
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
  rw [recurrence5Scalar1Exceptional_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_212 :
    recurrence5Scalar1Exceptional.coeff 212 =
      -((((((5281156 * 10 ^ 70 +
        9076127297638442817614208080017594713060149996280445866461312211739130) * 10 ^ 70 +
        6982198789725198580258085272980740192849527150837036190741255864293268) * 10 ^ 70 +
        6797552273644685119491673125457469889527433920114485800026609326364853) * 10 ^ 70 +
        2150042460115181849030785078359441127320454587888703758097761140736122) * 10 ^ 70 +
        7931266748495187309609520217269623780127839465589157677221636884339906) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 128 +
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
  rw [recurrence5Scalar1Exceptional_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_213 :
    recurrence5Scalar1Exceptional.coeff 213 =
      ((((((6090012 * 10 ^ 70 +
        2814471629457525202542907615797889394857967942548414193878413969961167) * 10 ^ 70 +
        8870975210618264379461043907177581726278844944688741217986821792217782) * 10 ^ 70 +
        8419650328416030612283146265881365459233710049955947823145508738224919) * 10 ^ 70 +
        1343702764301296741718487270835716682163372320570570369596101795665822) * 10 ^ 70 +
        4161293070885079980388222181472343619539731803326602448636541841146966) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 129 +
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
  rw [recurrence5Scalar1Exceptional_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_214 :
    recurrence5Scalar1Exceptional.coeff 214 =
      -((((((6854022 * 10 ^ 70 +
        8384155619006191227685058054151968440923248929602532827779661548246923) * 10 ^ 70 +
        8882971717545299155121179299069890881139010304335674123986635259972632) * 10 ^ 70 +
        0644013304709565001422268769193446523036957065661193275932543286069918) * 10 ^ 70 +
        4745932454577049776021042503350409098778179125858132849247319251594452) * 10 ^ 70 +
        7302325237787451497047310660832415979423066839901074734437328243420235) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 130 +
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
  rw [recurrence5Scalar1Exceptional_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_215 :
    recurrence5Scalar1Exceptional.coeff 215 =
      ((((((7520560 * 10 ^ 70 +
        6340654916480256210677240861205902986415778103828260546558494636929250) * 10 ^ 70 +
        0188154618310155885107291032187215023239263467419514050326207901920339) * 10 ^ 70 +
        6670774707760314087787915182818519069547408788696345137741886225659157) * 10 ^ 70 +
        1966562966197372231981560777654797614848381161346750107357931828377070) * 10 ^ 70 +
        1527345335549295698207613234165193076539019748371455854906837815804632) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 131 +
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
  rw [recurrence5Scalar1Exceptional_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_216 :
    recurrence5Scalar1Exceptional.coeff 216 =
      -((((((8034232 * 10 ^ 70 +
        9580534230144944225067529967067159412966680889401326667189382905280414) * 10 ^ 70 +
        4110192021376947087350171368411087897854154530808640113615710570451230) * 10 ^ 70 +
        5547131701085796145436349365784393702593422059635243619977091019079932) * 10 ^ 70 +
        3830575467378455168379584165932514032730490832110767377413052957910105) * 10 ^ 70 +
        8449003552263088330842139030625524725648167463257320144427058209784638) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 132 +
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
  rw [recurrence5Scalar1Exceptional_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_217 :
    recurrence5Scalar1Exceptional.coeff 217 =
      ((((((8341860 * 10 ^ 70 +
        5099887248315477287280738986661849253399972088725850752761625866067309) * 10 ^ 70 +
        2295670239870022396283070865572403640665967345790905450866610684606406) * 10 ^ 70 +
        0692462342977007132616604683961718654081015226196074299702393810485218) * 10 ^ 70 +
        8237773604480957506519733785102099596857276986441020558423927919660805) * 10 ^ 70 +
        5696789219135492725073322541455228899382488781650945533706810605713703) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 133 +
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
  rw [recurrence5Scalar1Exceptional_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_218 :
    recurrence5Scalar1Exceptional.coeff 218 =
      -((((((8398143 * 10 ^ 70 +
        0411910358159845689776649379802195410792928623770048990136087702236220) * 10 ^ 70 +
        1174772528374933948681641426192217131643171380330645557279468418671298) * 10 ^ 70 +
        6237467547322739846036560522466485600840705493868843754629928650181706) * 10 ^ 70 +
        5072273555723191404583007540870299939824748912980577152442289597001968) * 10 ^ 70 +
        1799732161724178621320983410257162873853705169569811221656587720951772) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 134 +
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
  rw [recurrence5Scalar1Exceptional_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
