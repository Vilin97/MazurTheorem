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

private theorem recurrence5Scalar1Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_362 :
    recurrence5Scalar1Exceptional.coeff 362 =
      -(((((36707239259328763023605099603840680132 * 10 ^ 70 +
        1888460396002603313116876070513469151371004624326379705866940433037483) * 10 ^ 70 +
        8034380775870744233241290408199427839807890527477638378704864036046058) * 10 ^ 70 +
        1507892569513594425568073667779004652765158332677933094715454218777644) * 10 ^ 70 +
        3992679187290564154597576533183298022141780689642617935645373623027156) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 278 +
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
  rw [recurrence5Scalar1Exceptional_coeff_362_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_363 :
    recurrence5Scalar1Exceptional.coeff 363 =
      (((((6825196189979622334377593098527800209 * 10 ^ 70 +
        4896054940028876358320530476486956122006328182559294772518145984965249) * 10 ^ 70 +
        1636480896595808921238946524694235743242266133711861086956536501527129) * 10 ^ 70 +
        7988513881951892224500755503245810202443276658883212309282755332896452) * 10 ^ 70 +
        6369062363935424446244843168612036605218193867972179999203185433746097) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 279 +
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
  rw [recurrence5Scalar1Exceptional_coeff_363_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_364 :
    recurrence5Scalar1Exceptional.coeff 364 =
      -(((((335051390301929325266190219898849797 * 10 ^ 70 +
        0579635457394470459142619503814701793175143107540083887137670787450485) * 10 ^ 70 +
        0297528816682696706320552618802005861629571590922235002997781311971284) * 10 ^ 70 +
        6496909259551424549719466739771756761208134690560390233441497896562349) * 10 ^ 70 +
        8501424793373942213308581775506468948193005773615376165162822384396213) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 280 +
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
  rw [recurrence5Scalar1Exceptional_coeff_364_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_365 :
    recurrence5Scalar1Exceptional.coeff 365 =
      -(((((537580659299944473373727615342644919 * 10 ^ 70 +
        8836397963561981081291167315708230092196455439983374725417450059777341) * 10 ^ 70 +
        7566946105322926248094615959884648671836328172966406622717945591973085) * 10 ^ 70 +
        0174478185071296706143344096130720758143574303872375281080542371919564) * 10 ^ 70 +
        1089857623412900736801931091864464385724054568562637812230403630145609) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 281 +
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
  rw [recurrence5Scalar1Exceptional_coeff_365_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_366 :
    recurrence5Scalar1Exceptional.coeff 366 =
      (((((385132035321086405013471593156636357 * 10 ^ 70 +
        3926881288780403815188696611594908489721669575992350250803940628475098) * 10 ^ 70 +
        4083343215925094184405288366887787699209885540283613059273914490612993) * 10 ^ 70 +
        3326839667055013251070790885186123154440385105444008241632348990438983) * 10 ^ 70 +
        6966422850652579502261695064284022734895961602507637733964572382846910) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 282 +
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
  rw [recurrence5Scalar1Exceptional_coeff_366_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_367 :
    recurrence5Scalar1Exceptional.coeff 367 =
      -(((((190656661908334444520109906449471415 * 10 ^ 70 +
        8643770018342837543577497445696953832837824290195961109991708329495608) * 10 ^ 70 +
        3127826255608607298946954701973340433167974572773052510001373657902663) * 10 ^ 70 +
        1336078088732733284582837563069326774387150383979032694202963161303523) * 10 ^ 70 +
        7067104197691440522982311166212805944086087347012323064488538657417056) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 283 +
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
  rw [recurrence5Scalar1Exceptional_coeff_367_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_368 :
    recurrence5Scalar1Exceptional.coeff 368 =
      (((((81446077707704404923859971757567868 * 10 ^ 70 +
        6290808018099563714050349034431407688514736132452956580817848823369224) * 10 ^ 70 +
        9184527970155464861965845019485505720419484731859914829228011290710557) * 10 ^ 70 +
        1954906211961058604666692007235644681054488544698306872415761618234113) * 10 ^ 70 +
        5038591507658433483446204181547635884052059415290816394671701460460607) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 284 +
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
  rw [recurrence5Scalar1Exceptional_coeff_368_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_369 :
    recurrence5Scalar1Exceptional.coeff 369 =
      -(((((31950634731797665187948212561793699 * 10 ^ 70 +
        8789032558951927899188710443177660477597844197660274160101282854375674) * 10 ^ 70 +
        0527309907261861761084388968543667224104591652289535725497008734838407) * 10 ^ 70 +
        0277976010826250930243208474564831858097709145069618203153750825491799) * 10 ^ 70 +
        4595676268680372984980397577579463019490824889305070683460271718543468) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 285 +
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
  rw [recurrence5Scalar1Exceptional_coeff_369_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_370 :
    recurrence5Scalar1Exceptional.coeff 370 =
      (((((11802351565883735350439060545799904 * 10 ^ 70 +
        4072508794551959653527261955591603217130545322056826549122372609009685) * 10 ^ 70 +
        8624532112052407312238138347102498434332591768840383597575406033675105) * 10 ^ 70 +
        7162039955423633427915552063865302125385568545025100187127098554459707) * 10 ^ 70 +
        5887403245175250888619853839394337252871385215932935528770598148100553) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 286 +
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
  rw [recurrence5Scalar1Exceptional_coeff_370_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_371 :
    recurrence5Scalar1Exceptional.coeff 371 =
      -(((((4151575692487954759621635054455146 * 10 ^ 70 +
        8123538375452406661585830968773567100729794909133451599103908990782836) * 10 ^ 70 +
        6061006220144135090276760541345863022595568282023184964943569678212611) * 10 ^ 70 +
        7250785300715521649601804351547649406467849503789994611841587001118272) * 10 ^ 70 +
        3100986671066200185033705018492747778686696555208849934299074798913662) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 287 +
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
  rw [recurrence5Scalar1Exceptional_coeff_371_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_372 :
    recurrence5Scalar1Exceptional.coeff 372 =
      (((((1396977176688767010229058270933971 * 10 ^ 70 +
        3898534638661191382717582269449854485382620746166511572105773310425618) * 10 ^ 70 +
        3616445112377973315310413233921043781844889409070420363914278873934221) * 10 ^ 70 +
        0714916670881558875137488451832149850187453754069304891399508786705469) * 10 ^ 70 +
        6675332264834107210765439637421117808960304899461119911392187453776825) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 288 +
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
  rw [recurrence5Scalar1Exceptional_coeff_372_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_373 :
    recurrence5Scalar1Exceptional.coeff 373 =
      -(((((449930429576492523855406377661078 * 10 ^ 70 +
        9086279470277145081138010384731707949547581201974783316311401565058105) * 10 ^ 70 +
        9444766442148752396658928920497081468003927795385358929489422769696091) * 10 ^ 70 +
        4903830008237716743740966598657466036724711253764137825582624631532209) * 10 ^ 70 +
        0012297041627205886632018402135091614376852412412099936051171353566937) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 289 +
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
  rw [recurrence5Scalar1Exceptional_coeff_373_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_374 :
    recurrence5Scalar1Exceptional.coeff 374 =
      (((((138356538244971380793203761675903 * 10 ^ 70 +
        2567135025328605012601989536090009122841369646219199378368039291790714) * 10 ^ 70 +
        0041021605373745024481856213176172335900815938663205780477854673609335) * 10 ^ 70 +
        5374429638304225483813682824717719623615826946994578546562276414927401) * 10 ^ 70 +
        5524079130367233250183145987619988117103747597872694589512097999581034) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 290 +
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
  rw [recurrence5Scalar1Exceptional_coeff_374_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_375 :
    recurrence5Scalar1Exceptional.coeff 375 =
      -(((((40390647692496897602028792000807 * 10 ^ 70 +
        1365273769037002300810960150068439107140349463836652236541637798534459) * 10 ^ 70 +
        4865494810803222852792205834690992411463750722334160466533820365053543) * 10 ^ 70 +
        7363812260577444529736389170885220408368718792369826731075282566183893) * 10 ^ 70 +
        3312748335051808481244012538112092240458919925516901077592117526202094) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 291 +
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
  rw [recurrence5Scalar1Exceptional_coeff_375_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_376 :
    recurrence5Scalar1Exceptional.coeff 376 =
      (((((11080681258211045594060379719641 * 10 ^ 70 +
        8430386298690790997323760873421495994950331875878726894326820094431111) * 10 ^ 70 +
        6806204629014384672902222285691673615601577713864945876415616334015834) * 10 ^ 70 +
        2378804412000522547069905577629983526936664123907249328373703013382123) * 10 ^ 70 +
        5331715206942105096665365368205315896462119236984470017753399767578347) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 292 +
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
  rw [recurrence5Scalar1Exceptional_coeff_376_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_377 :
    recurrence5Scalar1Exceptional.coeff 377 =
      -(((((2805048017336980407512006482125 * 10 ^ 70 +
        1529939714035272224715538428966451088007470380717930898506675228244312) * 10 ^ 70 +
        9383658844561448443182810364606645796490831803434077899246910434044133) * 10 ^ 70 +
        0857864541465381078282787842363649042879291257099361168617467167641808) * 10 ^ 70 +
        8770597141551202510004275950089561831809807010226440454806293042752111) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 293 +
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
  rw [recurrence5Scalar1Exceptional_coeff_377_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_378 :
    recurrence5Scalar1Exceptional.coeff 378 =
      (((((631811094125512386324115626766 * 10 ^ 70 +
        4704795579768330229819496611085518733846060293222469285798312582844999) * 10 ^ 70 +
        7887945126677299934031727596744433524680716473018167201678958192009070) * 10 ^ 70 +
        8673235584992385875554192407136583602453828712174518011762902871582817) * 10 ^ 70 +
        6558154213132174566452851719404353982982637825023253010277294521099336) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 294 +
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
  rw [recurrence5Scalar1Exceptional_coeff_378_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (379 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_379 :
    recurrence5Scalar1Exceptional.coeff 379 =
      -(((((115435175388248151907451605707 * 10 ^ 70 +
        5128236481507551169973154495033581130183913160532866431827403293577526) * 10 ^ 70 +
        0299743598892304428315460692847188585155545845893889812806702642411776) * 10 ^ 70 +
        6571940223318434590438368714813512618838953783626326765074108168202465) * 10 ^ 70 +
        3840503529101792003562746334725883633283789788925310481444532102908910) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 295 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (380 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_380 :
    recurrence5Scalar1Exceptional.coeff 380 =
      (((((11145060379671509390076018971 * 10 ^ 70 +
        8616090231280127423001051800686795421873048182056879424908250705105199) * 10 ^ 70 +
        2348418807020182488015426883055738268612013504610685780884544569142601) * 10 ^ 70 +
        3534607364209309460663186629821569329386910869885775808711311437221768) * 10 ^ 70 +
        3198663836583949461364904354460066226385467586632265947381239727139257) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 296 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 19 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (381 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_381 :
    recurrence5Scalar1Exceptional.coeff 381 =
      (((((3348346565696827143006259034 * 10 ^ 70 +
        5090455371168827787020641916174540767421330327184298824428567599279489) * 10 ^ 70 +
        8028345843841891718973977870437021191556736587976338239541777740387820) * 10 ^ 70 +
        2499714571759595654879098104989517916332267609683394843110852346728130) * 10 ^ 70 +
        7353553954342636819098959476979770314948466918740681799810912971453657) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 297 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 18 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (382 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_382 :
    recurrence5Scalar1Exceptional.coeff 382 =
      -(((((2693932424234780832732179796 * 10 ^ 70 +
        7939370384181989085740599666174518174687176511873715594867390238449170) * 10 ^ 70 +
        5613591143740190468099800902375411884740473474323579170096392345481543) * 10 ^ 70 +
        1107386843702531298426163501717945059701195247917293286976903881490692) * 10 ^ 70 +
        2532476871669128489390378079155905090430769563701637107283673680172257) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 298 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 17 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (383 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_383 :
    recurrence5Scalar1Exceptional.coeff 383 =
      (((((1169741903514739228169303032 * 10 ^ 70 +
        4599689310492587555709914481627144398394924081208238957340049827934653) * 10 ^ 70 +
        4918178949042169382598538356813816906518133874283115221498808695219102) * 10 ^ 70 +
        6312653828029490289555233434123914545080948996610428947186471965266142) * 10 ^ 70 +
        6842377183872408007101224732911221312334091227167109821289409289013396) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 299 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 16 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_383_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (384 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_384 :
    recurrence5Scalar1Exceptional.coeff 384 =
      -(((((407818674991069471072099327 * 10 ^ 70 +
        1707616238817509460113103632230947948255867346780382005128646999325795) * 10 ^ 70 +
        7178200176832715883436823019781487838943069612732169002119525900956203) * 10 ^ 70 +
        8624435156209798582142264696978638841849770302993300748809283420613219) * 10 ^ 70 +
        8863240518158489851059806051756928804111227288194957268347597665759804) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 300 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 15 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_384_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (385 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_385 :
    recurrence5Scalar1Exceptional.coeff 385 =
      (((((124029176712217823530993161 * 10 ^ 70 +
        3533897846538950921237813271891079400678998853792269886330834714133944) * 10 ^ 70 +
        7967271712819935147580035241737837592901155065811736736060001790650435) * 10 ^ 70 +
        9830264745169305388604149306634704312969034232020088405783282238554468) * 10 ^ 70 +
        3692351263947414041517931595639707054594848439420939724092069327356557) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 301 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 14 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_385_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (386 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_386 :
    recurrence5Scalar1Exceptional.coeff 386 =
      -(((((33818888281238083708044722 * 10 ^ 70 +
        5787319771452155005715279128753488239497588956432081602045280942640179) * 10 ^ 70 +
        8065750652931011865484047066797981193317295467419918480471458936866646) * 10 ^ 70 +
        0473985156845036009552890560151781681904138535989897121975799567673662) * 10 ^ 70 +
        8332570772218881813747503056253943286932954419704191570541989887127142) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 302 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 13 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_386_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (387 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_387 :
    recurrence5Scalar1Exceptional.coeff 387 =
      (((((8323774464341653217021035 * 10 ^ 70 +
        2258125457792182478862186939334011074497994028898844328480812011635718) * 10 ^ 70 +
        5176425765943017011764129786866385032242489279598146396651875693828695) * 10 ^ 70 +
        3922276732013584768014194190856634203044511518520700870780115286016861) * 10 ^ 70 +
        3148688700644817433401344694832353593762340808379727628544804144827637) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 303 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 12 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_387_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (388 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_388 :
    recurrence5Scalar1Exceptional.coeff 388 =
      -(((((1835934166351940622774946 * 10 ^ 70 +
        1603560265119847238834996801878481397234256482614124172105958804755143) * 10 ^ 70 +
        1353813928295573508581532623578754484834953870796737646516799518817584) * 10 ^ 70 +
        0603049726126178236165122539141835320901297979081051168277441305190441) * 10 ^ 70 +
        6216897087279296740068885570689196881820948574975238529251129344988854) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 304 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 11 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_388_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (389 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_389 :
    recurrence5Scalar1Exceptional.coeff 389 =
      (((((353362235131141899608932 * 10 ^ 70 +
        3587285260056535970802790409738203742359454890441518895663906438532916) * 10 ^ 70 +
        5945221429922441636894900675507071857261664237270263971132403026111380) * 10 ^ 70 +
        6171737509592854158086956380852824794353421164783016900223683969079318) * 10 ^ 70 +
        2629737797127215422111342394503932951450249108659553182995119720534681) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 305 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 10 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_389_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (390 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_390 :
    recurrence5Scalar1Exceptional.coeff 390 =
      -(((((55016026110522514658506 * 10 ^ 70 +
        4588014504598740161723642756140854333342064954829444724953862675483915) * 10 ^ 70 +
        8515106764223380616665566659337254750200112905706998694035734667593638) * 10 ^ 70 +
        1947097702510986423984655755803774023083599417666688785764192246603597) * 10 ^ 70 +
        8300564529472514312752817662706079447025787204570158598934315967277194) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 306 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 9 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_390_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (391 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_391 :
    recurrence5Scalar1Exceptional.coeff 391 =
      (((((5003451963078258005865 * 10 ^ 70 +
        7554227079761463544145948507793875438639328495388076674793295488074539) * 10 ^ 70 +
        1592206549898648441442532872686978871679622399248591968882010358257281) * 10 ^ 70 +
        2955492327260133560786004224203741833075598297798423670389708104038023) * 10 ^ 70 +
        6899057552548202610687098283141072162339498653158659429613672564924806) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 307 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 8 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_391_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (392 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_392 :
    recurrence5Scalar1Exceptional.coeff 392 =
      (((((720892982574318692369 * 10 ^ 70 +
        5470788943111916757223109203738335968180719226388132887373885190257901) * 10 ^ 70 +
        9868746600882371063785460791975714560721585446102131507991487064896347) * 10 ^ 70 +
        0184971488125567134662634537621900638321068159579946755457420986639945) * 10 ^ 70 +
        0138162314047374702660433816730580945951821002881100599008091804684375) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 308 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 7 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_392_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Exceptional_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (393 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_393 :
    recurrence5Scalar1Exceptional.coeff 393 =
      -(((((557642553137562246535 * 10 ^ 70 +
        0853938513768944271709081104303797626175469369571667324216295569155702) * 10 ^ 70 +
        3905144994027826800761284562545470290582699625718085043271655805116703) * 10 ^ 70 +
        2533532990319559339537156470190278565534192121295264485101151521258053) * 10 ^ 70 +
        3230471710106911884389209705740779361040439696798220433274311185796441) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 309 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 6 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_393_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
