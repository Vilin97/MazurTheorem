/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C2_coeff_0
  recurrence4C2_coeff_1
  recurrence4C2_coeff_10
  recurrence4C2_coeff_100
  recurrence4C2_coeff_101
  recurrence4C2_coeff_102
  recurrence4C2_coeff_103
  recurrence4C2_coeff_104
  recurrence4C2_coeff_105
  recurrence4C2_coeff_106
  recurrence4C2_coeff_107
  recurrence4C2_coeff_108
  recurrence4C2_coeff_109
  recurrence4C2_coeff_11
  recurrence4C2_coeff_110
  recurrence4C2_coeff_111
  recurrence4C2_coeff_112
  recurrence4C2_coeff_113
  recurrence4C2_coeff_114
  recurrence4C2_coeff_115
  recurrence4C2_coeff_116
  recurrence4C2_coeff_117
  recurrence4C2_coeff_118
  recurrence4C2_coeff_119
  recurrence4C2_coeff_12
  recurrence4C2_coeff_120
  recurrence4C2_coeff_121
  recurrence4C2_coeff_122
  recurrence4C2_coeff_123
  recurrence4C2_coeff_124
  recurrence4C2_coeff_125
  recurrence4C2_coeff_126
  recurrence4C2_coeff_127
  recurrence4C2_coeff_128
  recurrence4C2_coeff_129
  recurrence4C2_coeff_13
  recurrence4C2_coeff_130
  recurrence4C2_coeff_131
  recurrence4C2_coeff_132
  recurrence4C2_coeff_133
  recurrence4C2_coeff_134
  recurrence4C2_coeff_135
  recurrence4C2_coeff_136
  recurrence4C2_coeff_137
  recurrence4C2_coeff_138
  recurrence4C2_coeff_139
  recurrence4C2_coeff_14
  recurrence4C2_coeff_140
  recurrence4C2_coeff_141
  recurrence4C2_coeff_142
  recurrence4C2_coeff_143
  recurrence4C2_coeff_144
  recurrence4C2_coeff_145
  recurrence4C2_coeff_15
  recurrence4C2_coeff_16
  recurrence4C2_coeff_17
  recurrence4C2_coeff_18
  recurrence4C2_coeff_19
  recurrence4C2_coeff_2
  recurrence4C2_coeff_20
  recurrence4C2_coeff_21
  recurrence4C2_coeff_22
  recurrence4C2_coeff_23
  recurrence4C2_coeff_24

attribute [local simp]
  recurrence4C2_coeff_25
  recurrence4C2_coeff_26
  recurrence4C2_coeff_27
  recurrence4C2_coeff_28
  recurrence4C2_coeff_29
  recurrence4C2_coeff_3
  recurrence4C2_coeff_30
  recurrence4C2_coeff_31
  recurrence4C2_coeff_32
  recurrence4C2_coeff_33
  recurrence4C2_coeff_34
  recurrence4C2_coeff_35
  recurrence4C2_coeff_36
  recurrence4C2_coeff_37
  recurrence4C2_coeff_38
  recurrence4C2_coeff_39
  recurrence4C2_coeff_4
  recurrence4C2_coeff_40
  recurrence4C2_coeff_41
  recurrence4C2_coeff_42
  recurrence4C2_coeff_43
  recurrence4C2_coeff_44
  recurrence4C2_coeff_45
  recurrence4C2_coeff_46
  recurrence4C2_coeff_47
  recurrence4C2_coeff_48
  recurrence4C2_coeff_49
  recurrence4C2_coeff_5
  recurrence4C2_coeff_50
  recurrence4C2_coeff_51
  recurrence4C2_coeff_52
  recurrence4C2_coeff_53
  recurrence4C2_coeff_54
  recurrence4C2_coeff_55
  recurrence4C2_coeff_56
  recurrence4C2_coeff_57
  recurrence4C2_coeff_58
  recurrence4C2_coeff_59
  recurrence4C2_coeff_6
  recurrence4C2_coeff_60
  recurrence4C2_coeff_61
  recurrence4C2_coeff_62
  recurrence4C2_coeff_63
  recurrence4C2_coeff_64
  recurrence4C2_coeff_65
  recurrence4C2_coeff_66
  recurrence4C2_coeff_67
  recurrence4C2_coeff_68
  recurrence4C2_coeff_69
  recurrence4C2_coeff_7
  recurrence4C2_coeff_70
  recurrence4C2_coeff_71
  recurrence4C2_coeff_72
  recurrence4C2_coeff_73
  recurrence4C2_coeff_74
  recurrence4C2_coeff_75
  recurrence4C2_coeff_76
  recurrence4C2_coeff_77
  recurrence4C2_coeff_78
  recurrence4C2_coeff_79
  recurrence4C2_coeff_8
  recurrence4C2_coeff_80
  recurrence4C2_coeff_81
  recurrence4C2_coeff_82

attribute [local simp]
  recurrence4C2_coeff_83
  recurrence4C2_coeff_84
  recurrence4C2_coeff_85
  recurrence4C2_coeff_86
  recurrence4C2_coeff_87
  recurrence4C2_coeff_88
  recurrence4C2_coeff_89
  recurrence4C2_coeff_9
  recurrence4C2_coeff_90
  recurrence4C2_coeff_91
  recurrence4C2_coeff_92
  recurrence4C2_coeff_93
  recurrence4C2_coeff_94
  recurrence4C2_coeff_95
  recurrence4C2_coeff_96
  recurrence4C2_coeff_97
  recurrence4C2_coeff_98
  recurrence4C2_coeff_99
  recurrence4ExceptionalProduct_coeff_100
  recurrence4ExceptionalProduct_coeff_101
  recurrence4ExceptionalProduct_coeff_102
  recurrence4ExceptionalProduct_coeff_103
  recurrence4ExceptionalProduct_coeff_104
  recurrence4ExceptionalProduct_coeff_105
  recurrence4ExceptionalProduct_coeff_106
  recurrence4ExceptionalProduct_coeff_107
  recurrence4ExceptionalProduct_coeff_108
  recurrence4ExceptionalProduct_coeff_109
  recurrence4ExceptionalProduct_coeff_110
  recurrence4ExceptionalProduct_coeff_111
  recurrence4ExceptionalProduct_coeff_112
  recurrence4ExceptionalProduct_coeff_113
  recurrence4ExceptionalProduct_coeff_114
  recurrence4ExceptionalProduct_coeff_115
  recurrence4ExceptionalProduct_coeff_116
  recurrence4ExceptionalProduct_coeff_117
  recurrence4ExceptionalProduct_coeff_118
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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
  recurrence4ExceptionalProduct_coeff_75
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_80
  recurrence4ExceptionalProduct_coeff_81
  recurrence4ExceptionalProduct_coeff_82
  recurrence4ExceptionalProduct_coeff_83
  recurrence4ExceptionalProduct_coeff_84
  recurrence4ExceptionalProduct_coeff_85
  recurrence4ExceptionalProduct_coeff_86
  recurrence4ExceptionalProduct_coeff_87
  recurrence4ExceptionalProduct_coeff_88
  recurrence4ExceptionalProduct_coeff_89
  recurrence4ExceptionalProduct_coeff_90
  recurrence4ExceptionalProduct_coeff_91
  recurrence4ExceptionalProduct_coeff_92
  recurrence4ExceptionalProduct_coeff_93
  recurrence4ExceptionalProduct_coeff_94
  recurrence4ExceptionalProduct_coeff_95
  recurrence4ExceptionalProduct_coeff_96
  recurrence4ExceptionalProduct_coeff_97
  recurrence4ExceptionalProduct_coeff_98
  recurrence4ExceptionalProduct_coeff_99

private theorem recurrence4Scalar2Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (220 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_220 :
    recurrence4Scalar2Exceptional.coeff 220 =
      (((((96990572399880666595584 * 10 ^ 70 +
        3074436925106086372612361088403799905447405640776345096113403713785045) * 10 ^ 70 +
        2994941376284190827068514790901659618297071931698154190391202560263752) * 10 ^ 70 +
        0556651964890901801341947429405978958483653998208600523663385575220557) * 10 ^ 70 +
        7770966421007974026265132653273238063768405920967712458534166632651256) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (220 - x)) = _
  rw [show 221 = 75 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (221 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_221 :
    recurrence4Scalar2Exceptional.coeff 221 =
      -(((((155505078523931214426595 * 10 ^ 70 +
        6629293440157728591720942433355970403182661171974366027072467985813020) * 10 ^ 70 +
        6896901537083320453238534506508237146535781420041909012826312829767703) * 10 ^ 70 +
        9462088193720686484117877498534407073257677102587815985372047227952596) * 10 ^ 70 +
        2184341858465171504561692143005200674912428077809566312106746535260500) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (221 - x)) = _
  rw [show 222 = 76 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (222 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_222 :
    recurrence4Scalar2Exceptional.coeff 222 =
      (((((245937558601606372173042 * 10 ^ 70 +
        3015266381173582492468158586054650713170180371644930719471376385962135) * 10 ^ 70 +
        5070421405975941457859059038441459743792291218763176361617606979331187) * 10 ^ 70 +
        9482489592386383214226752166415889301748028435698566406726650351118601) * 10 ^ 70 +
        2399852785271507281968500748004210150899997220126898815087227540045422) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (222 - x)) = _
  rw [show 223 = 77 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (223 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_223 :
    recurrence4Scalar2Exceptional.coeff 223 =
      -(((((383692577220865713733985 * 10 ^ 70 +
        3354536019171168180416318056575538209111931965422962523045807690006251) * 10 ^ 70 +
        3855823328248036815915967877595575144884668504599904686665081527285673) * 10 ^ 70 +
        7016628506585596906760871437904452585010478004563657217786129781478993) * 10 ^ 70 +
        9073008671988456917280422746243401860162123780969066401092222493844334) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (223 - x)) = _
  rw [show 224 = 78 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (224 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_224 :
    recurrence4Scalar2Exceptional.coeff 224 =
      (((((590517470854293975528825 * 10 ^ 70 +
        3361381859009075266618285547227424177240335988098918902119171596331793) * 10 ^ 70 +
        3986258172326196850684818044991565767501595548731007695484286466255590) * 10 ^ 70 +
        9010311005906438042916955059934172306039790246561012747680667450044327) * 10 ^ 70 +
        4407814490616988580725712143169919698874338187945878245418123942444837) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (224 - x)) = _
  rw [show 225 = 79 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (225 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_225 :
    recurrence4Scalar2Exceptional.coeff 225 =
      -(((((896571649534707915582320 * 10 ^ 70 +
        5098073138260137319430534445005214752600846206387670175787140095220002) * 10 ^ 70 +
        0001054268156632968181246299099095439268466423147943346483352285803502) * 10 ^ 70 +
        3454115791488070456658593507331451513103165280946823426656421787039406) * 10 ^ 70 +
        2593034424912402717480901466663028612965577202025847796168479419459377) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (225 - x)) = _
  rw [show 226 = 80 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (226 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_226 :
    recurrence4Scalar2Exceptional.coeff 226 =
      (((((1342925044552475265922709 * 10 ^ 70 +
        5588891507028055889868439438085264271456081007372742709692243267219767) * 10 ^ 70 +
        7062420298806750702572197714914519287987118255138816740425016621625859) * 10 ^ 70 +
        7453220924540065175184053223320245691677766744066347529077812269819405) * 10 ^ 70 +
        4849491805281318448864102784965425148325051019828218896073343769950379) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (226 - x)) = _
  rw [show 227 = 81 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (227 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_227 :
    recurrence4Scalar2Exceptional.coeff 227 =
      -(((((1984468614692001276422854 * 10 ^ 70 +
        4074198751885349315335840600374659268099359427786294093230171245689151) * 10 ^ 70 +
        9464942479655323161230438903394547384051319931606004047290227151090278) * 10 ^ 70 +
        9007589634834827646018549165277222704646727550206249834197539256298016) * 10 ^ 70 +
        6413612629326814145755755076347128845005571099285461531342643575305583) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (227 - x)) = _
  rw [show 228 = 82 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (228 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_228 :
    recurrence4Scalar2Exceptional.coeff 228 =
      (((((2893164392276006285930337 * 10 ^ 70 +
        7140796834700328587531723453426022018630719338493311318839192690369459) * 10 ^ 70 +
        1105374526847937614057493925776070218159462016657032132869305109134907) * 10 ^ 70 +
        9593155333636258435145793545383109558913218701244223143710005778504959) * 10 ^ 70 +
        3240414554284395145054446923524598285237443555390191912215634780459734) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (228 - x)) = _
  rw [show 229 = 83 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (229 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_229 :
    recurrence4Scalar2Exceptional.coeff 229 =
      -(((((4161488413420686478160522 * 10 ^ 70 +
        1981115764210037281810150762114465633936316767138214777188584046322764) * 10 ^ 70 +
        2546863052082495442672283822108440297159653958691518440823142412111357) * 10 ^ 70 +
        9280448032755977717677802466678763386110977251103281154329941221410572) * 10 ^ 70 +
        9559303314902493598532822284550946890156817202960291658420367501406362) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (229 - x)) = _
  rw [show 230 = 84 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (230 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_230 :
    recurrence4Scalar2Exceptional.coeff 230 =
      (((((5905828418404347428331250 * 10 ^ 70 +
        1187445638988645268933892114404313592330953611937099999445526315566060) * 10 ^ 70 +
        0641502829603140315478216121788116601053158033682824778986508735670405) * 10 ^ 70 +
        0906265391824708669794130509715058434064817876977091253288293464422587) * 10 ^ 70 +
        1531046933760324142009132613754901079765504122115647519162181659459036) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (230 - x)) = _
  rw [show 231 = 85 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (231 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_231 :
    recurrence4Scalar2Exceptional.coeff 231 =
      -(((((8269494216686292148270952 * 10 ^ 70 +
        0494648920506685206888794371170782546129390819922292145112607314509118) * 10 ^ 70 +
        5491305809622210371723297552835564828291100608077161418756645749235251) * 10 ^ 70 +
        0780191952653683919273837994058346534324045423194745549664021645337148) * 10 ^ 70 +
        0369609293469278660848974643039182421492128484721571129255309688515616) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (231 - x)) = _
  rw [show 232 = 86 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (232 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_232 :
    recurrence4Scalar2Exceptional.coeff 232 =
      (((((11424891058704695071263194 * 10 ^ 70 +
        8785122985415963576339169297287235046055508903141423981814308302939396) * 10 ^ 70 +
        7073129694454843115506360834747208632168160330481429080196543745380933) * 10 ^ 70 +
        7896140132143060105861416538532361570723239284825176302759834049624454) * 10 ^ 70 +
        4787709868398228541359593479721221823086332516371341442157665012388527) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (232 - x)) = _
  rw [show 233 = 87 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (233 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_233 :
    recurrence4Scalar2Exceptional.coeff 233 =
      -(((((15574308752676827668540361 * 10 ^ 70 +
        3441537999597883625893152211516466072860556023320972249721978350668007) * 10 ^ 70 +
        0014551919721837718535137347069301362576512425182478520954804675326596) * 10 ^ 70 +
        1895613833953198276802002380319251306555666918775082290348379812962491) * 10 ^ 70 +
        6431144099491251532579308759936579270693028670560834445595996102454909) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (233 - x)) = _
  rw [show 234 = 88 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (234 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_234 :
    recurrence4Scalar2Exceptional.coeff 234 =
      (((((20948709325902767128726560 * 10 ^ 70 +
        7799614186527536150657962200478042234439195184140573373140572255635686) * 10 ^ 70 +
        2931802260099558610888484254997171633441005835936215861146434585284678) * 10 ^ 70 +
        4205489814931132132296857540710945103773862749840530839052197210558771) * 10 ^ 70 +
        4383834720822492155626325650016597856199254210015336511193899905737089) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (234 - x)) = _
  rw [show 235 = 89 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (235 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_235 :
    recurrence4Scalar2Exceptional.coeff 235 =
      -(((((27803874435379632183169322 * 10 ^ 70 +
        9823567856750013603593715121033542569794678768908349416397145899463961) * 10 ^ 70 +
        9511378838204211445936278615018175449468954979626084719556495334566361) * 10 ^ 70 +
        1937054968973527779910285229550206825677479725123649771963533686292477) * 10 ^ 70 +
        2806440548901610743100220090704449297796163138246233790966383798511799) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (235 - x)) = _
  rw [show 236 = 90 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (236 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_236 :
    recurrence4Scalar2Exceptional.coeff 236 =
      (((((36413321833248289554624215 * 10 ^ 70 +
        0739743459554657343016182377607110687618134081059713762948537868279717) * 10 ^ 70 +
        8472986645990198265273688435928220970670158862985794209396407482028829) * 10 ^ 70 +
        9601044508999596879829945857704044798378608827282004085564755388364984) * 10 ^ 70 +
        4241712505320053936525127683337154184664399634636894213112490777055469) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (236 - x)) = _
  rw [show 237 = 91 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (237 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_237 :
    recurrence4Scalar2Exceptional.coeff 237 =
      -(((((47057536717013548577487184 * 10 ^ 70 +
        7953922869949233319155703286930292104538301878472325535787969002688519) * 10 ^ 70 +
        0713872663225633683659016468172430724175969310932672016361742620539173) * 10 ^ 70 +
        5792434469070024408962322846306715620391983044160272256506833750996120) * 10 ^ 70 +
        4950755765632044447662884282740299653734463124786562991225513539906069) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (237 - x)) = _
  rw [show 238 = 92 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (238 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_238 :
    recurrence4Scalar2Exceptional.coeff 238 =
      (((((60009300811249691118037962 * 10 ^ 70 +
        6614063761357998152589196211261386268921953314608529983247150404922859) * 10 ^ 70 +
        4741385534167040006078393070807511288582909135559045784623579196634619) * 10 ^ 70 +
        3834403702087123980934793234730287194152649418007913543009593367062955) * 10 ^ 70 +
        4802442651474437007894420870140989436951103983589315037601582856638836) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (238 - x)) = _
  rw [show 239 = 93 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (239 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_239 :
    recurrence4Scalar2Exceptional.coeff 239 =
      -(((((75515240684880677044305051 * 10 ^ 70 +
        9214959957690899642065681349563598426827699965248626247499312714444915) * 10 ^ 70 +
        0013731052817412621440206577270802796559276631327090156634374671987058) * 10 ^ 70 +
        4153593889340434538722756566296208531541117420994482403462996908723674) * 10 ^ 70 +
        0141916600754176388184696531740559423504838715854095157267564583629447) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (239 - x)) = _
  rw [show 240 = 94 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (240 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_240 :
    recurrence4Scalar2Exceptional.coeff 240 =
      (((((93774143592370659587776769 * 10 ^ 70 +
        3406413474492514523493409040789599108428223637025549232121552732626422) * 10 ^ 70 +
        6083328697825902445037660704176377976288481200854647791683230244108617) * 10 ^ 70 +
        3478807730255516656179423472183367523292724215578724369317003531580388) * 10 ^ 70 +
        7825095905964024997064101791693690273954751836549342488809159160647453) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (240 - x)) = _
  rw [show 241 = 95 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (241 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_241 :
    recurrence4Scalar2Exceptional.coeff 241 =
      -(((((114913073522818875932132581 * 10 ^ 70 +
        6457480240214031816420606958489575891828255944945152835358427192828315) * 10 ^ 70 +
        4126339832486481439306403637678070751750926029438204963856102085290573) * 10 ^ 70 +
        3840921779380361772811626596638080060635494065783929440756668490060647) * 10 ^ 70 +
        7145177294408136570809136844527161017884140209515575401006880047904952) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (241 - x)) = _
  rw [show 242 = 96 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (242 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_242 :
    recurrence4Scalar2Exceptional.coeff 242 =
      (((((138962814566668026821012467 * 10 ^ 70 +
        9146482401004719838725999587672120959635600330624299020510079886218775) * 10 ^ 70 +
        4001662108878239368008281708011013498946584513689187617693223844026487) * 10 ^ 70 +
        5890426560553136852257496221092335865192386403898607143106732202651127) * 10 ^ 70 +
        7699953099807080182896399321158075489835726887615561868946230600961186) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (242 - x)) = _
  rw [show 243 = 97 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (243 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_243 :
    recurrence4Scalar2Exceptional.coeff 243 =
      -(((((165834611401488875129980883 * 10 ^ 70 +
        3323759343329349700038965878618805668307346748358121459959765906705171) * 10 ^ 70 +
        6563580389515980110989019458365133464501528525174969409403222436567418) * 10 ^ 70 +
        4484989073288395731704284212007231964027609862163559180887371689404142) * 10 ^ 70 +
        1346404522494799571150979855176383862808541672232372399669543805900461) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (243 - x)) = _
  rw [show 244 = 98 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (244 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_244 :
    recurrence4Scalar2Exceptional.coeff 244 =
      (((((195300497806880491293336980 * 10 ^ 70 +
        1864504207936004981555868375971657588526178064626631388539773315049455) * 10 ^ 70 +
        9545199463582641310764012450833502669099668468380575803109109897209101) * 10 ^ 70 +
        6211943747375123603577536738916138399975565889554939198936007974485264) * 10 ^ 70 +
        6572706852524427056361646411894925683278662998523107976139745978257726) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (244 - x)) = _
  rw [show 245 = 99 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (245 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_245 :
    recurrence4Scalar2Exceptional.coeff 245 =
      -(((((226979634715608654657781807 * 10 ^ 70 +
        0247996774196612979927167166375317965113048616475546249195681509586662) * 10 ^ 70 +
        2936156271517685081975296135045637541571992813135376612595405884548883) * 10 ^ 70 +
        6925296135028393915059594566293691124961203286332080724834800657570759) * 10 ^ 70 +
        8987396419010754414812834328405603994162524448772987451215712200818634) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (245 - x)) = _
  rw [show 246 = 100 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (246 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_246 :
    recurrence4Scalar2Exceptional.coeff 246 =
      (((((260332962341674938099902774 * 10 ^ 70 +
        2199979930567249973384455834303098406829174512974818225457100530627168) * 10 ^ 70 +
        7536919243261134406628569102875479640775572466644229935069435814638829) * 10 ^ 70 +
        3518550823142464263785395988460673920202686486879443738986533741585139) * 10 ^ 70 +
        5590235296362925366404204671219166353808075392399466215864902649108740) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (246 - x)) = _
  rw [show 247 = 101 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (247 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_247 :
    recurrence4Scalar2Exceptional.coeff 247 =
      -(((((294668072558080403611529222 * 10 ^ 70 +
        7987245919515362655688598557673909269380260071810480734113721164850910) * 10 ^ 70 +
        9578464759320466944274021103187689133862441544545563145643263793197649) * 10 ^ 70 +
        0620068108124797354468051887834012805149720831064743039649163238551309) * 10 ^ 70 +
        9583952232404351104237495032624476995481935372680114445491407149726556) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (247 - x)) = _
  rw [show 248 = 102 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (248 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_248 :
    recurrence4Scalar2Exceptional.coeff 248 =
      (((((329155527042066704491397522 * 10 ^ 70 +
        1101934701113252805181918651314842109063829185174939682100242955619727) * 10 ^ 70 +
        5018139788581795533689030988639744850015677996716088874531956099159737) * 10 ^ 70 +
        4440502192438949318783434876421803539322082705045555076703823639501993) * 10 ^ 70 +
        1231428224159768353363775692036912615637158758497400261888516258199596) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (248 - x)) = _
  rw [show 249 = 103 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (249 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_249 :
    recurrence4Scalar2Exceptional.coeff 249 =
      -(((((362856921899959854129416038 * 10 ^ 70 +
        6047258936857412879819169024389572277567268208882541538365575236785137) * 10 ^ 70 +
        4304186065315239644425301225715987544686693442377418680989018922839561) * 10 ^ 70 +
        1016768950197006575296760300381447248167871560749297890011291181673521) * 10 ^ 70 +
        2582790849572275569019382754858705442431133882752063938594925427904989) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (249 - x)) = _
  rw [show 250 = 104 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (250 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_250 :
    recurrence4Scalar2Exceptional.coeff 250 =
      (((((394763908340588738800164739 * 10 ^ 70 +
        1711993788578182450411671667548583389831366843413009263075183845516353) * 10 ^ 70 +
        1066655661142364976240157181783286952883106588654233087071637076090769) * 10 ^ 70 +
        7760915803829541504343792893482130723461556389609691785825787855981992) * 10 ^ 70 +
        0027327560968595623689934507102140233631452018226550225864308409863402) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (250 - x)) = _
  rw [show 251 = 105 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (251 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_251 :
    recurrence4Scalar2Exceptional.coeff 251 =
      -(((((423846233210788953136904877 * 10 ^ 70 +
        9713772190779101537927806670210962056734549642253026955783121068275552) * 10 ^ 70 +
        8037862315209024469851923032754770738175946537935447475667512764136666) * 10 ^ 70 +
        7911279366855820695071450359836257433254477214633901102178612450912507) * 10 ^ 70 +
        5325824948734886821771314833513900201337747198607258763408420159312622) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (251 - x)) = _
  rw [show 252 = 106 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (252 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_252 :
    recurrence4Scalar2Exceptional.coeff 252 =
      (((((449105796353325438692926464 * 10 ^ 70 +
        6957833559452221778956020074486109934788308429288419157201372708451502) * 10 ^ 70 +
        5817578189642359524285951242436598096200844171955306803348552435919013) * 10 ^ 70 +
        5224717224466839157727964217890141055477729360006000712778905748525746) * 10 ^ 70 +
        0291275668581520676907083106409712195560207932728505842931317411320099) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (252 - x)) = _
  rw [show 253 = 107 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (253 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_253 :
    recurrence4Scalar2Exceptional.coeff 253 =
      -(((((469632871894879271767680029 * 10 ^ 70 +
        1476451980358587050704355344391369923456110788577669183654457166955211) * 10 ^ 70 +
        4873525480674402951129206939940138841962889304245640840897354528611958) * 10 ^ 70 +
        5953673858429858900912634007936827263839667306451399674239330440195562) * 10 ^ 70 +
        9448240006145651448361788675489928450537414534218000057592294857762772) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (253 - x)) = _
  rw [show 254 = 108 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (254 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_254 :
    recurrence4Scalar2Exceptional.coeff 254 =
      (((((484660130505135699598332853 * 10 ^ 70 +
        7670930887783143638789111430225113138908763560183803663928840062421640) * 10 ^ 70 +
        4418436178611530332863573554150486080645119265528500861825209117930979) * 10 ^ 70 +
        7836523831163155618936595293779715221131086786545593791284330382100899) * 10 ^ 70 +
        2826351119376214609103748530126038076696339542763176624628914842733949) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (254 - x)) = _
  rw [show 255 = 109 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (255 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_255 :
    recurrence4Scalar2Exceptional.coeff 255 =
      -(((((493610017439169838876313812 * 10 ^ 70 +
        6491310553281965919360058100810914081803967004657815214411873724883075) * 10 ^ 70 +
        4801186834976557855578393945141872971471167990997546239535822141961882) * 10 ^ 70 +
        2399232808608326283565973976408707158278976434830590502104864016710046) * 10 ^ 70 +
        4933538495643000414755609159824874175798515235321008040162353286692850) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (255 - x)) = _
  rw [show 256 = 110 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (256 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_256 :
    recurrence4Scalar2Exceptional.coeff 256 =
      (((((496131424545306301640827354 * 10 ^ 70 +
        0947329730636294789712490747130606227405866978937211201134883734077537) * 10 ^ 70 +
        0408021180557565693302367781353424542149405208421299022422044941580230) * 10 ^ 70 +
        6287366181160981202875689452151147876888210848093186510964659258429681) * 10 ^ 70 +
        2304145565061079781262625732862929391025218936531983334322894678206903) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (256 - x)) = _
  rw [show 257 = 111 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (257 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_257 :
    recurrence4Scalar2Exceptional.coeff 257 =
      -(((((492122422132073171829934586 * 10 ^ 70 +
        7311136033317074072115704496491827508392688988595341370289918310527442) * 10 ^ 70 +
        9511695162387466045958740079588906729289268631222475419866092539098794) * 10 ^ 70 +
        6970062095125000619185302798897333145400896163385328169561272360099278) * 10 ^ 70 +
        9570423263588409064055256174624180635641474183352391962833187903291289) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (257 - x)) = _
  rw [show 258 = 112 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (258 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_258 :
    recurrence4Scalar2Exceptional.coeff 258 =
      (((((481737008390248269546727181 * 10 ^ 70 +
        5814116055270069829531273904880869332421365449201031774742415153317900) * 10 ^ 70 +
        5974583636060706577843146463721647382524181454416512592057215849853447) * 10 ^ 70 +
        5630363368472115928819710431370584637312257807836238494778342062874059) * 10 ^ 70 +
        8336789044179424045993680916019415228253900528851730105620734660010487) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (258 - x)) = _
  rw [show 259 = 113 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (259 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_259 :
    recurrence4Scalar2Exceptional.coeff 259 =
      -(((((465375259935570201952748577 * 10 ^ 70 +
        0866680741230062106170003561615253839317794145458148234231096833022275) * 10 ^ 70 +
        2162500869386409824774126588945990071386829393072745683378910315309066) * 10 ^ 70 +
        1446306827584462065199771357428091007103114483574782293378919359974612) * 10 ^ 70 +
        0694452076582129547873420697666102954897635403122278219968387410059155) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (259 - x)) = _
  rw [show 260 = 114 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (260 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_260 :
    recurrence4Scalar2Exceptional.coeff 260 =
      (((((443657764390996784407039279 * 10 ^ 70 +
        0895267023184150947313786353347922697508402223402331632250549296594327) * 10 ^ 70 +
        8294000611444571635421501435524866513927778902895970716150919430062950) * 10 ^ 70 +
        7294855823491270625453920746123919361914159571050522758755580559631296) * 10 ^ 70 +
        1121903679756029667858406395392634035358537819845696996395082047196884) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (260 - x)) = _
  rw [show 261 = 115 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (261 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_261 :
    recurrence4Scalar2Exceptional.coeff 261 =
      -(((((417386612154047017388407031 * 10 ^ 70 +
        1736747552211761488276949768409427044893671808312993991246869569238571) * 10 ^ 70 +
        9737681939601216002504768733081206778083662692400655834900009464807026) * 10 ^ 70 +
        0005064068889566753888937498783753643173879116909429819181746771714911) * 10 ^ 70 +
        7760946096768048372557360460775050340357574464507630451926252038024965) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (261 - x)) = _
  rw [show 262 = 116 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (262 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_262 :
    recurrence4Scalar2Exceptional.coeff 262 =
      (((((387496361138326423823488401 * 10 ^ 70 +
        6165250536610636739814961258764052340988306299027172137248093132357463) * 10 ^ 70 +
        0362461586839407724052813256895230792782774917869543721931907782501834) * 10 ^ 70 +
        7119624747124270550068630874809155846293880654107519699527610572663075) * 10 ^ 70 +
        7699324905640113808255513147039169378510059549521843523107430481266786) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (262 - x)) = _
  rw [show 263 = 117 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (263 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_263 :
    recurrence4Scalar2Exceptional.coeff 263 =
      -(((((354999142883696201161283622 * 10 ^ 70 +
        4892262132190669739092709156975551055797021154202018691343143330089619) * 10 ^ 70 +
        0384595303704470032534825273859528371685951427015368899025866867072542) * 10 ^ 70 +
        1047689671677708269733134817786493036685394129049145306156759707145553) * 10 ^ 70 +
        8030870655722692201039487516423535779939585560027781579902888508349855) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (263 - x)) = _
  rw [show 264 = 118 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (264 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_264 :
    recurrence4Scalar2Exceptional.coeff 264 =
      (((((320928380517225327259707632 * 10 ^ 70 +
        1995907921722362899462500913589336086610097282123046849063199405828927) * 10 ^ 70 +
        6584583584015362703977197045769453201295953844328620262630432519744791) * 10 ^ 70 +
        5737827623493162778371772632995014473065020023537788579144296697339000) * 10 ^ 70 +
        3680733579988688758817090654692110422406839803466562030244759373104796) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (264 - x)) = _
  rw [show 265 = 119 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (265 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_265 :
    recurrence4Scalar2Exceptional.coeff 265 =
      -(((((286285427775088040367578170 * 10 ^ 70 +
        1885002566909337318781296148974176754628904206273596336735856071641490) * 10 ^ 70 +
        9510959612975715676835285305810984889352816178606336584636935629834501) * 10 ^ 70 +
        5721689255120812449680583739952780654250086295303542064205831163723311) * 10 ^ 70 +
        4749961262206740640066015141884343707968532702903231066453945535278653) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (265 - x)) = _
  rw [show 266 = 120 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (266 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_266 :
    recurrence4Scalar2Exceptional.coeff 266 =
      (((((251992860895282542226455731 * 10 ^ 70 +
        7537546485807382190099034327934219426532648029810262816881836418300529) * 10 ^ 70 +
        1621110804377863740786691163578920207106283037487141970915291295334140) * 10 ^ 70 +
        2393747674561354787698889801899876355803280080761601376030672575548893) * 10 ^ 70 +
        4680464234578174904880620941725758729184815152286051545083162385988770) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (266 - x)) = _
  rw [show 267 = 121 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (267 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_267 :
    recurrence4Scalar2Exceptional.coeff 267 =
      -(((((218857256898969861576888979 * 10 ^ 70 +
        1306676871525344621439110504367213844000689613124286531199519281930826) * 10 ^ 70 +
        5085392989921687009379860610392461422424379576650180585480488274925521) * 10 ^ 70 +
        1187622832684015122046790927943010875831266990939917121975488159949991) * 10 ^ 70 +
        4705751695547125538949136222838496967412595566109434487076556821056045) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (267 - x)) = _
  rw [show 268 = 122 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (268 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_268 :
    recurrence4Scalar2Exceptional.coeff 268 =
      (((((187543199405287443526123988 * 10 ^ 70 +
        4180164117004992710276122969568579039194877672677904765225367768509522) * 10 ^ 70 +
        3369564581827395909929510066515075001815014793614426717393433371899335) * 10 ^ 70 +
        9197263039193431687572209616234426307282847566179722922335921742208652) * 10 ^ 70 +
        4771264253659364912681866795975033668412119936636257397188504964102805) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (268 - x)) = _
  rw [show 269 = 123 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (269 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_269 :
    recurrence4Scalar2Exceptional.coeff 269 =
      -(((((158559105341861245242563558 * 10 ^ 70 +
        0292297709024903974078670984576573385105925534115570213301930743819579) * 10 ^ 70 +
        2027446527015836634583794403974150771564039034745703891422037753358939) * 10 ^ 70 +
        6122854757562160528998386384121741828051306579053869839453812784238011) * 10 ^ 70 +
        7806165984229618344557682206821266803515905560846793097119830563909653) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (269 - x)) = _
  rw [show 270 = 124 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_269_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (270 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_270 :
    recurrence4Scalar2Exceptional.coeff 270 =
      (((((132254393641857938247049281 * 10 ^ 70 +
        0523980196159034455349258807177557414658507916634239243757883757201889) * 10 ^ 70 +
        0365071563544325608864296618954587363497546078015448265566247665302931) * 10 ^ 70 +
        5391792873001082510706756850852009582136748819697776347697723678093654) * 10 ^ 70 +
        2459951019771588501733549515816947669364656861696609427314836089086161) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (270 - x)) = _
  rw [show 271 = 125 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_270_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (271 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_271 :
    recurrence4Scalar2Exceptional.coeff 271 =
      -(((((108826626978262168356525736 * 10 ^ 70 +
        2683574961002739414590917416963352400128443475515534901885267789894573) * 10 ^ 70 +
        8014136056799526085334986213835250454782187716436175161658869684515498) * 10 ^ 70 +
        5665993485326263952498625954915880472934653420487304155030942347651044) * 10 ^ 70 +
        9737754724687910494677424790695991114031887251980655837494014025569688) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (271 - x)) = _
  rw [show 272 = 126 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_271_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (272 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_272 :
    recurrence4Scalar2Exceptional.coeff 272 =
      (((((88336621214306093336536410 * 10 ^ 70 +
        7551118984354246063716381709972324796317744220098778862798378742989560) * 10 ^ 70 +
        1911328899375779513167736399825019613077321255383556922575673354722375) * 10 ^ 70 +
        9798795129097760095248060171275887541853365472770006047430516985505395) * 10 ^ 70 +
        1723496808784292697095599918114927587738366080490042144771351708680458) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (272 - x)) = _
  rw [show 273 = 127 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_272_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (273 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_273 :
    recurrence4Scalar2Exceptional.coeff 273 =
      -(((((70729166047772119026580784 * 10 ^ 70 +
        7469236413880561096310533761684067718681946403777257333498415396263446) * 10 ^ 70 +
        8557674342607323831145971228581373515114250597520075816691144649716849) * 10 ^ 70 +
        6285010667567045475039042215931880076501060533746407804387667809354592) * 10 ^ 70 +
        5402173147300059800268435668775338284687279964700291926499230857413944) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (273 - x)) = _
  rw [show 274 = 128 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_273_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (274 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_274 :
    recurrence4Scalar2Exceptional.coeff 274 =
      (((((55856927504074519019113467 * 10 ^ 70 +
        3933137691440523410793954221287242377874789587637857064471233099014065) * 10 ^ 70 +
        5719648086430167590070095171758909260313719966951361305363165326403641) * 10 ^ 70 +
        6914513837813457243822357160959960392960106566331114353889090299060838) * 10 ^ 70 +
        3277835272479012723038576166630614732057999846896505002773351725986298) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (274 - x)) = _
  rw [show 275 = 129 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_274_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (275 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_275 :
    recurrence4Scalar2Exceptional.coeff 275 =
      -(((((43505270183923502003579291 * 10 ^ 70 +
        7621957522163996979869391122653035846033036999788222297905224374100182) * 10 ^ 70 +
        5186190481059838692682643849652324204587452676737003955465346197887387) * 10 ^ 70 +
        4920624849762203740880954051329678949861257110791555061149390415588036) * 10 ^ 70 +
        7361551397803776505722376767824170057424600501942518634706422743281840) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (275 - x)) = _
  rw [show 276 = 130 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_275_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (276 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_276 :
    recurrence4Scalar2Exceptional.coeff 276 =
      (((((33416084781724029164470674 * 10 ^ 70 +
        7836972923892988486510514123534661040314276078679995556757075755965282) * 10 ^ 70 +
        5481873325223881924843234476925324999974502627297639845395642497020345) * 10 ^ 70 +
        2126256051414267273258852878527217446516015552126056269272510184977946) * 10 ^ 70 +
        7406969922891049379426240570666662980250079614573618049265944131923270) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (276 - x)) = _
  rw [show 277 = 131 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_276_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (277 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_277 :
    recurrence4Scalar2Exceptional.coeff 277 =
      -(((((25309164592429824664660854 * 10 ^ 70 +
        4273420751895883268101457889297284939665617530369323941333075056809392) * 10 ^ 70 +
        5628412245765775873840928185142680290665935009146825630230605025510622) * 10 ^ 70 +
        5491317241303040354640968987614710061110868370805053059203393041676879) * 10 ^ 70 +
        7264982994088096559602276880404893467814167303283778736178948563054971) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (277 - x)) = _
  rw [show 278 = 132 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_277_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (278 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_278 :
    recurrence4Scalar2Exceptional.coeff 278 =
      (((((18900174385107635408901847 * 10 ^ 70 +
        7527872438784745438700992454583027376174229389059871089141623078364254) * 10 ^ 70 +
        2498647660065612431094693163859093917109713793101565662877484321057475) * 10 ^ 70 +
        9574425959671491304058706859554086685254150774698026100405399659654903) * 10 ^ 70 +
        6582592831312975947672634810043996802645432923451755167943957336587096) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (278 - x)) = _
  rw [show 279 = 133 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_278_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (279 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_279 :
    recurrence4Scalar2Exceptional.coeff 279 =
      -(((((13914736204008382473396516 * 10 ^ 70 +
        5797470439656875900157759467275742447541208526982402005264382929114020) * 10 ^ 70 +
        2049897129893540096322925852836051291312290749321125193683618937996003) * 10 ^ 70 +
        5863790332828181403421730000289165572068120246636088801445411545825707) * 10 ^ 70 +
        1751282077912458413375697526346433735456883072694406769397023455861259) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (279 - x)) = _
  rw [show 280 = 134 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_279_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (280 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_280 :
    recurrence4Scalar2Exceptional.coeff 280 =
      (((((10098574203744825857941203 * 10 ^ 70 +
        5122725375088564685063019210787201492381849687258752493213375080717474) * 10 ^ 70 +
        2777004971277715059009584798361236493985777017908947837673938175982829) * 10 ^ 70 +
        0419934993978976986259995197772060468413829614965865764155066074771105) * 10 ^ 70 +
        4518079735543513055528430062610410707829875215682567516335377527142566) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (280 - x)) = _
  rw [show 281 = 135 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_280_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (281 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_281 :
    recurrence4Scalar2Exceptional.coeff 281 =
      -(((((7223986555610747853372565 * 10 ^ 70 +
        5533165161410362529135675091104327766113718960817564956800750403137805) * 10 ^ 70 +
        4157034243489024561548720597682974601029147091834338040740286268553947) * 10 ^ 70 +
        8508566516470621455460467768409402808502662801707614583135763209087595) * 10 ^ 70 +
        6027696519659419037937994545705308588922576484849394782785734139643803) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (281 - x)) = _
  rw [show 282 = 136 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_281_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (282 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_282 :
    recurrence4Scalar2Exceptional.coeff 282 =
      (((((5093135538106177167115766 * 10 ^ 70 +
        3904586370361990749994461066674315328582926123233591265054890201699695) * 10 ^ 70 +
        1916397587853078231479571282317428677070789558296343054087899982548275) * 10 ^ 70 +
        6744804569770112416020697544472452189311480216977047966302555585787805) * 10 ^ 70 +
        3923054948247980756796606082513493496090119319835606309964696349704538) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (282 - x)) = _
  rw [show 283 = 137 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_282_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (283 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_283 :
    recurrence4Scalar2Exceptional.coeff 283 =
      -(((((3538770071361602895536661 * 10 ^ 70 +
        7956125025519755917326049849582420049041831523028759189026453912480197) * 10 ^ 70 +
        9178550604316173396077130792777882260853450020825794403028430334265519) * 10 ^ 70 +
        3564804940594976471354144212734417209546800381685271951618606811182583) * 10 ^ 70 +
        9526775122479426013105679812876700688705802324110098719835691075940063) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (283 - x)) = _
  rw [show 284 = 138 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_283_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (284 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_284 :
    recurrence4Scalar2Exceptional.coeff 284 =
      (((((2423031425778024001633313 * 10 ^ 70 +
        1880600250296569384715172562978055146340227488222967228213762891654016) * 10 ^ 70 +
        7634534499664920998783117341642592346457349629263631138640383865928593) * 10 ^ 70 +
        2934050509992619143799275704063218748886553034849484366702881428232050) * 10 ^ 70 +
        2205892193789000667049684973840560824901590667611806586984837537320072) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (284 - x)) = _
  rw [show 285 = 139 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_284_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (285 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_285 :
    recurrence4Scalar2Exceptional.coeff 285 =
      -(((((1634961974009705919604250 * 10 ^ 70 +
        0276182048208358746762759053994686728043922790565132235647852061332905) * 10 ^ 70 +
        3482469663949180491105781540478536913447633177384176843041664801939734) * 10 ^ 70 +
        8506970397455721519688220568664285964234320042720755458925589290989870) * 10 ^ 70 +
        6276081064451628576059943575716342745235480591564572074019000098921258) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (285 - x)) = _
  rw [show 286 = 140 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_285_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (286 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_286 :
    recurrence4Scalar2Exceptional.coeff 286 =
      (((((1087260162403353666111290 * 10 ^ 70 +
        2136755830544812437111296677100678943665086924915988383745784316115583) * 10 ^ 70 +
        0822919827941464006182538258891701204804514000056026886827678114451759) * 10 ^ 70 +
        6164291794396705312934683070241215851138884451263738160130466568413705) * 10 ^ 70 +
        0196482611143881027031254455738855474108401815795035895705214319106852) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (286 - x)) = _
  rw [show 287 = 141 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_286_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (287 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_287 :
    recurrence4Scalar2Exceptional.coeff 287 =
      -(((((712722851809740500562659 * 10 ^ 70 +
        6870476302192944744640240919755936637430493255279123772880463493918709) * 10 ^ 70 +
        5576063751218756047278963107951733082847435677386463693977677766685587) * 10 ^ 70 +
        0251740038706567647065004347030303258970952041424170641814434374646107) * 10 ^ 70 +
        3007515105067546734362372668303959246514999002017255895197516592229109) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (287 - x)) = _
  rw [show 288 = 142 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_287_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (288 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_288 :
    recurrence4Scalar2Exceptional.coeff 288 =
      (((((460706165949299482585558 * 10 ^ 70 +
        8110850037480100590654581632720482817071310375600924907126197334093610) * 10 ^ 70 +
        4114498314166736590782897393460942828390311050539211441189385932706460) * 10 ^ 70 +
        2832874313687250271606524230602976631914225679393421325977581865613500) * 10 ^ 70 +
        8472797507346634427090469594951981343216718621973719292226273502331068) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (288 - x)) = _
  rw [show 289 = 143 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_288_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (289 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_289 :
    recurrence4Scalar2Exceptional.coeff 289 =
      -(((((293831057260146508566715 * 10 ^ 70 +
        7181257736573563593950932004146728281445382582359398986000519499372403) * 10 ^ 70 +
        2389737606130961972880784359548231720202861376519903910692069471713008) * 10 ^ 70 +
        3760750193883346273651404145241273523670893003448978988973193497699436) * 10 ^ 70 +
        5091539993784785955225729400479679460660980965151140453914194514937156) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (289 - x)) = _
  rw [show 290 = 144 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_289_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (290 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_290 :
    recurrence4Scalar2Exceptional.coeff 290 =
      (((((185068498113986787578300 * 10 ^ 70 +
        1019253904106626178881781264763438450992631592730161606635948305539613) * 10 ^ 70 +
        1788399922911102727620879566342265102716520426332104468480333825520776) * 10 ^ 70 +
        8660092221506207306552101980910443765842744409097966751563225582397424) * 10 ^ 70 +
        9107075332596127764692029330485313869575943293005867628740180950396757) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (290 - x)) = _
  rw [show 291 = 145 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (291 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_291 :
    recurrence4Scalar2Exceptional.coeff 291 =
      -(((((115265947990892450901649 * 10 ^ 70 +
        8070822447081500340170643931169260841310838233532267379134161858782789) * 10 ^ 70 +
        3921912703063942380980509335067970554947862880242059818334705824367838) * 10 ^ 70 +
        1901341247493105771083016860578890225728118480082852410364672295017325) * 10 ^ 70 +
        7562920615032341577846896920358487232908023120525036571616981845433226) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (291 - x)) = _
  rw [show 292 = 146 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_291_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (292 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_292 :
    recurrence4Scalar2Exceptional.coeff 292 =
      (((((71122625324343700067315 * 10 ^ 70 +
        0935333897336316624343466256907495101034389675323631495794473141777205) * 10 ^ 70 +
        2561212121899906125000597546256869596684471945304998432642294159402164) * 10 ^ 70 +
        8948489669793048071628535629597670653534684317295495735768822822087477) * 10 ^ 70 +
        2088332509864178769501743724801840471860803111447893769966292576467541) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (292 - x)) = _
  rw [show 293 = 147 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_292_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (293 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_293 :
    recurrence4Scalar2Exceptional.coeff 293 =
      -(((((43584846588552915522463 * 10 ^ 70 +
        5944216242716590526924597884539372005828350800429842885171951104487487) * 10 ^ 70 +
        2972953638765886678446418427781168668160863029921075003578543175360784) * 10 ^ 70 +
        4901666020927595051065222097474971593506704430153543049359133987313842) * 10 ^ 70 +
        7437370081003463985558205424481182987101301459497717487470181804599614) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (293 - x)) = _
  rw [show 294 = 148 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_293_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (294 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_294 :
    recurrence4Scalar2Exceptional.coeff 294 =
      (((((26611572118443861950955 * 10 ^ 70 +
        7198363264416203324163841389408544555465097720588304144894687193475496) * 10 ^ 70 +
        5871163858402434957744952991811511143449663552062038924102010351995513) * 10 ^ 70 +
        4635357499889455523080297684044763001013937589618514903635585953907443) * 10 ^ 70 +
        3469098038592627021136823339888150921157056010035570890437658516060883) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (294 - x)) = _
  rw [show 295 = 149 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_294_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (295 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_295 :
    recurrence4Scalar2Exceptional.coeff 295 =
      -(((((16250970911328700141624 * 10 ^ 70 +
        1388609256923794970013769425887483342756574438598188963956791917802657) * 10 ^ 70 +
        1937293270251830678267962686535397500717449972976769436047853443947274) * 10 ^ 70 +
        9129919721379784560607242270755975043772396297658271618197965030914361) * 10 ^ 70 +
        9479784519513133785870436431805973484901155972286315271690779428127728) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (295 - x)) = _
  rw [show 296 = 150 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_295_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (296 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_296 :
    recurrence4Scalar2Exceptional.coeff 296 =
      (((((9967904393954896299253 * 10 ^ 70 +
        2959394977635999125640639460346130957383285068826011912201045754392169) * 10 ^ 70 +
        8925408042555431555388733647133910692410503157423802975619919040233316) * 10 ^ 70 +
        0470490230846323768982735292799233566448220712051121903485467529552681) * 10 ^ 70 +
        7225683258389471529088887666848529829371152064760099712913129901622031) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (296 - x)) = _
  rw [show 297 = 151 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_296_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (297 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_297 :
    recurrence4Scalar2Exceptional.coeff 297 =
      -(((((6166710259217662109898 * 10 ^ 70 +
        7448220809683293731045362452962204736053909655197778118436270164001840) * 10 ^ 70 +
        2333811688329398717394064143764689009508012809564719603155779846445990) * 10 ^ 70 +
        5074486932181028403536360928754911267881022537485786275185858570908357) * 10 ^ 70 +
        5637944345424758978428391778075543115077290534184290555890973028532214) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (297 - x)) = _
  rw [show 298 = 152 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_297_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (298 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_298 :
    recurrence4Scalar2Exceptional.coeff 298 =
      (((((3861087224828047436161 * 10 ^ 70 +
        7590793076796925424267786185337242579558758114521931369829035443877476) * 10 ^ 70 +
        1885041871152393847623716567307559428724765858352223659019322968815894) * 10 ^ 70 +
        9289402857893879334752844715477851655534286534215651870850268679815503) * 10 ^ 70 +
        0580235103051418198656788975927959805225224489217444003286290922530240) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (298 - x)) = _
  rw [show 299 = 153 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_298_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (299 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_299 :
    recurrence4Scalar2Exceptional.coeff 299 =
      -(((((2451414611052265757353 * 10 ^ 70 +
        6873562917849703546753213184400344651858300811256704965418601374803697) * 10 ^ 70 +
        1513233879755095753178490310474888859921524362873432169525406789369597) * 10 ^ 70 +
        6610254692040563051175233291809125303623494783579596302915361484591429) * 10 ^ 70 +
        9359650850717259457481283111123006585341978853786652572356497553987257) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (299 - x)) = _
  rw [show 300 = 154 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_299_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (300 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_300 :
    recurrence4Scalar2Exceptional.coeff 300 =
      (((((1578254412310598391124 * 10 ^ 70 +
        8117759154624282185247236454694011940826262955259962488263603961070343) * 10 ^ 70 +
        2178184042898619816409707501687066947515994067023007440389339959919476) * 10 ^ 70 +
        2216367393731117678144231526793536816148757329214947334642737415630707) * 10 ^ 70 +
        6368304317515571722206577818555573725133787769075268011932611456274312) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (300 - x)) = _
  rw [show 301 = 155 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_300_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (301 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_301 :
    recurrence4Scalar2Exceptional.coeff 301 =
      -(((((1028344613835756183287 * 10 ^ 70 +
        4198778427389605722954281225080567428577228467251398050134793709254316) * 10 ^ 70 +
        4867392669318903297959311950151801693975227463564095423857296921352059) * 10 ^ 70 +
        9120202104534440895148245014439709548451467448476396749536422079319517) * 10 ^ 70 +
        5254138517966057881475877235143911228393997842932199326233227397782739) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (301 - x)) = _
  rw [show 302 = 156 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_301_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (302 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_302 :
    recurrence4Scalar2Exceptional.coeff 302 =
      (((((675749927215207754256 * 10 ^ 70 +
        8371158703035032405497644973258846914815693131163699657781771630923934) * 10 ^ 70 +
        1985180439381799885800457746306749116659342912782065294578631106610174) * 10 ^ 70 +
        1994553597117267552900999908609272793629484730379925390149265127510785) * 10 ^ 70 +
        4481169713731391443060004596885059583657920564223592870010614898424183) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (302 - x)) = _
  rw [show 303 = 157 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_302_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (303 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_303 :
    recurrence4Scalar2Exceptional.coeff 303 =
      -(((((445905666355811966050 * 10 ^ 70 +
        3334624613110369175568255142477831355709746654131861965710110240507523) * 10 ^ 70 +
        5516828592803553411919249808557847461409807072424756792617833780606849) * 10 ^ 70 +
        0026335072042329687175884946322502289807246242739531354670324775368930) * 10 ^ 70 +
        2560535766189333764728316023254236106620666890786057196727170755386411) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (303 - x)) = _
  rw [show 304 = 158 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_303_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (304 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_304 :
    recurrence4Scalar2Exceptional.coeff 304 =
      (((((294154158394892570367 * 10 ^ 70 +
        2190833397362096286845690706010159130555322722513804583990715632397691) * 10 ^ 70 +
        4098838432665151508662493014941774145052364701402705429923274796183054) * 10 ^ 70 +
        1060269516489824562287053190742031093063091205721085476173038518653552) * 10 ^ 70 +
        0126645805820757605076576449663394126232716933592673536445711482406913) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (304 - x)) = _
  rw [show 305 = 159 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_304_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (305 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_305 :
    recurrence4Scalar2Exceptional.coeff 305 =
      -(((((193200359966625412133 * 10 ^ 70 +
        3093416655748253670450045077191214835654296915040120926437810252820168) * 10 ^ 70 +
        6943078280248758558596932893717628764315267011941540270824455167473930) * 10 ^ 70 +
        9018077566478285691517310931422160435401185333379061350362774146001505) * 10 ^ 70 +
        8874286523728437435729849215622591204532799708340075275857182646873483) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (305 - x)) = _
  rw [show 306 = 160 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_305_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (306 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_306 :
    recurrence4Scalar2Exceptional.coeff 306 =
      (((((125905145740546425687 * 10 ^ 70 +
        0448067131821919069104116981439885229305045428943797596139708906336302) * 10 ^ 70 +
        8765969398874965311028744336512301375289750801192400551035598224081184) * 10 ^ 70 +
        2674741643707561825088624906092889804997064003309918259336512763414721) * 10 ^ 70 +
        5884257715983479618472295312480990582905951893913879138741442051315425) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (306 - x)) = _
  rw [show 307 = 161 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_306_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (307 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_307 :
    recurrence4Scalar2Exceptional.coeff 307 =
      -(((((81187594142168305146 * 10 ^ 70 +
        4691774303775814612299092534604692254866370216867537681654347964554743) * 10 ^ 70 +
        3680893269748389729730305844475451340445926451405800148634389252763257) * 10 ^ 70 +
        9415236315966379014966454999314756366960315152271808480844158784472584) * 10 ^ 70 +
        8848768594893389695042484691972716760932476533064141473650952093936097) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (307 - x)) = _
  rw [show 308 = 162 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_307_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (308 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_308 :
    recurrence4Scalar2Exceptional.coeff 308 =
      (((((51693947250914128471 * 10 ^ 70 +
        3696300231562696948840057012207144171227932273967040412641297347705528) * 10 ^ 70 +
        3336487197353796608010404867679320526923055082518438790446369040853679) * 10 ^ 70 +
        9878728978178843520243957046131309708670723890899100811286309686633975) * 10 ^ 70 +
        7882201888415810680266864193738986740471809555109868525539456997434424) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (308 - x)) = _
  rw [show 309 = 163 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_308_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (309 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_309 :
    recurrence4Scalar2Exceptional.coeff 309 =
      -(((((32450940373636053337 * 10 ^ 70 +
        1008302957627922315213645529126160021012723376577680267214479458617276) * 10 ^ 70 +
        5532367715213677781925831213887299295875739027780929685850536533913360) * 10 ^ 70 +
        9724886271538936999145232680046367606815274660369771488588811356607532) * 10 ^ 70 +
        1748108560040915244196590192612225930856504580445036260793513736674805) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (309 - x)) = _
  rw [show 310 = 164 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_309_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (310 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_310 :
    recurrence4Scalar2Exceptional.coeff 310 =
      (((((20062133488787949376 * 10 ^ 70 +
        4775161328288495081373617623012880204725749690069535949986312166719807) * 10 ^ 70 +
        7833523553592354456353743595133611037046803095398080047107162247249717) * 10 ^ 70 +
        2745916401842285050604208186124412387889785645254493365357202534413908) * 10 ^ 70 +
        6732335151967303608347818619560483615452657500024060846960963055822500) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (310 - x)) = _
  rw [show 311 = 165 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_310_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (311 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_311 :
    recurrence4Scalar2Exceptional.coeff 311 =
      -(((((12205614338639305923 * 10 ^ 70 +
        9263157984038028496941756540247416068274129585577216362065293014125050) * 10 ^ 70 +
        9709804469800441299146459091278011797116305678950511857273814668911036) * 10 ^ 70 +
        9248031634220890416496536529718216544397097367871326879355772997595996) * 10 ^ 70 +
        4946040685442353754219022803574713418349181806442890409857739020439272) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (311 - x)) = _
  rw [show 312 = 166 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_311_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (312 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_312 :
    recurrence4Scalar2Exceptional.coeff 312 =
      (((((7303887389422915860 * 10 ^ 70 +
        5173412016446075695245571295942031813364021014550940376209365809271325) * 10 ^ 70 +
        5834322833392490114035381785558742430023390832646964031267612783574054) * 10 ^ 70 +
        9549910299957704843476798364325809673886270199213527433897272038555673) * 10 ^ 70 +
        1473712649355889292903054746069989148253310186839133316878349933018627) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (312 - x)) = _
  rw [show 313 = 167 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_312_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (313 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_313 :
    recurrence4Scalar2Exceptional.coeff 313 =
      -(((((4297539274229839120 * 10 ^ 70 +
        5199163627314774772682563671554108695613779828344784537341942208863419) * 10 ^ 70 +
        9750201557406262982507012937607190190825255307424539327576890567003399) * 10 ^ 70 +
        2901658011670592436427094098588179042863132546012521695980772248424962) * 10 ^ 70 +
        0790620359245002081335406865957518120233243768486736960551256349041228) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (313 - x)) = _
  rw [show 314 = 168 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_313_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (314 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_314 :
    recurrence4Scalar2Exceptional.coeff 314 =
      (((((2485855815843781484 * 10 ^ 70 +
        7060662728144533427662250580809278992209852462079081842864906279368818) * 10 ^ 70 +
        2988705278682707730509487301900337576490584251620828054256015552370922) * 10 ^ 70 +
        2090751044911030701359441284014387476585516675175631934160003915040852) * 10 ^ 70 +
        7896701255021777152788581489752595077594516063019917602057612304860589) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (314 - x)) = _
  rw [show 315 = 169 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_314_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (315 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_315 :
    recurrence4Scalar2Exceptional.coeff 315 =
      -(((((1413469118864093181 * 10 ^ 70 +
        0115472179311197701283890225366421132034860117815539574271732514125878) * 10 ^ 70 +
        3039750387612619844314829920510707548188853131190507200354342172450340) * 10 ^ 70 +
        3962084693983866584950775000186362652279794385789175146743391548666555) * 10 ^ 70 +
        7569386712057841691481252870167426501869269265993185215008561756724523) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (315 - x)) = _
  rw [show 316 = 170 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_315_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (316 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_316 :
    recurrence4Scalar2Exceptional.coeff 316 =
      (((((790043296847210541 * 10 ^ 70 +
        6770563923017820097422033248822169553036917404700020601385073926265916) * 10 ^ 70 +
        8634155243073068756492097027444984833373168317065319695749696906851966) * 10 ^ 70 +
        4329014052976926989978030833207617264726846957095532269285903739781215) * 10 ^ 70 +
        2571391430369255015076952790688611716092489467580055321508282963041551) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (316 - x)) = _
  rw [show 317 = 171 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_316_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (317 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_317 :
    recurrence4Scalar2Exceptional.coeff 317 =
      -(((((434110537470814736 * 10 ^ 70 +
        2229660549466921834402518647865631440992815649876889075393755549169586) * 10 ^ 70 +
        2301741857967593902081804601923643580146556576154736180594922516673412) * 10 ^ 70 +
        4538121915482283834028468600450590705949779550607174307260022556936506) * 10 ^ 70 +
        2700216730616502528310280056247419193254689007243238937773499961546095) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (317 - x)) = _
  rw [show 318 = 172 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_317_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (318 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_318 :
    recurrence4Scalar2Exceptional.coeff 318 =
      (((((234527926569549222 * 10 ^ 70 +
        9561461392643876893057032366921949912269672598140420824856585748174411) * 10 ^ 70 +
        8792392037272316192899518452797682088547107015999056850213647891146076) * 10 ^ 70 +
        9319024562358982802497655009834894589152706853351358068598980661315414) * 10 ^ 70 +
        9730482022553324934171253005341557255309817462357336630803624265544692) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (318 - x)) = _
  rw [show 319 = 173 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_318_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (319 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_319 :
    recurrence4Scalar2Exceptional.coeff 319 =
      -(((((124601766178319961 * 10 ^ 70 +
        7601366859927073658485880395632899882299890478520894367069929297565438) * 10 ^ 70 +
        6574650307385295230273123788239987468559088348724294429700914644764031) * 10 ^ 70 +
        1876770765514920485600010176217908457875368816332201555445145906706818) * 10 ^ 70 +
        0480109290952812443764703517536011682232449762658960676492965589357848) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (319 - x)) = _
  rw [show 320 = 174 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_319_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (320 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_320 :
    recurrence4Scalar2Exceptional.coeff 320 =
      (((((65120033737911959 * 10 ^ 70 +
        3435411450474553034978794256693327454787614072836136532106948523851630) * 10 ^ 70 +
        3060403467258758064249016989771766115149915527011112300954348039449512) * 10 ^ 70 +
        5193682860585428613822155869564488668177333796310964734407549213607425) * 10 ^ 70 +
        8125339573619501169527032907544213873645471884586377204150180527793461) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (320 - x)) = _
  rw [show 321 = 175 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_320_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (321 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_321 :
    recurrence4Scalar2Exceptional.coeff 321 =
      -(((((33491350289453721 * 10 ^ 70 +
        3290280289521940347646438986262521536624509063644011255695795599313941) * 10 ^ 70 +
        3706423426520110541784948912129235433290847342946961132498740829570823) * 10 ^ 70 +
        0275778358776207530270424708160595091090285903784850824445021679923849) * 10 ^ 70 +
        1071594074971948928596830196430134000746040170073340816061837417106352) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (321 - x)) = _
  rw [show 322 = 176 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_321_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (322 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_322 :
    recurrence4Scalar2Exceptional.coeff 322 =
      (((((16958821104105162 * 10 ^ 70 +
        6304996538612842044983976117589354751822783589276794632582175346632329) * 10 ^ 70 +
        9244728549157779119772159125416176044909676560773854411649565753423069) * 10 ^ 70 +
        0739133640892474295408337708601510011289109234584447799388497002552678) * 10 ^ 70 +
        4688887750931390452098492322858811978668561170039067252388512089219490) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (322 - x)) = _
  rw [show 323 = 177 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_322_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (323 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_323 :
    recurrence4Scalar2Exceptional.coeff 323 =
      -(((((8460238901208915 * 10 ^ 70 +
        1928284025766255514136006066306112562332510445972210076014683185303149) * 10 ^ 70 +
        2119258102745448278184138183031062820841709241414296176026193111208119) * 10 ^ 70 +
        0600521139585513445661260884126204669140457722056673611927942617366391) * 10 ^ 70 +
        9853256210002822800213983348580553735206753281292639651226943972093340) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (323 - x)) = _
  rw [show 324 = 178 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_323_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (324 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_324 :
    recurrence4Scalar2Exceptional.coeff 324 =
      (((((4161471685827704 * 10 ^ 70 +
        3325174223401048844717064117982312653245212620231525671176784232552314) * 10 ^ 70 +
        8166190985064499922017730158574888569808248380681356468010747940079946) * 10 ^ 70 +
        9616802051157211852887036914605926528380477166085561345506206638129406) * 10 ^ 70 +
        8848632508827663453085078393890295060892629243631101567064721580369777) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (324 - x)) = _
  rw [show 325 = 179 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_324_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (325 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_325 :
    recurrence4Scalar2Exceptional.coeff 325 =
      -(((((2020363340272073 * 10 ^ 70 +
        1294339587758342754181221935390112364372508984826094923715960693394760) * 10 ^ 70 +
        0940043331319554918640642035498496123847674215891300641552895397114251) * 10 ^ 70 +
        8169987691894823656385989569185568968691925699810485499877122111386415) * 10 ^ 70 +
        3381874343040840157847958753104166096738580618543837279387323366454221) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (325 - x)) = _
  rw [show 326 = 180 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_325_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (326 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_326 :
    recurrence4Scalar2Exceptional.coeff 326 =
      (((((969326489131009 * 10 ^ 70 +
        4740336851102616760609584837577368049151764148141878497119144552448707) * 10 ^ 70 +
        6439457167487519436988100621064654790195084787312986951710715435300318) * 10 ^ 70 +
        0647649467074110644841913540375190204511807954492231938016430950632927) * 10 ^ 70 +
        4327194983984589137274522108861424087322535380401457153783905181766160) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (326 - x)) = _
  rw [show 327 = 181 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_326_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (327 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_327 :
    recurrence4Scalar2Exceptional.coeff 327 =
      -(((((460271684604314 * 10 ^ 70 +
        0072671548630331388752675667832571174852826992417273710599354578041946) * 10 ^ 70 +
        9291111005680622073532011177074862895561853489331714549815973085158308) * 10 ^ 70 +
        5551313321725751071400840762005215887692198051585533087706815817685919) * 10 ^ 70 +
        1897009602146036825238694215600353898712910740156229226521806431135831) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (327 - x)) = _
  rw [show 328 = 182 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_327_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (328 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_328 :
    recurrence4Scalar2Exceptional.coeff 328 =
      (((((216675891199227 * 10 ^ 70 +
        9614893969616222902746759164077731671520306641320317907448132761209982) * 10 ^ 70 +
        7009144473595498419773705790935423877736574973150438144420981103333794) * 10 ^ 70 +
        1064983348231921231660411147099229197020395507877687083284111053442091) * 10 ^ 70 +
        3132530988299821650512678867740701375705779282655697056537273402875594) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (328 - x)) = _
  rw [show 329 = 183 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_328_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (329 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_329 :
    recurrence4Scalar2Exceptional.coeff 329 =
      -(((((101319607958433 * 10 ^ 70 +
        1395507907490595673950415029831466445014980834168386486095410299741233) * 10 ^ 70 +
        0981711033717886263872301232386022174775638356389772605689428740562600) * 10 ^ 70 +
        4924406825928033659270470861190860589963315651748946083632112562624410) * 10 ^ 70 +
        2196469057731015091440186317227387184281906226908386965122406963502491) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (329 - x)) = _
  rw [show 330 = 184 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_329_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (330 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_330 :
    recurrence4Scalar2Exceptional.coeff 330 =
      (((((47157021799540 * 10 ^ 70 +
        4332609304479332601973133006584201956856536234798623101683535603901506) * 10 ^ 70 +
        4269925049771093648840826130991620756867768306855834469117996001371709) * 10 ^ 70 +
        5007660727142262399831623036063582630761865949148040689997210644051146) * 10 ^ 70 +
        0713288714567764017579548892269412640506219552630372013208101195507557) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (330 - x)) = _
  rw [show 331 = 185 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_330_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (331 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_331 :
    recurrence4Scalar2Exceptional.coeff 331 =
      -(((((21889842642200 * 10 ^ 70 +
        6917089992365900412253093513455399119085667647580631818856223452030786) * 10 ^ 70 +
        0965484487031311265637810778775892563847909074601097537626030741130120) * 10 ^ 70 +
        5486052951362079018613829638156077623846908540669677664427710144992985) * 10 ^ 70 +
        5566487833463994311545748418951383258393223360197832478710271570088802) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (331 - x)) = _
  rw [show 332 = 186 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_331_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (332 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_332 :
    recurrence4Scalar2Exceptional.coeff 332 =
      (((((10152383787131 * 10 ^ 70 +
        2798242749564345449375895387633360519472655025688475128979630300038147) * 10 ^ 70 +
        5854086842007171082982890188992045222635668356913050788559787904726473) * 10 ^ 70 +
        8828158297267963851192283666443882528573483886513161891362583452672465) * 10 ^ 70 +
        5860598381545449278824939440761256720578746860163417698301211688565475) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (332 - x)) = _
  rw [show 333 = 187 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_332_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (333 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_333 :
    recurrence4Scalar2Exceptional.coeff 333 =
      -(((((4711233362855 * 10 ^ 70 +
        3324231092541053964595947213490153024841907390247942729387639471310851) * 10 ^ 70 +
        8936387506508129860413895697664472548717785516134436970387397271286604) * 10 ^ 70 +
        9172849139983114018946332108640998012272984910431270238460769569175707) * 10 ^ 70 +
        8516997571909825147708871475569385545613202152600562417958076480782975) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (333 - x)) = _
  rw [show 334 = 188 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_333_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (334 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_334 :
    recurrence4Scalar2Exceptional.coeff 334 =
      (((((2189295638957 * 10 ^ 70 +
        5679738911419826110735333173248338493306993971527838625714470795850355) * 10 ^ 70 +
        9262494615021498634365807081687551005597421352850498389479337186098777) * 10 ^ 70 +
        7495078424683166786492474321508878101889000771686738626378290468296376) * 10 ^ 70 +
        2239967393055252537923686638550524375956879755223866088538242233716877) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (334 - x)) = _
  rw [show 335 = 189 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_334_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (335 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_335 :
    recurrence4Scalar2Exceptional.coeff 335 =
      -(((((1018923951834 * 10 ^ 70 +
        5357151514191812963845172710396892235154085283832591985366314109701650) * 10 ^ 70 +
        1426883727797335814577080104410609698472401445887180068990762958510770) * 10 ^ 70 +
        3065923575861378948141443879008321280013806962763956839167434291476017) * 10 ^ 70 +
        9179042878624488714612603757451791735207307599934445039587098139849012) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (335 - x)) = _
  rw [show 336 = 190 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_335_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (336 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_336 :
    recurrence4Scalar2Exceptional.coeff 336 =
      (((((474688132673 * 10 ^ 70 +
        2621611615726884455201492803820016239827065140126056115419975527682114) * 10 ^ 70 +
        1254485490115068225940974348323639883571526326117055352354675224059046) * 10 ^ 70 +
        4853026156157154755387799529139335369010320557063273147221996566513437) * 10 ^ 70 +
        0667300337154086164309360123833031104699338862232575932590841619303147) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (336 - x)) = _
  rw [show 337 = 191 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_336_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (337 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_337 :
    recurrence4Scalar2Exceptional.coeff 337 =
      -(((((221106886645 * 10 ^ 70 +
        5598846847127347714458338779058056544469548626549520975678001161901957) * 10 ^ 70 +
        8771053531381283429074237304992108118381100319422979888269889301858965) * 10 ^ 70 +
        7489305784680518474385247517108927695575619419934650847415195360712520) * 10 ^ 70 +
        0409957227582746792545573986733097709752888678660300791717325542715917) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (337 - x)) = _
  rw [show 338 = 192 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_337_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (338 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_338 :
    recurrence4Scalar2Exceptional.coeff 338 =
      (((((102808666266 * 10 ^ 70 +
        9600368512829938956232775493754825810689655864539366109500020271404566) * 10 ^ 70 +
        6623519068076428669140127576627674356360465643951474135312997255347055) * 10 ^ 70 +
        8432980134890684525868280869335456713175399563735497793608364348202372) * 10 ^ 70 +
        6949098238995062638486313665123273303758347774771597377609973418121325) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (338 - x)) = _
  rw [show 339 = 193 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_338_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (339 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_339 :
    recurrence4Scalar2Exceptional.coeff 339 =
      -(((((47631145034 * 10 ^ 70 +
        3754414000380834603402228508559967335568890607931033173799074749069438) * 10 ^ 70 +
        4780148757700321032989985870586507222510378729742884122643489525197890) * 10 ^ 70 +
        7554367054703431428522614184712911898848637546601930094246959693260808) * 10 ^ 70 +
        8351252924443363094519139569200903107979013790600010839245858412931070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (339 - x)) = _
  rw [show 340 = 194 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_339_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (340 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_340 :
    recurrence4Scalar2Exceptional.coeff 340 =
      (((((21946309630 * 10 ^ 70 +
        8660072995352400154663595409005539012947278326200751596739398268263016) * 10 ^ 70 +
        7298492889577800661827250956250530931957964771440716546070654305085575) * 10 ^ 70 +
        2764146863079174241310275241737464435432321774292328167641987218377182) * 10 ^ 70 +
        9982717379336720400721217600759465674211046496043543120714776602677259) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (340 - x)) = _
  rw [show 341 = 195 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_340_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (341 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_341 :
    recurrence4Scalar2Exceptional.coeff 341 =
      -(((((10038184619 * 10 ^ 70 +
        4113420260211404730532085114570899836793154333522854316182906019555633) * 10 ^ 70 +
        3063712634591011271062723905360999032814669834045905122417247367554923) * 10 ^ 70 +
        2398315501125429346057804695328637819005130705199925910305914595367968) * 10 ^ 70 +
        9399691001782294545216154852888452793656673829789924462497146975608247) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (341 - x)) = _
  rw [show 342 = 196 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_341_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (342 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_342 :
    recurrence4Scalar2Exceptional.coeff 342 =
      (((((4550570848 * 10 ^ 70 +
        8305710022749220209904118579368991346198650144706145869262756125742232) * 10 ^ 70 +
        3051395307276017502704552818829219219950222204702678245103615431392059) * 10 ^ 70 +
        3491374289896050439673451432006712699168076384268398420342241316431403) * 10 ^ 70 +
        4030992659551597130118935544402388293668876197649549528325795700807926) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (342 - x)) = _
  rw [show 343 = 197 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_342_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (343 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_343 :
    recurrence4Scalar2Exceptional.coeff 343 =
      -(((((2041676602 * 10 ^ 70 +
        0355481268032800414456839116017360598807845850333717326296519136701029) * 10 ^ 70 +
        3603670067673465396322424766505627524984344818917278578360680725615108) * 10 ^ 70 +
        4422942077400592610282376998598526793636750849888104522124979203592192) * 10 ^ 70 +
        3396423144277636185561815461069876320148171195281465788979294972909415) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (343 - x)) = _
  rw [show 344 = 198 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_343_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (344 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_344 :
    recurrence4Scalar2Exceptional.coeff 344 =
      (((((905552560 * 10 ^ 70 +
        1503531462821730953432545768234426317307043407157551519271457139872090) * 10 ^ 70 +
        4008586709507604053176936357774303774624281209339864123386427935440450) * 10 ^ 70 +
        9012842265305368523878839428208360360663921150229428815166742548804702) * 10 ^ 70 +
        0037779544512615947023427577693677181336932474934882006641452937216357) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (344 - x)) = _
  rw [show 345 = 199 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_344_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (345 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_345 :
    recurrence4Scalar2Exceptional.coeff 345 =
      -(((((396673383 * 10 ^ 70 +
        5679809881646417925547569464603265124104902782698994199853457979361817) * 10 ^ 70 +
        0149678118879948858930009105520999611967481953220207360695046447356538) * 10 ^ 70 +
        0424836633192366251699740654405246175218482717668052517870244450654509) * 10 ^ 70 +
        3622303185572608136530742378141180533963301235189084444531648998168073) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (345 - x)) = _
  rw [show 346 = 200 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_345_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (346 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_346 :
    recurrence4Scalar2Exceptional.coeff 346 =
      (((((171476669 * 10 ^ 70 +
        3779304097619054629806752982584330672632625654405358131874559851661062) * 10 ^ 70 +
        7605309470357935347757251831625265498655938533781199904703255213762307) * 10 ^ 70 +
        4557982245990194925596470320855448954943388797923628615324403452438261) * 10 ^ 70 +
        5474613887646384534882457999699704519947621366068962497070140605713243) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (346 - x)) = _
  rw [show 347 = 201 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_346_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (347 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_347 :
    recurrence4Scalar2Exceptional.coeff 347 =
      -(((((73103267 * 10 ^ 70 +
        4861021849604298967511245540163703862355275897476184189671953375125718) * 10 ^ 70 +
        2114545409157916072695313409105513958052736339809217212488633830666754) * 10 ^ 70 +
        6707914307820486825893364009456478990714774693165388721289690558428865) * 10 ^ 70 +
        5765249201194178323229064240306087110156844816096559536176409109794068) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (347 - x)) = _
  rw [show 348 = 202 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_347_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (348 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_348 :
    recurrence4Scalar2Exceptional.coeff 348 =
      (((((30715037 * 10 ^ 70 +
        2503366201580755286344280396796728471917063512722135866383429470438128) * 10 ^ 70 +
        6204387210654887195542485721516757563408401862178269604849786689221054) * 10 ^ 70 +
        0254377523744286017514146078176516337786556939485827684725340624468825) * 10 ^ 70 +
        0866834175766191720959673945781840805849269578330639390635754609260589) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (348 - x)) = _
  rw [show 349 = 203 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_348_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (349 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_349 :
    recurrence4Scalar2Exceptional.coeff 349 =
      -(((((12710037 * 10 ^ 70 +
        7443563025464858911498268086851215021726652733441654012131041753348637) * 10 ^ 70 +
        3190848570462724614892882250462638549068349005042791849937605257221672) * 10 ^ 70 +
        4921564629461995130265904302033404824870818890591528277954229184133946) * 10 ^ 70 +
        4871242654505667327500129062816985597636757920135039344430631559498431) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (349 - x)) = _
  rw [show 350 = 204 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_349_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (350 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_350 :
    recurrence4Scalar2Exceptional.coeff 350 =
      (((((5175466 * 10 ^ 70 +
        2616015235490844682281303132815376552602059826341638056914206195065309) * 10 ^ 70 +
        1214531236316644231313260522211770724203109593539571031916222777196221) * 10 ^ 70 +
        2586868837956194538346678104382025737153972290727140500231027875021871) * 10 ^ 70 +
        1517409320058782444041497272295547688503467773757141706190437612380481) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (350 - x)) = _
  rw [show 351 = 205 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_350_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (351 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_351 :
    recurrence4Scalar2Exceptional.coeff 351 =
      -(((((2071304 * 10 ^ 70 +
        0017955371401068111757937667921902958878389033189141682256607976724539) * 10 ^ 70 +
        1848691465583185492567140130934899395921721769967218002601411751289259) * 10 ^ 70 +
        5569065939616996616289909618040388359236560279732019625305289349680303) * 10 ^ 70 +
        6961484018127311748721327890703384084180998719937569771498705294174989) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (351 - x)) = _
  rw [show 352 = 206 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_351_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (352 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_352 :
    recurrence4Scalar2Exceptional.coeff 352 =
      (((((813355 * 10 ^ 70 +
        1200248009674869553433885294844494411980460596970677855047914018095386) * 10 ^ 70 +
        6341917058351013482344655513191161943338155723963876407249265301802889) * 10 ^ 70 +
        7507976691127837355138597183758436212317702937913299184692627933669221) * 10 ^ 70 +
        0032960743190049753941348462479355452952352041187446871183803156178490) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (352 - x)) = _
  rw [show 353 = 207 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_352_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (353 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_353 :
    recurrence4Scalar2Exceptional.coeff 353 =
      -(((((312559 * 10 ^ 70 +
        1841535139445071589012536724959050378814354490137760336303843791984491) * 10 ^ 70 +
        5351875134308496003521139426010223553067026394243325898575075938711592) * 10 ^ 70 +
        0467234861846634324180941098846051614531615442654906570876154244170391) * 10 ^ 70 +
        4896066397761932889698166641581896369861677201030649053943771194931307) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (353 - x)) = _
  rw [show 354 = 208 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_353_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (354 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_354 :
    recurrence4Scalar2Exceptional.coeff 354 =
      (((((117075 * 10 ^ 70 +
        3556320130244983298005941560269989352775209689781803952176316586794196) * 10 ^ 70 +
        0081725799177874567027966204617227797585627031839860560801229752669256) * 10 ^ 70 +
        9073222295231637457337752196493013736077122118242299282550822392417600) * 10 ^ 70 +
        3658612429758281812340243004512617368643613409182261405404544146391269) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (354 - x)) = _
  rw [show 355 = 209 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_354_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (355 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_355 :
    recurrence4Scalar2Exceptional.coeff 355 =
      -(((((42473 * 10 ^ 70 +
        8646358615904177271482016330693970879218899372941785216930663403491164) * 10 ^ 70 +
        8509797035068171868376045524349308314714145458066741586702677862713476) * 10 ^ 70 +
        0583634687810777870294890558711822903532898647790025521773945893214563) * 10 ^ 70 +
        4991924632682831536907842870316738720729390938220854553595548842897655) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (355 - x)) = _
  rw [show 356 = 210 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_355_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (356 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_356 :
    recurrence4Scalar2Exceptional.coeff 356 =
      (((((14766 * 10 ^ 70 +
        7635805122269300012229792197228236272283358206258118144468382716560030) * 10 ^ 70 +
        1532188718881105817552278432441537223312477598099994677608486209621621) * 10 ^ 70 +
        7202093018570352812975686963966806867809489138282157495724031943800815) * 10 ^ 70 +
        9875382349767414665820322161453471308774261618764474496312457636753251) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (356 - x)) = _
  rw [show 357 = 211 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_356_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (357 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_357 :
    recurrence4Scalar2Exceptional.coeff 357 =
      -(((((4825 * 10 ^ 70 +
        5534263038107987120806390144552719864703882786239915554586178269842683) * 10 ^ 70 +
        4742341886164576172440960703820043298165733100984775802184849845307938) * 10 ^ 70 +
        0020933395574541972676918261940933296378138213318568875164759518566868) * 10 ^ 70 +
        5182693922123186694429877164406792923164598084701508191900713319001677) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (357 - x)) = _
  rw [show 358 = 212 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_357_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (358 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_358 :
    recurrence4Scalar2Exceptional.coeff 358 =
      (((((1422 * 10 ^ 70 +
        9937688978257451180182805323054101552270689848159297710477116179752348) * 10 ^ 70 +
        0420231275019453203031300757953056620778385771197840728211315901957066) * 10 ^ 70 +
        9394724925823725869991344130331053996501037626928124373900889307665751) * 10 ^ 70 +
        0759415388946623400757769410497726332706789024424222377975494644747917) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (358 - x)) = _
  rw [show 359 = 213 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_358_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (359 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_359 :
    recurrence4Scalar2Exceptional.coeff 359 =
      -(((((338 * 10 ^ 70 +
        2600988871296492248371894021186199559707625066512113488270717826061912) * 10 ^ 70 +
        6442619108311795732173243853918598381921390188013394422028273653001341) * 10 ^ 70 +
        0334058865371292333081232403329873233012105646614652975531099921848617) * 10 ^ 70 +
        7993091307900768869705586105427979156564659281580627882310208864118598) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (359 - x)) = _
  rw [show 360 = 214 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_359_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (360 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_360 :
    recurrence4Scalar2Exceptional.coeff 360 =
      (((((32 * 10 ^ 70 +
        9661615092047706977116331461847810171830263103897241183420210740000487) * 10 ^ 70 +
        0718570625603354394455131953639037133568488940430078386328066524076931) * 10 ^ 70 +
        4150444881148406657567418157908360213911710111865890971499284571731861) * 10 ^ 70 +
        6920154246249907847818108495537853384003063448982520104495060087153243) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (360 - x)) = _
  rw [show 361 = 215 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_360_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (361 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_361 :
    recurrence4Scalar2Exceptional.coeff 361 =
      (((((30 * 10 ^ 70 +
        9960113022549560304158749273636076946093912480076613474068197712330726) * 10 ^ 70 +
        2944979948644239936605559413920253898315673270088904712948387126521638) * 10 ^ 70 +
        7286411825625170873805670897110325171187409315690970447057839303718785) * 10 ^ 70 +
        6946912924978514385459906153360055322366915917559353900111673728817935) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (361 - x)) = _
  rw [show 362 = 216 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_361_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (362 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_362 :
    recurrence4Scalar2Exceptional.coeff 362 =
      -(((((30 * 10 ^ 70 +
        9748474361352242166734734333550860351991632140521438351984879613734996) * 10 ^ 70 +
        4755669950164290060757447056223880105290844431858599249653997248748232) * 10 ^ 70 +
        3040139645167116692275735279886107187984708073431246795510165189847028) * 10 ^ 70 +
        2136825533296835843131892638836602461022291092276220001013658805713703) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (362 - x)) = _
  rw [show 363 = 217 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_362_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (363 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_363 :
    recurrence4Scalar2Exceptional.coeff 363 =
      (((((19 * 10 ^ 70 +
        9848691680277069223102433497876794298941888608774363058530420441444411) * 10 ^ 70 +
        4118149566575311738764362093395883897363416282141969897499522388791096) * 10 ^ 70 +
        1432966540038766073424523493375721756546904458709018653598915335110975) * 10 ^ 70 +
        0383186064020304245151003164310280015286820439513665527523073142006559) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (363 - x)) = _
  rw [show 364 = 218 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_363_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (364 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_364 :
    recurrence4Scalar2Exceptional.coeff 364 =
      -(((((11 * 10 ^ 70 +
        0056492858908783541365054433184178258247968168152647193781137376565828) * 10 ^ 70 +
        8162686105589829523834453796048041474652936529851363998929717210648624) * 10 ^ 70 +
        5650094914664658661185285353051161511578804835328998656398316342656536) * 10 ^ 70 +
        5662433746895533167583307008572971476177106550776241530820007826297770) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (364 - x)) = _
  rw [show 365 = 219 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_364_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (365 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_365 :
    recurrence4Scalar2Exceptional.coeff 365 =
      (((((5 * 10 ^ 70 +
        5560308019321073269542192158478870727020922839316668121253305776162806) * 10 ^ 70 +
        6180200613930040915722509104849829921273979885243132579487982260530820) * 10 ^ 70 +
        3582228730538067473989762334935364594356586112291148135040373602067339) * 10 ^ 70 +
        8113525395704629340978169849416764423479923909182343715854229828187740) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (365 - x)) = _
  rw [show 366 = 220 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_365_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (366 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_366 :
    recurrence4Scalar2Exceptional.coeff 366 =
      -(((((2 * 10 ^ 70 +
        6468920060127490325608888437456524072276022219505317997384661066625273) * 10 ^ 70 +
        5664449472259634473186329337363494168205446963970470847495709340417373) * 10 ^ 70 +
        3413676323028267144968508489966945726553414179061806556990484844894850) * 10 ^ 70 +
        5775072772567751626569413743434477784382604151598226357751920123594934) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (366 - x)) = _
  rw [show 367 = 221 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_366_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (367 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_367 :
    recurrence4Scalar2Exceptional.coeff 367 =
      (((((1 * 10 ^ 70 +
        2073130628377063361187135447029293486825277324591570143970803795391400) * 10 ^ 70 +
        9842038360263658892878917485662319055316912237702361593534838081491319) * 10 ^ 70 +
        5568707208703325817559218248663864489309039055219007869813708821822173) * 10 ^ 70 +
        1509483552712512722492163631045631987595561788670637595916168220076254) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (367 - x)) = _
  rw [show 368 = 222 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_367_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (368 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_368 :
    recurrence4Scalar2Exceptional.coeff 368 =
      -((((5315662531450233381575459720058099652785679308909897335174340696321066 * 10 ^ 70 +
        7691980299934941194523997861048298771015763157572953723240414027234000) * 10 ^ 70 +
        8635026097954207778590603876451661494951664784389379919291111321100536) * 10 ^ 70 +
        4043444040203757169549081313867746132700195223874357303660019031100864) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (368 - x)) = _
  rw [show 369 = 223 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_368_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (369 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_369 :
    recurrence4Scalar2Exceptional.coeff 369 =
      ((((2270368298018531185156725721770368752689186844468808978969468905387598 * 10 ^ 70 +
        9766309484203196084240670558953610100008542668723725274538171996296891) * 10 ^ 70 +
        4653532963307194614862334298794648319856268934111517988282444297378666) * 10 ^ 70 +
        8491430164146369937496324212776401878484347465777646585448541746891623) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (369 - x)) = _
  rw [show 370 = 224 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_369_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (370 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_370 :
    recurrence4Scalar2Exceptional.coeff 370 =
      -((((943610668473053246285886005985093815972363690134690727478412300968528 * 10 ^ 70 +
        0813839634055231599630929723913914889642551053741100958288387973235857) * 10 ^ 70 +
        8521395952647569280259670094054568686565038723182940526103071817142184) * 10 ^ 70 +
        7220676946790523062604603587917095540524277494435700794379994624587826) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (370 - x)) = _
  rw [show 371 = 225 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (371 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_371 :
    recurrence4Scalar2Exceptional.coeff 371 =
      ((((382387899632330942034047004120954299401221768507386439296643093075782 * 10 ^ 70 +
        0315911581833393661460579268041021913063663349318372018260700632619689) * 10 ^ 70 +
        6581061522782876677995785009635508978764921115250583522109189231276668) * 10 ^ 70 +
        8162854526517040578264825616452500420459428151680891607259195042823386) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (371 - x)) = _
  rw [show 372 = 226 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 16 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
