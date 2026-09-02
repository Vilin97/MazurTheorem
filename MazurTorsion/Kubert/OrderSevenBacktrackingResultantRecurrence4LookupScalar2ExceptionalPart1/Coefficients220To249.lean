/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
