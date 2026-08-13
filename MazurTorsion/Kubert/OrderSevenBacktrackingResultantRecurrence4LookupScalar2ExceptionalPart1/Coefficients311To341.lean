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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
