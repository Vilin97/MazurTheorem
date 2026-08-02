/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_1
  recurrence4C1_coeff_10
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_11
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_12
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_13
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_2
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21

attribute [local simp]
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_3
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_4
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_5
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_6
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_7
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_8

attribute [local simp]
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_9
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar1Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (272 + x) *
        remainder6Coefficient1.coeff (272 - (272 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 272 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (272 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (272 - (272 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_272 :
    recurrence4Scalar1Exceptional.coeff 272 =
      (((((2886786394452517511269673636 * 10 ^ 70 +
        6101779730743934553211880964864347717165377678059591537580586461868332) * 10 ^ 70 +
        5025686815356174866119059470908994551146313823051553755518590424800449) * 10 ^ 70 +
        5089586821214009318989902026402176849532156557350142580804846383080320) * 10 ^ 70 +
        6085575626965306501663937642813847445501692095668818312071984904417297) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (272 - x)) = _
  rw [show 273 = 123 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (273 + x) *
        remainder6Coefficient1.coeff (273 - (273 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 273 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (273 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (273 - (273 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_273 :
    recurrence4Scalar1Exceptional.coeff 273 =
      -(((((2382987929810189974973572612 * 10 ^ 70 +
        6862564322332312888653581838359436799312169271249285944903741430424062) * 10 ^ 70 +
        7848692327383338023611707619758994880317133989718486203674739131777649) * 10 ^ 70 +
        8790069455447257919522882176482366679538393020232547723336362536213625) * 10 ^ 70 +
        2634065680971924452467393004185613713471102860154916234788263488523481) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (273 - x)) = _
  rw [show 274 = 124 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (274 + x) *
        remainder6Coefficient1.coeff (274 - (274 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 274 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (274 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (274 - (274 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_274 :
    recurrence4Scalar1Exceptional.coeff 274 =
      (((((1940938195184930130235869961 * 10 ^ 70 +
        1217404231527164639084569588518062309466594785668067105945237410874366) * 10 ^ 70 +
        6069098791820482182993582423136732016894142939497042068992749025568455) * 10 ^ 70 +
        4365223735617051036422266035374670636272586384872509135298762606089638) * 10 ^ 70 +
        0405411617133510889321734326794001313004972669370990125666097542554930) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (274 - x)) = _
  rw [show 275 = 125 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (275 + x) *
        remainder6Coefficient1.coeff (275 - (275 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 275 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (275 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (275 - (275 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_275 :
    recurrence4Scalar1Exceptional.coeff 275 =
      -(((((1559768003755490772797985087 * 10 ^ 70 +
        4716370298888193943572767542633906392178824290587343196965344714730427) * 10 ^ 70 +
        3739242218583233478913321426727660357024480340960160525642806804655046) * 10 ^ 70 +
        0199495842546629475744058889244386639919457123033892557659398248688123) * 10 ^ 70 +
        9829042167949378151019436758349945788081711459549739955731531825842033) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (275 - x)) = _
  rw [show 276 = 126 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (276 + x) *
        remainder6Coefficient1.coeff (276 - (276 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 276 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (276 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (276 - (276 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_276 :
    recurrence4Scalar1Exceptional.coeff 276 =
      (((((1236628692016876795504727740 * 10 ^ 70 +
        0753411803555617241525845960329256750019563726611519581529162119244567) * 10 ^ 70 +
        3142855319335701211828024152178417194065521856857053032239269557154578) * 10 ^ 70 +
        9950666628246730058843880689892986152434793067311270304518988399176879) * 10 ^ 70 +
        5743709378469364757275795188408751470594144996216805253931442703524055) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (276 - x)) = _
  rw [show 277 = 127 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (277 + x) *
        remainder6Coefficient1.coeff (277 - (277 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 277 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (277 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (277 - (277 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_277 :
    recurrence4Scalar1Exceptional.coeff 277 =
      -(((((967205236007632606069762082 * 10 ^ 70 +
        6006606937927781917564211157146984412122186142091725304728488025106328) * 10 ^ 70 +
        2566458366211668151220098051429092656700865116318109196295489105025093) * 10 ^ 70 +
        0827742509578706930423876684587846402105082813555770289737114583021737) * 10 ^ 70 +
        2912392421007867551621487837530362952474978799448871206971091541125184) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (277 - x)) = _
  rw [show 278 = 128 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (278 + x) *
        remainder6Coefficient1.coeff (278 - (278 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 278 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (278 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (278 - (278 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_278 :
    recurrence4Scalar1Exceptional.coeff 278 =
      (((((746213269880396009228623704 * 10 ^ 70 +
        2370967895679497446999273464576924295028063222480921885066077522463065) * 10 ^ 70 +
        0237954001625103104463997230910465776194769631115831934614534779724928) * 10 ^ 70 +
        9805629022224784958765952725032821165172183842150557994710361632021336) * 10 ^ 70 +
        9688199345658081033816000093447579470641589468444349166486313813270937) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (278 - x)) = _
  rw [show 279 = 129 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (279 + x) *
        remainder6Coefficient1.coeff (279 - (279 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 279 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (279 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (279 - (279 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_279 :
    recurrence4Scalar1Exceptional.coeff 279 =
      -(((((567848976678702289811016716 * 10 ^ 70 +
        3707556165705034674743341487723242018532495258889247057112457813042664) * 10 ^ 70 +
        4722128470727362388618010738208720853903207514288661904073634045649555) * 10 ^ 70 +
        1811013345366263216559833917990173886932520393230359277984703869377278) * 10 ^ 70 +
        4825262443335962554612683145803936850992367967697819332429961883775195) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (279 - x)) = _
  rw [show 280 = 130 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (280 + x) *
        remainder6Coefficient1.coeff (280 - (280 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 280 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (280 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (280 - (280 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_280 :
    recurrence4Scalar1Exceptional.coeff 280 =
      (((((426170975167561055775561184 * 10 ^ 70 +
        8900605440553241551632648718434022189376103401894177171381786000340689) * 10 ^ 70 +
        8652585302787524723347415019170524226781710578270100390883441545326907) * 10 ^ 70 +
        7185716568020602400530172150134679592996107617469157884350424083632822) * 10 ^ 70 +
        7054515223978273719770522897438607115771422697964383463515905682722066) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (280 - x)) = _
  rw [show 281 = 131 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (281 + x) *
        remainder6Coefficient1.coeff (281 - (281 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 281 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (281 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (281 - (281 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_281 :
    recurrence4Scalar1Exceptional.coeff 281 =
      -(((((315403237737375234234310351 * 10 ^ 70 +
        4157848481237866673361776347716810895750163360745937725080770034738075) * 10 ^ 70 +
        3485836882728784909797841250546430499505076485163558376290684012775104) * 10 ^ 70 +
        3996890888706191042954077698150994234628149677256848304531841591807254) * 10 ^ 70 +
        5941682936534170348373431018323038702161702617860731431877803081285157) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (281 - x)) = _
  rw [show 282 = 132 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (282 + x) *
        remainder6Coefficient1.coeff (282 - (282 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 282 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (282 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (282 - (282 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_282 :
    recurrence4Scalar1Exceptional.coeff 282 =
      (((((230156789407359884171792158 * 10 ^ 70 +
        3831094857256645480845442761565901294207123474334192878265109188300019) * 10 ^ 70 +
        0507705865338907230797278514837139573386304922373027314197512299544974) * 10 ^ 70 +
        6125541816989855793807598754412839569389767627623610988517150222025035) * 10 ^ 70 +
        8626223536955063826652538434546000402724229950210195344833020159263206) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (282 - x)) = _
  rw [show 283 = 133 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (283 + x) *
        remainder6Coefficient1.coeff (283 - (283 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 283 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (283 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (283 - (283 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_283 :
    recurrence4Scalar1Exceptional.coeff 283 =
      -(((((165574847059039672624271723 * 10 ^ 70 +
        1172405195093565129119058816560041405139471131095578201277909898333986) * 10 ^ 70 +
        8644957395592516042737602753426033177387451202528387741745545646790907) * 10 ^ 70 +
        3239828236827810351498753150495718440060203273888429526801418719513475) * 10 ^ 70 +
        1596562719596022203712372390828428071856608127944808812336040155352367) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (283 - x)) = _
  rw [show 284 = 134 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (284 + x) *
        remainder6Coefficient1.coeff (284 - (284 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 284 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (284 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (284 - (284 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_284 :
    recurrence4Scalar1Exceptional.coeff 284 =
      (((((117410892677976932103802303 * 10 ^ 70 +
        5849671967004169375272000741639168160073321156686788239060188348235208) * 10 ^ 70 +
        2328653064591585575855492772627538989112383766196407499410786719770414) * 10 ^ 70 +
        3469334159291377075724630020187671037265890711669589632713889346542370) * 10 ^ 70 +
        4585067065544773874666243919833070928455336659516165353085115638588465) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (284 - x)) = _
  rw [show 285 = 135 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (285 + x) *
        remainder6Coefficient1.coeff (285 - (285 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 285 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (285 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (285 - (285 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_285 :
    recurrence4Scalar1Exceptional.coeff 285 =
      -(((((82051959973399954653520105 * 10 ^ 70 +
        9610664094632798850977740827384584520274888647077147740579453316575592) * 10 ^ 70 +
        5255889208456260803689760409580031700623144359978174396926062003103419) * 10 ^ 70 +
        8449193890143174791650271038331070171552851259707864430759492158401308) * 10 ^ 70 +
        2776765369485178289813349764972500871788390162243859909829542860292652) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (285 - x)) = _
  rw [show 286 = 136 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (286 + x) *
        remainder6Coefficient1.coeff (286 - (286 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 286 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (286 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (286 - (286 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_286 :
    recurrence4Scalar1Exceptional.coeff 286 =
      (((((56500394858633526335557916 * 10 ^ 70 +
        1289212333834263718267691318130954932169063010455016109447527219837919) * 10 ^ 70 +
        1260247869520619809423691996643574280419600754666357227596321397385132) * 10 ^ 70 +
        0881254112235692593684427977282064009177708403702192845362598991530316) * 10 ^ 70 +
        6270450556542945723557500923059323001792739237977504712069031443065316) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (286 - x)) = _
  rw [show 287 = 137 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (287 + x) *
        remainder6Coefficient1.coeff (287 - (287 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 287 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (287 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (287 - (287 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_287 :
    recurrence4Scalar1Exceptional.coeff 287 =
      -(((((38326905688224403272316512 * 10 ^ 70 +
        9571452207088992899894382156379840699774698870255334809056195387128058) * 10 ^ 70 +
        2634312888781321227871092294507467632805990174191836532657438325865868) * 10 ^ 70 +
        1865809261398052056021505458971918926870705559368183277816496951852972) * 10 ^ 70 +
        4296942421780720105342032269964987864729767800635434336163065637345613) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (287 - x)) = _
  rw [show 288 = 138 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (288 + x) *
        remainder6Coefficient1.coeff (288 - (288 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 288 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (288 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (288 - (288 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_288 :
    recurrence4Scalar1Exceptional.coeff 288 =
      (((((25606281265794995906576127 * 10 ^ 70 +
        7484671850128436548124652776392974247173782325814870394004845365408303) * 10 ^ 70 +
        7988197601117923789720249200130010303791694604787358293796848387776361) * 10 ^ 70 +
        3866078855406933747986176476901026659089220178746885527882573120912232) * 10 ^ 70 +
        4814065477836037458100817383902715475421585663677324184546011211808086) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (288 - x)) = _
  rw [show 289 = 139 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (289 + x) *
        remainder6Coefficient1.coeff (289 - (289 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 289 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (289 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (289 - (289 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_289 :
    recurrence4Scalar1Exceptional.coeff 289 =
      -(((((16845143496264682846585136 * 10 ^ 70 +
        1313041301848823006081876228394865339884420917905247088867418688319562) * 10 ^ 70 +
        4229043526074643112944801459902242122932303513663640839853005782996807) * 10 ^ 70 +
        3114884921122859271284992977200127388186355747178045973101233167807900) * 10 ^ 70 +
        3591451670447629875320501741754910925488023237153918538603318298113507) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (289 - x)) = _
  rw [show 290 = 140 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (290 + x) *
        remainder6Coefficient1.coeff (290 - (290 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 290 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (290 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (290 - (290 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_290 :
    recurrence4Scalar1Exceptional.coeff 290 =
      (((((10908878666099753629683235 * 10 ^ 70 +
        6370543130463232542519536173664251716612963150661718112668842952828329) * 10 ^ 70 +
        8427806994015595006857091619160596452845152078155048852941276987004090) * 10 ^ 70 +
        1065251122282346625551016735505071580960647941138303160308512382061069) * 10 ^ 70 +
        8866415199053918361017557701384494117849293202085338138064835093412427) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (290 - x)) = _
  rw [show 291 = 141 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (291 + x) *
        remainder6Coefficient1.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 291 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (291 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (291 - (291 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_291 :
    recurrence4Scalar1Exceptional.coeff 291 =
      -(((((6952734196277086843873731 * 10 ^ 70 +
        9339020255860401851595309429414268177840080378833976845346606056108042) * 10 ^ 70 +
        7702111960267394122350546849362907622829512707286548094506442803129220) * 10 ^ 70 +
        4732242162127946341906974617517757427395748263178235807291580106460114) * 10 ^ 70 +
        7533115527483898051682789711678239961510994131175460336829426129218996) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (291 - x)) = _
  rw [show 292 = 142 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (292 + x) *
        remainder6Coefficient1.coeff (292 - (292 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 292 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (292 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (292 - (292 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_292 :
    recurrence4Scalar1Exceptional.coeff 292 =
      (((((4360162537191147566894993 * 10 ^ 70 +
        2788511421968802394339985588980415246029825033797141769698635758613601) * 10 ^ 70 +
        8874619510638065500239628237006604915629955536345771005199471570341104) * 10 ^ 70 +
        9830892673620386447702936342647430432391547094862491617886577787078747) * 10 ^ 70 +
        3920670459910449032648945849234352033082978028194976538591084466777107) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (292 - x)) = _
  rw [show 293 = 143 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (293 + x) *
        remainder6Coefficient1.coeff (293 - (293 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 293 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (293 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (293 - (293 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_293 :
    recurrence4Scalar1Exceptional.coeff 293 =
      -(((((2689942070645429578062251 * 10 ^ 70 +
        1604235319697502118123111188192650141414333045787186550165618474927683) * 10 ^ 70 +
        3693904851390380079786701170362981609851127867441069143000636714554142) * 10 ^ 70 +
        5869573254216804976980324050598476791887170675979130916386338027589917) * 10 ^ 70 +
        8108643719654892655306347787977068656143473444811493030463700323278581) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (293 - x)) = _
  rw [show 294 = 144 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (294 + x) *
        remainder6Coefficient1.coeff (294 - (294 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 294 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (294 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (294 - (294 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_294 :
    recurrence4Scalar1Exceptional.coeff 294 =
      (((((1632438185893987025368894 * 10 ^ 70 +
        8271922381840033489851870586407153558678771415349408360553882630570247) * 10 ^ 70 +
        4659364573820665687436165830954507478966642708365448341592134213906191) * 10 ^ 70 +
        4640325036950587320025915466932312597096202399627998216479632040500023) * 10 ^ 70 +
        8746997696905216501268430365604091767443391148947179451146061426234000) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (294 - x)) = _
  rw [show 295 = 145 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (295 + x) *
        remainder6Coefficient1.coeff (295 - (295 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 295 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (295 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (295 - (295 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_295 :
    recurrence4Scalar1Exceptional.coeff 295 =
      -(((((974567161934249696010356 * 10 ^ 70 +
        4691379194035945156860429741813348516585416812699672789660578103055324) * 10 ^ 70 +
        0204713068176900037062428255042516578042664133933691090677676731713714) * 10 ^ 70 +
        5383583488247874651107969526877168194133520793608849108786965848496344) * 10 ^ 70 +
        0340336391626819103459522136912121781558087028269996103565312703404070) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (295 - x)) = _
  rw [show 296 = 146 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (296 + x) *
        remainder6Coefficient1.coeff (296 - (296 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 296 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (296 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (296 - (296 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_296 :
    recurrence4Scalar1Exceptional.coeff 296 =
      (((((572540546658626566005694 * 10 ^ 70 +
        4778599439264739674030513314675181277011783275858433156406697523852527) * 10 ^ 70 +
        8576593663327178984502711233400353400929352601329326149211452194522210) * 10 ^ 70 +
        6688656877972735082138747873627091079601131288574265729774617968099910) * 10 ^ 70 +
        2219530947368217262200830963841589311895122889807660111813864529905498) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (296 - x)) = _
  rw [show 297 = 147 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (297 + x) *
        remainder6Coefficient1.coeff (297 - (297 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 297 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (297 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (297 - (297 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_297 :
    recurrence4Scalar1Exceptional.coeff 297 =
      -(((((331232712898305272553676 * 10 ^ 70 +
        5442862086522452344417927447278744730343012362400070694217114018477477) * 10 ^ 70 +
        9409598111342997100224102476321419444010951075177682189910952360059325) * 10 ^ 70 +
        4844952700085428645933502258179846486902016151220503435746833220383912) * 10 ^ 70 +
        0138262177428440337660330472523961323207008623494876528613378941008690) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (297 - x)) = _
  rw [show 298 = 148 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (298 + x) *
        remainder6Coefficient1.coeff (298 - (298 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 298 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (298 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (298 - (298 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_298 :
    recurrence4Scalar1Exceptional.coeff 298 =
      (((((188961118456282703579034 * 10 ^ 70 +
        0378959633777814595670682481846711600102118203257552561622143052552568) * 10 ^ 70 +
        5929892557650213248954939105339094142668624275443655430960240976884776) * 10 ^ 70 +
        5519754964444715747575330668723678783089356406999118364516345783782364) * 10 ^ 70 +
        3815940332422919946487726816258702448110386622206655641631854403906335) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (298 - x)) = _
  rw [show 299 = 149 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (299 + x) *
        remainder6Coefficient1.coeff (299 - (299 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 299 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (299 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (299 - (299 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_299 :
    recurrence4Scalar1Exceptional.coeff 299 =
      -(((((106535512876377735754992 * 10 ^ 70 +
        8596720292607967127687122686515618049577590506219592878696112406174612) * 10 ^ 70 +
        7019413797582755290929154074966214753557330307952333774424063794181671) * 10 ^ 70 +
        3257153080748574180436500200682723517138497430286215244158110489105446) * 10 ^ 70 +
        9762541172726850023531783804298947530792269464117850798793787799961503) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (299 - x)) = _
  rw [show 300 = 150 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (300 + x) *
        remainder6Coefficient1.coeff (300 - (300 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 300 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (300 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (300 - (300 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_300 :
    recurrence4Scalar1Exceptional.coeff 300 =
      (((((59567702022884465820469 * 10 ^ 70 +
        2082556068630790363220026791009388011289533759711475745453256247343831) * 10 ^ 70 +
        3224412164075378159577089161685360447357365284394595639870044828004606) * 10 ^ 70 +
        4322569363050250979514881399149758177981296229451031665734030407858649) * 10 ^ 70 +
        6971959351440157764431925255254967458143200231755290134608503632784036) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (300 - x)) = _
  rw [show 301 = 151 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (301 + x) *
        remainder6Coefficient1.coeff (301 - (301 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 301 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (301 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (301 - (301 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_301 :
    recurrence4Scalar1Exceptional.coeff 301 =
      -(((((33198718534819545738006 * 10 ^ 70 +
        9836804607314133894232915193539239076202201403069081804593981749885996) * 10 ^ 70 +
        1936168218137521396445113955143264137932380429965521270450354702972538) * 10 ^ 70 +
        0332459397851547232441701879597957840899510757165945313503217807418240) * 10 ^ 70 +
        5544025453773866894500561890159570580016580264742284004777938751146168) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (301 - x)) = _
  rw [show 302 = 152 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (302 + x) *
        remainder6Coefficient1.coeff (302 - (302 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 302 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (302 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (302 - (302 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_302 :
    recurrence4Scalar1Exceptional.coeff 302 =
      (((((18568541814574563759227 * 10 ^ 70 +
        6524175153975102775730363274000968308337230713205007673083613051249674) * 10 ^ 70 +
        8386251740607647765054567034273488536466938102473702835163270034185180) * 10 ^ 70 +
        5915647876938576543098912370121812975416698252157768850193641616669168) * 10 ^ 70 +
        7737418811035815163520403092998536023834927926300408472837882914562554) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (302 - x)) = _
  rw [show 303 = 153 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (303 + x) *
        remainder6Coefficient1.coeff (303 - (303 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 303 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (303 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (303 - (303 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_303 :
    recurrence4Scalar1Exceptional.coeff 303 =
      -(((((10508318112582739838846 * 10 ^ 70 +
        0490716292417077646827543208053901700108086421193638146429016749988025) * 10 ^ 70 +
        4563540467490154922841081377911924933446118661719825535288559219584763) * 10 ^ 70 +
        5319084221587933541008000543225661363988640623051392154442283325393374) * 10 ^ 70 +
        1664919948051031912951208729037719184367666713699187673052902499613785) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (303 - x)) = _
  rw [show 304 = 154 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (304 + x) *
        remainder6Coefficient1.coeff (304 - (304 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 304 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (304 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (304 - (304 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_304 :
    recurrence4Scalar1Exceptional.coeff 304 =
      (((((6067805385324003413044 * 10 ^ 70 +
        8548440033087302544226641455743310949326768773505722478815757059848006) * 10 ^ 70 +
        2974958813314252999098376983104141390115198520436908713411424282080369) * 10 ^ 70 +
        8528805419603909688933218493763803604519029782115096511110193577032973) * 10 ^ 70 +
        2309831235066378338600671542252447899050675383205089301635714234389442) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (304 - x)) = _
  rw [show 305 = 155 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (305 + x) *
        remainder6Coefficient1.coeff (305 - (305 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 305 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (305 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (305 - (305 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_305 :
    recurrence4Scalar1Exceptional.coeff 305 =
      -(((((3598664665298428259056 * 10 ^ 70 +
        5845581551484636377187442402438830427089995822424962769304903253673105) * 10 ^ 70 +
        0953941082343543262097450895788916989062897553414643076892603137115688) * 10 ^ 70 +
        8302430266914142103645652131554932736331491921265401643729862344725401) * 10 ^ 70 +
        1288540753843178691158710789010182895769078390420816934999645359048935) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (305 - x)) = _
  rw [show 306 = 156 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (306 + x) *
        remainder6Coefficient1.coeff (306 - (306 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 306 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (306 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (306 - (306 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_306 :
    recurrence4Scalar1Exceptional.coeff 306 =
      (((((2198057681074446547263 * 10 ^ 70 +
        0004539763340331136115122849281013518006099849739743570296372855040010) * 10 ^ 70 +
        3729436223571710046912701631889073252361518665358224087100904219601131) * 10 ^ 70 +
        2236727967971430396460075848886436611113051122580475160253712162629484) * 10 ^ 70 +
        7950104593014470166059774676707944502610729792655087935954401156278011) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (306 - x)) = _
  rw [show 307 = 157 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (307 + x) *
        remainder6Coefficient1.coeff (307 - (307 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 307 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (307 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (307 - (307 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_307 :
    recurrence4Scalar1Exceptional.coeff 307 =
      -(((((1379646179575280980460 * 10 ^ 70 +
        4016232673863059160992408716103315206609862641290345191922892788431936) * 10 ^ 70 +
        8133780014583409458731331617406395142253325205541834053084641165103125) * 10 ^ 70 +
        3766606064293213365047168629658148840660678311668516975616767576390136) * 10 ^ 70 +
        9068526618375891869560741619352644456172199555986726695641063535954742) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (307 - x)) = _
  rw [show 308 = 158 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (308 + x) *
        remainder6Coefficient1.coeff (308 - (308 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 308 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (308 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (308 - (308 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_308 :
    recurrence4Scalar1Exceptional.coeff 308 =
      (((((884239478340075435617 * 10 ^ 70 +
        4269127658979301511973701609256330344100316154192806495419022536450853) * 10 ^ 70 +
        1849257473682726200441671847891947021812711333902037530397531765413380) * 10 ^ 70 +
        2665125281618728775711146012273394550615592129921024316606818436310750) * 10 ^ 70 +
        1907974758945527079389373590858772317754870939393503046494412524547015) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (308 - x)) = _
  rw [show 309 = 159 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (309 + x) *
        remainder6Coefficient1.coeff (309 - (309 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 309 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (309 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (309 - (309 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_309 :
    recurrence4Scalar1Exceptional.coeff 309 =
      -(((((573808065275258891176 * 10 ^ 70 +
        2010172748822025417116978591389898362356411057526988946557179061746371) * 10 ^ 70 +
        2488018152245266337677383443443783120028931001507593314359222194253165) * 10 ^ 70 +
        3284079944824841243259266000794025701219223636992351621573013905498969) * 10 ^ 70 +
        1884764921710773261599962953067563541349978161105907622401701940117149) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (309 - x)) = _
  rw [show 310 = 160 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (310 + x) *
        remainder6Coefficient1.coeff (310 - (310 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 310 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (310 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (310 - (310 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_310 :
    recurrence4Scalar1Exceptional.coeff 310 =
      (((((373817669402979534037 * 10 ^ 70 +
        8960949101998350126878968920712805061934441061321773413066701654641116) * 10 ^ 70 +
        9534404314379574483476175147157207383312928130117927854301144790288284) * 10 ^ 70 +
        7429476901928104109574295835299532126230716402485559413845389318487360) * 10 ^ 70 +
        6563221277817833530028572740104992967594229526368605818491006539657510) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (310 - x)) = _
  rw [show 311 = 161 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (311 + x) *
        remainder6Coefficient1.coeff (311 - (311 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 311 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (311 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (311 - (311 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_311 :
    recurrence4Scalar1Exceptional.coeff 311 =
      -(((((242717942800001806443 * 10 ^ 70 +
        1575818202114623491492460839976639011844396434268672623711015805433634) * 10 ^ 70 +
        1015596140375634808060172269718425591965116277241772020960737484007062) * 10 ^ 70 +
        3958461305408208779865736462789041057057014593743856397416629013123373) * 10 ^ 70 +
        2425859286948798767276508723413168230410823751647103504504861248709184) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (311 - x)) = _
  rw [show 312 = 162 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (312 + x) *
        remainder6Coefficient1.coeff (312 - (312 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 312 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (312 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (312 - (312 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_312 :
    recurrence4Scalar1Exceptional.coeff 312 =
      (((((156204472350645393000 * 10 ^ 70 +
        6440686415172639354068660058843878303295420184085947064469605003626040) * 10 ^ 70 +
        6117139040132812041637888631716447084281696913171044612926633530031700) * 10 ^ 70 +
        9131186337131356313427720940847158061387853844960813337747666116462669) * 10 ^ 70 +
        9606732749932667001805992899418818722520005904337430293651280670556847) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (312 - x)) = _
  rw [show 313 = 163 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (313 + x) *
        remainder6Coefficient1.coeff (313 - (313 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 313 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (313 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (313 - (313 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_313 :
    recurrence4Scalar1Exceptional.coeff 313 =
      -(((((99252507037498162080 * 10 ^ 70 +
        4190747421235003703768896787155265410636630753868354237075559217081911) * 10 ^ 70 +
        4030708369425142581152544755068912752905049596335367000826001756365027) * 10 ^ 70 +
        0826619007130793065669009117925693361921476814891647708157621263331871) * 10 ^ 70 +
        3586791639646774479912335090317388314111286870803851995760896816521938) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (313 - x)) = _
  rw [show 314 = 164 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (314 + x) *
        remainder6Coefficient1.coeff (314 - (314 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 314 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (314 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (314 - (314 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_314 :
    recurrence4Scalar1Exceptional.coeff 314 =
      (((((62103865585272468164 * 10 ^ 70 +
        6443189326201000049640667616387247073032387328873934413448522050988345) * 10 ^ 70 +
        8684578190171410115676093466454746868440056477283198598907408496806092) * 10 ^ 70 +
        9270438855860190859648922588667752606045714212173008080236336153406064) * 10 ^ 70 +
        2454500309806612144722512824811719331417253530464562051864569618383316) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (314 - x)) = _
  rw [show 315 = 165 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (315 + x) *
        remainder6Coefficient1.coeff (315 - (315 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 315 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (315 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (315 - (315 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_315 :
    recurrence4Scalar1Exceptional.coeff 315 =
      -(((((38204150755834228461 * 10 ^ 70 +
        9526613086408022656642871854674171537332333013348768946691702155604901) * 10 ^ 70 +
        0026730525879697634504760533299525663800055939238484043686713723349267) * 10 ^ 70 +
        6352021906226013554263710164470929992872608443490894604133724882173170) * 10 ^ 70 +
        6320047289200127045236603352909006568124663469772292510824625291471886) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (315 - x)) = _
  rw [show 316 = 166 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (316 + x) *
        remainder6Coefficient1.coeff (316 - (316 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 316 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (316 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (316 - (316 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_316 :
    recurrence4Scalar1Exceptional.coeff 316 =
      (((((23082723850639689437 * 10 ^ 70 +
        8466517378319343115617727489841064795286428367814046848720699403031543) * 10 ^ 70 +
        0498633573177708568097222144650713454258242720651983465475561670674913) * 10 ^ 70 +
        6154295743554251819565310886178013881530132500343420908748497944341987) * 10 ^ 70 +
        3447935242349569314072407606188538038720858311800189840840638845044226) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (316 - x)) = _
  rw [show 317 = 167 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (317 + x) *
        remainder6Coefficient1.coeff (317 - (317 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 317 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (317 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (317 - (317 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_317 :
    recurrence4Scalar1Exceptional.coeff 317 =
      -(((((13690065170089101436 * 10 ^ 70 +
        9587330912313066577706307830606806724583824971803313753209873611219327) * 10 ^ 70 +
        0364783737919711710083745705389508424625460470312256770142815861190922) * 10 ^ 70 +
        8542365203559306704040498708883919987788628050823840680158924096704854) * 10 ^ 70 +
        5604051064813765079945898108713717115700833081367747126301088472825845) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (317 - x)) = _
  rw [show 318 = 168 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (318 + x) *
        remainder6Coefficient1.coeff (318 - (318 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 318 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (318 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (318 - (318 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_318 :
    recurrence4Scalar1Exceptional.coeff 318 =
      (((((7967879427533889931 * 10 ^ 70 +
        7089179331631790113133118721871533462905879394093602964185251000091950) * 10 ^ 70 +
        0420509298178286945974415375606305058455983150868371723647633319820339) * 10 ^ 70 +
        1048295067399009928424571391292123115258603919634227269125525116598423) * 10 ^ 70 +
        0295718864742276399545394466083462400082398677896422305696892891212509) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (318 - x)) = _
  rw [show 319 = 169 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (319 + x) *
        remainder6Coefficient1.coeff (319 - (319 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 319 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (319 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (319 - (319 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_319 :
    recurrence4Scalar1Exceptional.coeff 319 =
      -(((((4550392070168036549 * 10 ^ 70 +
        5390894950460536124012233292981214075320729966316359750554867493308157) * 10 ^ 70 +
        8503019642647439104165239211579682214746078956410303590098248828407265) * 10 ^ 70 +
        4716725063321841869749518993497022852675323097711389582047327475455253) * 10 ^ 70 +
        4423530055089197572733634218171818436013687274048144417129562546887613) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (319 - x)) = _
  rw [show 320 = 170 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (320 + x) *
        remainder6Coefficient1.coeff (320 - (320 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 320 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (320 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (320 - (320 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_320 :
    recurrence4Scalar1Exceptional.coeff 320 =
      (((((2549859712001211970 * 10 ^ 70 +
        2790344366645613191162198896347959200097765367680896912143143963717957) * 10 ^ 70 +
        9513280757318747186566832081527723029959591276277983538526768168542961) * 10 ^ 70 +
        6218342555934090992989182702897586505284321450359014996147962081104411) * 10 ^ 70 +
        8566376736030420138754909210051843022087854462722779171372991284826682) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (320 - x)) = _
  rw [show 321 = 171 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (321 + x) *
        remainder6Coefficient1.coeff (321 - (321 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 321 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (321 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (321 - (321 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_321 :
    recurrence4Scalar1Exceptional.coeff 321 =
      -(((((1402039320863081697 * 10 ^ 70 +
        8201422247783862671809552600905796518744010485908605167994409674311824) * 10 ^ 70 +
        6550842683027396320113299610256408611256359572118043256101572059534640) * 10 ^ 70 +
        7408554967714064980467372139181188357688880679412354621107669776466851) * 10 ^ 70 +
        0338641076197165185364542692449965010486920933400220143506804050782590) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (321 - x)) = _
  rw [show 322 = 172 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (322 + x) *
        remainder6Coefficient1.coeff (322 - (322 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 322 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (322 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (322 - (322 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_322 :
    recurrence4Scalar1Exceptional.coeff 322 =
      (((((756493178164995312 * 10 ^ 70 +
        0240461291682798059014608753383163734720596141721332943739081451936563) * 10 ^ 70 +
        0908907979151786103075187657399023476252197839038219413412353367166447) * 10 ^ 70 +
        0661924664176812691935052287315346573192440216588647568527570441696250) * 10 ^ 70 +
        1722062507867757134887835945261709946544830372109197888261364262899501) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (322 - x)) = _
  rw [show 323 = 173 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (323 + x) *
        remainder6Coefficient1.coeff (323 - (323 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 323 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (323 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (323 - (323 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_323 :
    recurrence4Scalar1Exceptional.coeff 323 =
      -(((((400568031792753592 * 10 ^ 70 +
        5434772750859483013692091906288148310013018074043940702616847363314642) * 10 ^ 70 +
        7400119744366185417343284391502904173116163058755370202001847580525773) * 10 ^ 70 +
        9379604303715262854006055225114171796786363975720438515847300508643161) * 10 ^ 70 +
        7612036738610891776150476308590667441122021765522810778767433213311702) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (323 - x)) = _
  rw [show 324 = 174 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (324 + x) *
        remainder6Coefficient1.coeff (324 - (324 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 324 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (324 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (324 - (324 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_324 :
    recurrence4Scalar1Exceptional.coeff 324 =
      (((((208158981236852749 * 10 ^ 70 +
        5668441537782538955510597630399834074310085338262597221703105428353652) * 10 ^ 70 +
        9748566674847213194089266308859289083951786206411328534184130806152586) * 10 ^ 70 +
        4470608377012910349963629860854162736463973631164800742205981440220217) * 10 ^ 70 +
        1121098173034473319101398442772794110500427661426668695427599145097458) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (324 - x)) = _
  rw [show 325 = 175 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (325 + x) *
        remainder6Coefficient1.coeff (325 - (325 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 325 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (325 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (325 - (325 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_325 :
    recurrence4Scalar1Exceptional.coeff 325 =
      -(((((106163386078011320 * 10 ^ 70 +
        0370238073885043601056149789266107833572351181167609605868980336574501) * 10 ^ 70 +
        0625554871116888936014234667956241056935239216437078570043268409795787) * 10 ^ 70 +
        6790355126676034273464168007418517236971347213771476971105214889851919) * 10 ^ 70 +
        0027710308875035360001727763198744958910351730265541576447251205873744) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (325 - x)) = _
  rw [show 326 = 176 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (326 + x) *
        remainder6Coefficient1.coeff (326 - (326 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 326 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (326 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (326 - (326 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_326 :
    recurrence4Scalar1Exceptional.coeff 326 =
      (((((53139523962106192 * 10 ^ 70 +
        9408166179569629101381087084709364566262320835293740989739159758649629) * 10 ^ 70 +
        3780239119735244247741842019385376996269305946725702620034218570038061) * 10 ^ 70 +
        5989452065517576473065738527496810812496328387818917771125813443837634) * 10 ^ 70 +
        7745526492997805162278686033551752827998953100543425044313630375223217) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (326 - x)) = _
  rw [show 327 = 177 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (327 + x) *
        remainder6Coefficient1.coeff (327 - (327 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 327 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (327 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (327 - (327 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_327 :
    recurrence4Scalar1Exceptional.coeff 327 =
      -(((((26104396111202684 * 10 ^ 70 +
        9390034878721959430342149708037670012865335178485014887092504964620385) * 10 ^ 70 +
        2595418085652573551792871876573963917949037946256484461342870901412549) * 10 ^ 70 +
        4337756252295291366844054510017085508149566166067231679154265492128445) * 10 ^ 70 +
        7828118543149930561205146608248515694931521422003799411761236511683060) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (327 - x)) = _
  rw [show 328 = 178 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (328 + x) *
        remainder6Coefficient1.coeff (328 - (328 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 328 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (328 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (328 - (328 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_328 :
    recurrence4Scalar1Exceptional.coeff 328 =
      (((((12584547503506720 * 10 ^ 70 +
        2430994209128921588251237811823982855095928249119551436183577231565651) * 10 ^ 70 +
        2583659979021762513013117604684944225661543665646651828921485834169606) * 10 ^ 70 +
        6205095659732421453970258472928655850590712405826622554965480572773159) * 10 ^ 70 +
        3103332092696735641559040715407524376748738926624414447026087227186254) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (328 - x)) = _
  rw [show 329 = 179 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (329 + x) *
        remainder6Coefficient1.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 329 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (329 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_329 :
    recurrence4Scalar1Exceptional.coeff 329 =
      -(((((5953148938636584 * 10 ^ 70 +
        2196866439399458493979521275817701004454013732798087859346535985217405) * 10 ^ 70 +
        0690607327248768710769595161151179205569199030854615131655350706491770) * 10 ^ 70 +
        5795243913779823234486939599011970316967922009114432132936723452139124) * 10 ^ 70 +
        0067092956473890522689438801300918476529023288995490032162852104431638) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (329 - x)) = _
  rw [show 330 = 180 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (330 + x) *
        remainder6Coefficient1.coeff (330 - (330 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 330 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (330 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (330 - (330 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_330 :
    recurrence4Scalar1Exceptional.coeff 330 =
      (((((2762974664185835 * 10 ^ 70 +
        3280589299365943319754986047739531548646555675936489901599775074261104) * 10 ^ 70 +
        7898342305447664103819600098442233324814323502681551288544076507716254) * 10 ^ 70 +
        6745597314894047936508078589282514221741910321683093809274856084167306) * 10 ^ 70 +
        5510240098938519906242384768871233464141769527437173962508757582573069) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (330 - x)) = _
  rw [show 331 = 181 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (331 + x) *
        remainder6Coefficient1.coeff (331 - (331 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 331 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (331 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (331 - (331 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_331 :
    recurrence4Scalar1Exceptional.coeff 331 =
      -(((((1257873391985578 * 10 ^ 70 +
        7415195492454484534411051176977632093824916145198417314142111152023830) * 10 ^ 70 +
        4853903677821543329239147118812619028122172663308777308256537643841942) * 10 ^ 70 +
        4386644005329059203020970792106973017146734430179663007609046509604143) * 10 ^ 70 +
        4711001714992844701726616713594461448634931669710071035682429745476570) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (331 - x)) = _
  rw [show 332 = 182 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (332 + x) *
        remainder6Coefficient1.coeff (332 - (332 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 332 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (332 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (332 - (332 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_332 :
    recurrence4Scalar1Exceptional.coeff 332 =
      (((((561565408960899 * 10 ^ 70 +
        6225653936230383527306411622600440513766816708323611012386135065955465) * 10 ^ 70 +
        6996081649867762061930046240107521455230707713239412830992875421979136) * 10 ^ 70 +
        8859676677122997402658000706092862819335973548700935758413291464429763) * 10 ^ 70 +
        4199574860600173590378887896509481184779989934862655047271854953006274) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (332 - x)) = _
  rw [show 333 = 183 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (333 + x) *
        remainder6Coefficient1.coeff (333 - (333 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 333 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (333 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (333 - (333 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_333 :
    recurrence4Scalar1Exceptional.coeff 333 =
      -(((((245749415296568 * 10 ^ 70 +
        8584487927957867550664728466085076187684241564797534481512661043722565) * 10 ^ 70 +
        3230723010510451050425494850717381857173911165760216762860442010020818) * 10 ^ 70 +
        6134311873739342963631582654840610826923006146868034136270994672318018) * 10 ^ 70 +
        6099285845618314507985324393275248829690598176754047763110802476156996) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (333 - x)) = _
  rw [show 334 = 184 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (334 + x) *
        remainder6Coefficient1.coeff (334 - (334 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 334 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (334 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (334 - (334 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_334 :
    recurrence4Scalar1Exceptional.coeff 334 =
      (((((105358767774819 * 10 ^ 70 +
        3250524118059118917279894424623424423533043950852396315988454319913491) * 10 ^ 70 +
        8002869947444412550278190409959004176184218065986012693497338146274839) * 10 ^ 70 +
        4287597393814704409263518406756640291826142692893181278881429843869975) * 10 ^ 70 +
        7186282193687244928451736315625057737472278046451911516726657152087685) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (334 - x)) = _
  rw [show 335 = 185 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (335 + x) *
        remainder6Coefficient1.coeff (335 - (335 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 335 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (335 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (335 - (335 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_335 :
    recurrence4Scalar1Exceptional.coeff 335 =
      -(((((44217395876239 * 10 ^ 70 +
        5793755513329290916964618617031785476082771864529492412051332336618911) * 10 ^ 70 +
        4056029662699271335336071414915817152507944474533722816923088997745793) * 10 ^ 70 +
        0892621535372815611551054706916102400309094557022032732232877287234669) * 10 ^ 70 +
        3885283844012189541690419663008331964587727116956276449108711683444299) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (335 - x)) = _
  rw [show 336 = 186 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (336 + x) *
        remainder6Coefficient1.coeff (336 - (336 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 336 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (336 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (336 - (336 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_336 :
    recurrence4Scalar1Exceptional.coeff 336 =
      (((((18145529242631 * 10 ^ 70 +
        8390066667775800286019772904036312317901483295587818470070583627833882) * 10 ^ 70 +
        4279793392354934445147121799553566322817190844668531491466430885270926) * 10 ^ 70 +
        4169168317134160420600344530372912304429051448702870006912636585150773) * 10 ^ 70 +
        1125252736157008651178127583491406417688702829506344194821195986359769) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (336 - x)) = _
  rw [show 337 = 187 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (337 + x) *
        remainder6Coefficient1.coeff (337 - (337 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 337 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (337 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (337 - (337 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_337 :
    recurrence4Scalar1Exceptional.coeff 337 =
      -(((((7269098397812 * 10 ^ 70 +
        7164668445287887752627290013920385624217843948410033432955831540695023) * 10 ^ 70 +
        8583067513275800467069585907746446494566820745943754599300761581711090) * 10 ^ 70 +
        8362624741834310166546906501715112654514926252089358698356418774271595) * 10 ^ 70 +
        6566247508447293005398864090600098819494687200613723158242336077814845) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (337 - x)) = _
  rw [show 338 = 188 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (338 + x) *
        remainder6Coefficient1.coeff (338 - (338 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 338 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (338 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (338 - (338 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_338 :
    recurrence4Scalar1Exceptional.coeff 338 =
      (((((2835571529763 * 10 ^ 70 +
        9198512226937557623587943608345117297578290280935640061400166753764159) * 10 ^ 70 +
        0289389408391377695636159065758104121007101017327449121006717518291437) * 10 ^ 70 +
        6683285040455057250846138014682284970876323120843441120604413377150368) * 10 ^ 70 +
        6395960397259160929326010755172838269051430707153618006200422978645171) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (338 - x)) = _
  rw [show 339 = 189 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (339 + x) *
        remainder6Coefficient1.coeff (339 - (339 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 339 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (339 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (339 - (339 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_339 :
    recurrence4Scalar1Exceptional.coeff 339 =
      -(((((1072894083893 * 10 ^ 70 +
        5919517736551884360120994232796108584584874369129640239843257805046089) * 10 ^ 70 +
        0260560649797794947158644115196338749532179544678127177687189527799859) * 10 ^ 70 +
        2061281271952352756740710157701688978678946953537327233591738498585208) * 10 ^ 70 +
        8075672974520158041251686056418508303652116969098154321338291348479359) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (339 - x)) = _
  rw [show 340 = 190 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (340 + x) *
        remainder6Coefficient1.coeff (340 - (340 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 340 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (340 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (340 - (340 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_340 :
    recurrence4Scalar1Exceptional.coeff 340 =
      (((((391263472552 * 10 ^ 70 +
        6840309299550560765737759660573409457554796898367163948215843859496611) * 10 ^ 70 +
        3404747403989551253199324693459933940959674373937477149571028058348477) * 10 ^ 70 +
        8320684859251505632467224221122207586073973568818144313302159417950358) * 10 ^ 70 +
        6669585102499578821378912344032494867456581866288779660733816519659891) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (340 - x)) = _
  rw [show 341 = 191 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (341 + x) *
        remainder6Coefficient1.coeff (341 - (341 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 341 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (341 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (341 - (341 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_341 :
    recurrence4Scalar1Exceptional.coeff 341 =
      -(((((136016437443 * 10 ^ 70 +
        8203163958389375828414498197869187927183444360917707401862944257634698) * 10 ^ 70 +
        2982533738135391381352794825636145835338949217996920955244847429726174) * 10 ^ 70 +
        0963997746372827834992080909453749224002373186611401374016123288242351) * 10 ^ 70 +
        1409554225011125316077064924880044061434088969894375953320562614506560) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (341 - x)) = _
  rw [show 342 = 192 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (342 + x) *
        remainder6Coefficient1.coeff (342 - (342 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 342 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (342 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (342 - (342 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_342 :
    recurrence4Scalar1Exceptional.coeff 342 =
      (((((44137362233 * 10 ^ 70 +
        7279560665855231247860414135313071915112177111133333816455333430389240) * 10 ^ 70 +
        4966643421199851257425126896608744200212960492903887315004726647056882) * 10 ^ 70 +
        3361948344290779375704253887587186956463137864157777555801987008617624) * 10 ^ 70 +
        8888730414303717314913571571247234895903415219505970250132844024654030) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (342 - x)) = _
  rw [show 343 = 193 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (343 + x) *
        remainder6Coefficient1.coeff (343 - (343 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 343 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (343 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (343 - (343 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_343 :
    recurrence4Scalar1Exceptional.coeff 343 =
      -(((((12758950627 * 10 ^ 70 +
        6685099934271284211682793017366095524035682762615940217377516393924915) * 10 ^ 70 +
        7540782584018651431382202643915201851769769667025581873699657343625977) * 10 ^ 70 +
        2724555244340923839404527319812484262714013170600256511028244206604088) * 10 ^ 70 +
        8865511195645936170865428501044410909978652393127807159721522844713085) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (343 - x)) = _
  rw [show 344 = 194 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (344 + x) *
        remainder6Coefficient1.coeff (344 - (344 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 344 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (344 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (344 - (344 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_344 :
    recurrence4Scalar1Exceptional.coeff 344 =
      (((((2852130644 * 10 ^ 70 +
        0033897796251122078662744628955316119009158255994625555238261306499876) * 10 ^ 70 +
        0850435598013858875739622818464673455267996206541314657292745462828473) * 10 ^ 70 +
        0781637006829094959807151846645045697159691559127417126712440499914186) * 10 ^ 70 +
        9614248691198343232686693662389088928094157354752655927566426373316769) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (344 - x)) = _
  rw [show 345 = 195 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (345 + x) *
        remainder6Coefficient1.coeff (345 - (345 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 345 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (345 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (345 - (345 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_345 :
    recurrence4Scalar1Exceptional.coeff 345 =
      -(((((134129184 * 10 ^ 70 +
        6938689381956545694589817559757072228444795704769774172600875134349138) * 10 ^ 70 +
        0320011454565257176405945262439477622104366484008507314435790396329478) * 10 ^ 70 +
        2675028491498466767030796909339877021246567193570108942933921138157678) * 10 ^ 70 +
        7392721566326391030650757623702323101924026524343560255692779673418545) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (345 - x)) = _
  rw [show 346 = 196 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (346 + x) *
        remainder6Coefficient1.coeff (346 - (346 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 346 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (346 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (346 - (346 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_346 :
    recurrence4Scalar1Exceptional.coeff 346 =
      -(((((386074680 * 10 ^ 70 +
        8326761229363364358410285664767195514123369825231465037351795060161204) * 10 ^ 70 +
        5086880137083586512073191146809006083669141336964587826553914520454634) * 10 ^ 70 +
        9209449705389881300345350403783948701852943588632909477562537723721373) * 10 ^ 70 +
        4052136486195432295325348339927191651639863615067879704360934926424160) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (346 - x)) = _
  rw [show 347 = 197 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (347 + x) *
        remainder6Coefficient1.coeff (347 - (347 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 347 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (347 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (347 - (347 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_347 :
    recurrence4Scalar1Exceptional.coeff 347 =
      (((((342446240 * 10 ^ 70 +
        4364834462131661387133787953058672659390745999195575244078514731566649) * 10 ^ 70 +
        2740562305216714024227306708323949908388093937818645966374527442160158) * 10 ^ 70 +
        9334906979222403615108577431965674296799175295221016359711830660601563) * 10 ^ 70 +
        9650540235323889444411232999952468236609135261987700714505412609365136) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (347 - x)) = _
  rw [show 348 = 198 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (348 + x) *
        remainder6Coefficient1.coeff (348 - (348 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 348 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (348 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (348 - (348 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_348 :
    recurrence4Scalar1Exceptional.coeff 348 =
      -(((((215678303 * 10 ^ 70 +
        9777473447671772314244034350036973666965961515641609017465245053698043) * 10 ^ 70 +
        5799911238764854976664067706003991600738608394208134401657164973527628) * 10 ^ 70 +
        3779264897175951488963779243018642080386946880936282272541432806240780) * 10 ^ 70 +
        6149235103241501743068376372545823810419464466330719492951948708947419) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (348 - x)) = _
  rw [show 349 = 199 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (349 + x) *
        remainder6Coefficient1.coeff (349 - (349 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 349 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (349 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (349 - (349 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_349 :
    recurrence4Scalar1Exceptional.coeff 349 =
      (((((118461367 * 10 ^ 70 +
        4546875603904141994517477443148439747637453429812109727699110981100078) * 10 ^ 70 +
        2458691520212435483273953156524443466527884073717184511355146573227192) * 10 ^ 70 +
        5905558435295403376917989156720153624108928900779002887929255898689401) * 10 ^ 70 +
        1019021294172732555083686268450547737393378487175875013186441925936098) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (349 - x)) = _
  rw [show 350 = 200 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (350 + x) *
        remainder6Coefficient1.coeff (350 - (350 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 350 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (350 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (350 - (350 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_350 :
    recurrence4Scalar1Exceptional.coeff 350 =
      -(((((60202043 * 10 ^ 70 +
        9095907681712282596043604944473942045342193916962099575137029055690208) * 10 ^ 70 +
        3881097910912582038985518223275296317831946078830559261998943299658702) * 10 ^ 70 +
        7672609086425176061764950726288092772853611640983481774953156029192651) * 10 ^ 70 +
        3810487010144647357624678430769993856558573002594051221064125149794207) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (350 - x)) = _
  rw [show 351 = 201 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (351 + x) *
        remainder6Coefficient1.coeff (351 - (351 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 351 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (351 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (351 - (351 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_351 :
    recurrence4Scalar1Exceptional.coeff 351 =
      (((((29019112 * 10 ^ 70 +
        8236094584912702554054129083307885105726797965373527045365828031501260) * 10 ^ 70 +
        2191168658319273844950867277564803116212166837400167871676040426481561) * 10 ^ 70 +
        0022309222476124904784338718242800587125922356181259455835243108888683) * 10 ^ 70 +
        4845770787784585062581549644660399284648953619987943507260365822536353) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (351 - x)) = _
  rw [show 352 = 202 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (352 + x) *
        remainder6Coefficient1.coeff (352 - (352 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 352 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (352 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (352 - (352 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_352 :
    recurrence4Scalar1Exceptional.coeff 352 =
      -(((((13431312 * 10 ^ 70 +
        2169791362285262862684523847312120802085199379537256787244525205733680) * 10 ^ 70 +
        3083619150777119834700121581815759186928855832728407971652578491822701) * 10 ^ 70 +
        1672240765987657188467757653006559460505606483794690604073477122271450) * 10 ^ 70 +
        9932374342750154151820939913717290773241751771004360006112608970598966) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (352 - x)) = _
  rw [show 353 = 203 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (353 + x) *
        remainder6Coefficient1.coeff (353 - (353 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 353 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (353 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (353 - (353 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_353 :
    recurrence4Scalar1Exceptional.coeff 353 =
      (((((6008193 * 10 ^ 70 +
        2156482070595203958347337044485188556609487538767851299171594244454728) * 10 ^ 70 +
        0847364188666241559419072028331455574400075224413406088925254852402281) * 10 ^ 70 +
        9562289107816530706651236539482472646507582916737984147595877557861431) * 10 ^ 70 +
        5986098306703867870585279749139157344076841982781236738493543182770934) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (353 - x)) = _
  rw [show 354 = 204 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (354 + x) *
        remainder6Coefficient1.coeff (354 - (354 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 354 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (354 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (354 - (354 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_354 :
    recurrence4Scalar1Exceptional.coeff 354 =
      -(((((2606586 * 10 ^ 70 +
        5181418858689932300749061379713570272405123403318797526933985685275438) * 10 ^ 70 +
        6684023555714456459265970650910506218718954849730375008180450060584539) * 10 ^ 70 +
        4899371014005477470385411710964983518599004562406747364932178536129771) * 10 ^ 70 +
        8703479743191155246281942862019374597094053550743892628411122366497428) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (354 - x)) = _
  rw [show 355 = 205 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (355 + x) *
        remainder6Coefficient1.coeff (355 - (355 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 355 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (355 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (355 - (355 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_355 :
    recurrence4Scalar1Exceptional.coeff 355 =
      (((((1098591 * 10 ^ 70 +
        5460985922879995002400078972677436223283527945625605744053604621132196) * 10 ^ 70 +
        9207715854873814302814953558989168654025912402782869228025652289207209) * 10 ^ 70 +
        3796918401187225038903833114127612063398349033736512220106581761053503) * 10 ^ 70 +
        6793182763702263062407135304930226872872193016595086643976117681497351) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (355 - x)) = _
  rw [show 356 = 206 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (356 + x) *
        remainder6Coefficient1.coeff (356 - (356 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 356 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (356 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (356 - (356 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_356 :
    recurrence4Scalar1Exceptional.coeff 356 =
      -(((((450044 * 10 ^ 70 +
        9136662716715035670981319248516553452052882658283906576646847202977817) * 10 ^ 70 +
        9579891767048447719844715990632951613651459002596569809903597361053703) * 10 ^ 70 +
        3774085894388052383529783952582849694505220326087337011744420462833392) * 10 ^ 70 +
        2411409134248613128599410885907500905587995966339949617692690619146412) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (356 - x)) = _
  rw [show 357 = 207 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (357 + x) *
        remainder6Coefficient1.coeff (357 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 357 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (357 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (357 - (357 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_357 :
    recurrence4Scalar1Exceptional.coeff 357 =
      (((((179126 * 10 ^ 70 +
        9485946443165851390648229997421436072289862405455539847644462661518293) * 10 ^ 70 +
        7477128531482701958669426401655493511008473996401361535868830692427418) * 10 ^ 70 +
        9540858810634730331322720073320125916791045803782819365704377386678245) * 10 ^ 70 +
        1634020142834145212518315201569929675789674844624419821598695030072253) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (357 - x)) = _
  rw [show 358 = 208 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (358 + x) *
        remainder6Coefficient1.coeff (358 - (358 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 358 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (358 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (358 - (358 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_358 :
    recurrence4Scalar1Exceptional.coeff 358 =
      -(((((69186 * 10 ^ 70 +
        7448872318072538143037376269954150372117081316514308950131781301697176) * 10 ^ 70 +
        8891404747046768414733452310237355716857306672079086693135135364406034) * 10 ^ 70 +
        5857663059164905060139614343887547104716329010415737867833602904567178) * 10 ^ 70 +
        5565674995362664676291443299362378083074551509444403705012644591237900) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (358 - x)) = _
  rw [show 359 = 209 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (359 + x) *
        remainder6Coefficient1.coeff (359 - (359 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 359 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (359 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (359 - (359 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_359 :
    recurrence4Scalar1Exceptional.coeff 359 =
      (((((25876 * 10 ^ 70 +
        1893852918619440809798006844418791754863804000213191434080190532901778) * 10 ^ 70 +
        7973151461714970706540538269895538223901286031957833350940301052875236) * 10 ^ 70 +
        1152670530020932380161574400641438914226337762419718341794464335752056) * 10 ^ 70 +
        3367287656243204398444148431752666825437554230611518789482218653616145) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (359 - x)) = _
  rw [show 360 = 210 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (360 + x) *
        remainder6Coefficient1.coeff (360 - (360 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 360 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (360 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (360 - (360 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_360 :
    recurrence4Scalar1Exceptional.coeff 360 =
      -(((((9338 * 10 ^ 70 +
        3261254314628054523021829557110196966750550057293192522769364739612186) * 10 ^ 70 +
        8310327363483544705881590126530024630876934343909808514164284026840074) * 10 ^ 70 +
        9256095209076598469846314005563918024396934472658396646016602089172793) * 10 ^ 70 +
        9533427029520305650079858446883736472397384314884034660743374795620946) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (360 - x)) = _
  rw [show 361 = 211 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (361 + x) *
        remainder6Coefficient1.coeff (361 - (361 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 361 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (361 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (361 - (361 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_361 :
    recurrence4Scalar1Exceptional.coeff 361 =
      (((((3233 * 10 ^ 70 +
        2874210103881027202435304172486999140522753686800794834093130427224629) * 10 ^ 70 +
        6955715443984568546916196254241761558777276705273247687643812471933075) * 10 ^ 70 +
        0280608966501642660892481681576182888568259484256220418585513546888178) * 10 ^ 70 +
        9929899691360070199697754920959883790443390776543396369806393848644640) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (361 - x)) = _
  rw [show 362 = 212 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (362 + x) *
        remainder6Coefficient1.coeff (362 - (362 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 362 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (362 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (362 - (362 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_362 :
    recurrence4Scalar1Exceptional.coeff 362 =
      -(((((1063 * 10 ^ 70 +
        5249056201281744760275717010896938634479590212223120835382222038239118) * 10 ^ 70 +
        1323221366865851445301278645897570206584945349206828486888072110298191) * 10 ^ 70 +
        2720687165390902890041305433567684750193409268773753376808211137991309) * 10 ^ 70 +
        7824829457818677613808078215990115921414450976275516421436633742651690) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (362 - x)) = _
  rw [show 363 = 213 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (363 + x) *
        remainder6Coefficient1.coeff (363 - (363 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 363 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (363 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (363 - (363 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_363 :
    recurrence4Scalar1Exceptional.coeff 363 =
      (((((326 * 10 ^ 70 +
        2025582543476069575931930355015581854831193984081890350188596356066913) * 10 ^ 70 +
        6722033192139229516541136419497651498555966850403567666338674439311511) * 10 ^ 70 +
        7721795513803744628444009714720029902814352530872333141472114707397191) * 10 ^ 70 +
        2610904834625079692251189722910848274658588102428057854799991462315045) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (363 - x)) = _
  rw [show 364 = 214 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (364 + x) *
        remainder6Coefficient1.coeff (364 - (364 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 364 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (364 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (364 - (364 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_364 :
    recurrence4Scalar1Exceptional.coeff 364 =
      -(((((89 * 10 ^ 70 +
        5510138895895699561640806266743409114250294054727159921425966696399820) * 10 ^ 70 +
        7323268306238071928567036198930738148200508883728122747792734705553379) * 10 ^ 70 +
        3290337871432009694642902365599699135736323252270760944480287827937228) * 10 ^ 70 +
        5534715584505578378486114263528814656995980157896655032913652308697441) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (364 - x)) = _
  rw [show 365 = 215 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (365 + x) *
        remainder6Coefficient1.coeff (365 - (365 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 365 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (365 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (365 - (365 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_365 :
    recurrence4Scalar1Exceptional.coeff 365 =
      (((((19 * 10 ^ 70 +
        5325134345780802259849257304341058374711823886251328758199945287267524) * 10 ^ 70 +
        3193805410022875561909885305412865121647881236862705230441964498249422) * 10 ^ 70 +
        8994589320383403692715072260644332917204908272082804259607195847663610) * 10 ^ 70 +
        7564588044708827458933564989162347807085621921130152319621749474874741) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (365 - x)) = _
  rw [show 366 = 216 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (366 + x) *
        remainder6Coefficient1.coeff (366 - (366 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 366 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (366 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (366 - (366 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_366 :
    recurrence4Scalar1Exceptional.coeff 366 =
      -(((((1 * 10 ^ 70 +
        5128743315695287713186368569607847553104734850984514545839318544733238) * 10 ^ 70 +
        5566773276648736786958341400747604323902836923812983233584144518972657) * 10 ^ 70 +
        0939455256300665367624253854943671232711897177353676404095983836613315) * 10 ^ 70 +
        3539265449626840701484939590754562872750869874615410904351376087105703) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (366 - x)) = _
  rw [show 367 = 217 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (367 + x) *
        remainder6Coefficient1.coeff (367 - (367 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 367 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (367 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (367 - (367 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_367 :
    recurrence4Scalar1Exceptional.coeff 367 =
      -(((((1 * 10 ^ 70 +
        7796832809661783847714579448735735517376209843099687846041355565111358) * 10 ^ 70 +
        7459599795620751968127381267911769186695313691905600050535830326777902) * 10 ^ 70 +
        5839851135007745284361198683837527809042181781033712836330187733334470) * 10 ^ 70 +
        0445870928862988515864099491404757144933836561258226087751573321475979) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (367 - x)) = _
  rw [show 368 = 218 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (368 + x) *
        remainder6Coefficient1.coeff (368 - (368 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 368 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (368 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (368 - (368 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_368 :
    recurrence4Scalar1Exceptional.coeff 368 =
      (((((1 * 10 ^ 70 +
        6004845870171700904850279026247375560859055817785568484024066045202399) * 10 ^ 70 +
        3995591748570273112208135796693612865655083851281976356218052451535252) * 10 ^ 70 +
        8916843113738174091558420933085087577774854130798703319839323349361591) * 10 ^ 70 +
        3402989592753341141620469367857974823094121997901004666264395935296103) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (368 - x)) = _
  rw [show 369 = 219 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (369 + x) *
        remainder6Coefficient1.coeff (369 - (369 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 369 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (369 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (369 - (369 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_369 :
    recurrence4Scalar1Exceptional.coeff 369 =
      -((((9673735015895763794632328272203612405270846227820966138073634843822976 * 10 ^ 70 +
        2049108783558268270207866713731327661269715578942194610041372565953074) * 10 ^ 70 +
        0732664115778743503476385214194962824072582260766534087560581492504446) * 10 ^ 70 +
        4462129441393284945401573933438415271331950723178873658703164155274414) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (369 - x)) = _
  rw [show 370 = 220 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (370 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (370 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_370 :
    recurrence4Scalar1Exceptional.coeff 370 =
      ((((5060295351764261427115721359061479645209915341772905547136019275992204 * 10 ^ 70 +
        8442783638669295920761111449853293157219898414232487344229264670168633) * 10 ^ 70 +
        5538734989504458187514829822757808664449809407491691780364741932345929) * 10 ^ 70 +
        8712719440515873642454626239925172004044942907564060839527926579269663) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (370 - x)) = _
  rw [show 371 = 221 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (371 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (371 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_371 :
    recurrence4Scalar1Exceptional.coeff 371 =
      -((((2450400881246336126743943643431664173417710899428042033916140698749456 * 10 ^ 70 +
        9946199170780872530248039448937928500110627772608352060491247081088076) * 10 ^ 70 +
        0473670923988825520531427804804183406877470439457645536384787950750827) * 10 ^ 70 +
        9432766920223989460841533382753035690463352239730442219543622464658801) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (371 - x)) = _
  rw [show 372 = 222 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 20 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (372 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (372 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_372 :
    recurrence4Scalar1Exceptional.coeff 372 =
      ((((1128374236491658342061114212005907551418260129795465043282151805073601 * 10 ^ 70 +
        7510777008297573843917174816036828269706340488565291171650962807088257) * 10 ^ 70 +
        9682262072898298983269795295882784257377153683906687043768220423865471) * 10 ^ 70 +
        8160709174987997845208596579433932344034156464304783448875984192709744) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (372 - x)) = _
  rw [show 373 = 223 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 19 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (373 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (373 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_373 :
    recurrence4Scalar1Exceptional.coeff 373 =
      -((((500201204403585630359838139518939424883766000400478289888301618757444 * 10 ^ 70 +
        7546249909292678433312651975514256414816859550055347068716537243890618) * 10 ^ 70 +
        3145020542686121055295930183164361346441962085704570834161674001172990) * 10 ^ 70 +
        2033403573956889733330340905907866098571223608424349843581209981879866) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (373 - x)) = _
  rw [show 374 = 224 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 18 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (374 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (374 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_374 :
    recurrence4Scalar1Exceptional.coeff 374 =
      ((((214626093688518059438017211451530616657489872125541398892544544249912 * 10 ^ 70 +
        4576067261154120758273474806685402033542399263019988723370754003801915) * 10 ^ 70 +
        3196748643701608694902520570804552519985173925887817191893154037455573) * 10 ^ 70 +
        6706808140254365787714717351658378087401531468193980452257485958522363) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (374 - x)) = _
  rw [show 375 = 225 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 17 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (375 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (375 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_375 :
    recurrence4Scalar1Exceptional.coeff 375 =
      -((((89299701045799645013895468969660524328668125271682754989055872290012 * 10 ^ 70 +
        2989095564442020552645489084930162456059773195897549406215503093909614) * 10 ^ 70 +
        1615003906534050443274040385126199024847295611649731582823265139404696) * 10 ^ 70 +
        8586347043146032292818735347335464887615979352652456692000845036850997) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (375 - x)) = _
  rw [show 376 = 226 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 16 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (376 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (376 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_376 :
    recurrence4Scalar1Exceptional.coeff 376 =
      ((((36014924033741463364435427390356483301658719124580542689601701568791 * 10 ^ 70 +
        4377557690453167106962876169440487961064199880597698931588614237843762) * 10 ^ 70 +
        2597430390390391864474383729783932968183376711755192631669864644334666) * 10 ^ 70 +
        3435890922387900843970758173151993729554340617622586746181429715970754) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (376 - x)) = _
  rw [show 377 = 227 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 15 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (377 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (377 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_377 :
    recurrence4Scalar1Exceptional.coeff 377 =
      -((((14053253501468797426241601724513341651014841574569634773220900379381 * 10 ^ 70 +
        4864380470454688229279859565939545569018529639552395446388733961060342) * 10 ^ 70 +
        6990017508230490798738310403025295109312089891194811356287447274808301) * 10 ^ 70 +
        6760413150722463550932057366422804461097395771445641817185323899321181) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (377 - x)) = _
  rw [show 378 = 228 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 14 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (378 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (378 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_378 :
    recurrence4Scalar1Exceptional.coeff 378 =
      ((((5289420272725199184226421489904075992044184223183230667215659746936 * 10 ^ 70 +
        8975722493132312838108676238438280154450807757839784187838963782160650) * 10 ^ 70 +
        5253189455069377848246083646042519772625227887876599739842909934957400) * 10 ^ 70 +
        4384528097780627009770820349876646828331567998087103254796062370511412) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (378 - x)) = _
  rw [show 379 = 229 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 13 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (379 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (379 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_379 :
    recurrence4Scalar1Exceptional.coeff 379 =
      -((((1912017810631492468323058372591987731642076648082403539931707620080 * 10 ^ 70 +
        6273807964601144064329395014748613100369854905811501311217489682645839) * 10 ^ 70 +
        7406009621769920956495864647697609736729792913783295007246367062457459) * 10 ^ 70 +
        9491088791073373212520388204475895338171533311658300068768500749433490) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (379 - x)) = _
  rw [show 380 = 230 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 12 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (380 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (380 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_380 :
    recurrence4Scalar1Exceptional.coeff 380 =
      ((((659734121039728085180097221952101661336647704624497346323990998735 * 10 ^ 70 +
        1188998150132435118925782612491729617728755550989358440527050048878806) * 10 ^ 70 +
        0737536064283986820689901586774929977113471751937943572997911743070950) * 10 ^ 70 +
        4459554628328935814539740938716358198790557948944846812812386611537137) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (380 - x)) = _
  rw [show 381 = 231 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 11 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (381 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (381 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_381 :
    recurrence4Scalar1Exceptional.coeff 381 =
      -((((215319689293408322001758653740023008124377095802080510214547200234 * 10 ^ 70 +
        3584005357379339135248089170966200370483713270102387077009161333282830) * 10 ^ 70 +
        8849344127181712224775288812480393377417500255841415470113801310724236) * 10 ^ 70 +
        4737136135391745735981421797860706551768489271017424201768839561925383) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (381 - x)) = _
  rw [show 382 = 232 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 10 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (382 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (382 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_382 :
    recurrence4Scalar1Exceptional.coeff 382 =
      ((((65490488871895209253048086667787864506020495951695019152158882907 * 10 ^ 70 +
        1589160243980865769373071388437149788723598917945921228309087443025178) * 10 ^ 70 +
        3556095096093366551183209434852477485560008741546849347421350915746429) * 10 ^ 70 +
        8910078003939086557890000724332326231024309016025536666425337499648759) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (382 - x)) = _
  rw [show 383 = 233 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 9 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
