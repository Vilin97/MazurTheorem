/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Exceptional coefficient convolution

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

theorem recurrence5Scalar0Exceptional_coeff_0 :
    recurrence5Scalar0Exceptional.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_1 :
    recurrence5Scalar0Exceptional.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_2 :
    recurrence5Scalar0Exceptional.coeff 2 =
      -((538000971000222526023099986872709245460965839709009246890 * 10 ^ 70 +
        5914668940727449095618428256487521505390691735831997868913614705139712) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_3 :
    recurrence5Scalar0Exceptional.coeff 3 =
      ((3617506695558775387638654376070688667426555733514652752458064 * 10 ^ 70 +
        3516342332940159548117154844687965247214767964349635282427593398947840) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_4 :
    recurrence5Scalar0Exceptional.coeff 4 =
      -((6699034275103313356815201423867427782629190598396949183901124269 * 10 ^ 70 +
        1110624575690006187557888489738127669865544766170693701416965750877696) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_5 :
    recurrence5Scalar0Exceptional.coeff 5 =
      -((3653220561713706855103240485869352463366773356620649940127230780325 * 10 ^ 70 +
        4590478004418990190515830997895892017902258334763746262135060444474624) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_6 :
    recurrence5Scalar0Exceptional.coeff 6 =
      (((3 * 10 ^ 70 +
        3768552033177016279832190430990478296088024345132460163586850203927423) * 10 ^ 70 +
        0884737422108211693482334990415333842620748732859908243228756685911264) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_7 :
    recurrence5Scalar0Exceptional.coeff 7 =
      -(((5864 * 10 ^ 70 +
        7710879988983015271644594812299220267344301860405400300154119623673601) * 10 ^ 70 +
        1227670080803979943531886184036855529530669879314202104993063723418976) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_8 :
    recurrence5Scalar0Exceptional.coeff 8 =
      (((5066226 * 10 ^ 70 +
        7993987427972346832851552501891333049799747413473808455865029116187903) * 10 ^ 70 +
        2346340290384469090773484789549019007274798506868140231788401244116176) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_9 :
    recurrence5Scalar0Exceptional.coeff 9 =
      -(((2200165667 * 10 ^ 70 +
        3353861575373893620838243080896701055012391647871764129893071484755234) * 10 ^ 70 +
        6417573856162263213679379744986105658291207771721047768368325431478128) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_10 :
    recurrence5Scalar0Exceptional.coeff 10 =
      (((276527202373 * 10 ^ 70 +
        1562962866431948933644148051463618488167600959673613581653516203814650) * 10 ^ 70 +
        6228271664169954634000726708472111591473626951746121225510443957801632) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_11 :
    recurrence5Scalar0Exceptional.coeff 11 =
      (((180684372346260 * 10 ^ 70 +
        5406121072172603055148901972991276543500608960286617814622817568771923) * 10 ^ 70 +
        6904455596995797811807451952194570256697673362838909861118100493360412) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_12 :
    recurrence5Scalar0Exceptional.coeff 12 =
      -(((179579990156086408 * 10 ^ 70 +
        3998539696821475469186885522166655518281021635379471467400613352830030) * 10 ^ 70 +
        1267155405289642675777852927315043773326854324490337096034108883684000) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_13 :
    recurrence5Scalar0Exceptional.coeff 13 =
      (((163289835815767154124 * 10 ^ 70 +
        9452632346451610881302173413352782087928967813764353730889654092829658) * 10 ^ 70 +
        7216576741913544341647487689721995398675370794255810367814657304618704) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_14 :
    recurrence5Scalar0Exceptional.coeff 14 =
      -(((115873763077851828110317 * 10 ^ 70 +
        4965122081691287834015992627630497053202197073712485752726928603183958) * 10 ^ 70 +
        2296204846614804174373995062953352279209407717210445155390056141193340) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_15 :
    recurrence5Scalar0Exceptional.coeff 15 =
      (((52489659643440519367059318 * 10 ^ 70 +
        2133136509790277109600109440354657308673903933599310692431449096103260) * 10 ^ 70 +
        6892466301626458082509814417051689156921919984081476104975936251125668) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_16 :
    recurrence5Scalar0Exceptional.coeff 16 =
      -(((13831323499198478770936354899 * 10 ^ 70 +
        3312353411257484007593964321014883520336760336236413095154209775498405) * 10 ^ 70 +
        8574140169845363902494573197175609942302095711058122049254268111232628) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_17 :
    recurrence5Scalar0Exceptional.coeff 17 =
      (((936850284944755624462024749833 * 10 ^ 70 +
        9092071642342065373637953531246609479511522221176028488352056287717995) * 10 ^ 70 +
        1177116416803022591680157054615569190668073847356200589047407820678716) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_18 :
    recurrence5Scalar0Exceptional.coeff 18 =
      (((1244485000916126334934579976428467 * 10 ^ 70 +
        3135020951457323166301293054357906837971062244644325437710966738607249) * 10 ^ 70 +
        5603993186678067138045795020330204076037594118135067049541303059605740) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_19 :
    recurrence5Scalar0Exceptional.coeff 19 =
      -(((1060205822275267879667310996093696166 * 10 ^ 70 +
        3127322816703293884690011470246595902144452232068775897954525576142205) * 10 ^ 70 +
        5225098674691851556038011381427228396359022235969930482035582639665524) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_20 :
    recurrence5Scalar0Exceptional.coeff 20 =
      (((619590058863651411553223231229187044665 * 10 ^ 70 +
        1151509663967371639948452991309845809862836723026895069099620102200327) * 10 ^ 70 +
        4302883703598019488572731799265053810166687013361267788585251881819160) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_21 :
    recurrence5Scalar0Exceptional.coeff 21 =
      -(((271199866147298166073225229775392534502050 * 10 ^ 70 +
        7977589290892998179328257988532444803861434328636656953833996413557399) * 10 ^ 70 +
        6497530098658128065958546186280929661832524625086842477986085873725841) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_22 :
    recurrence5Scalar0Exceptional.coeff 22 =
      (((81080387603024936528036946303101554666763192 * 10 ^ 70 +
        4284913739250858390767852219782763667635311998075422088537957002838348) * 10 ^ 70 +
        6233080168951918563793616683762059503655714766228095525720872722551112) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_23 :
    recurrence5Scalar0Exceptional.coeff 23 =
      -(((11341995685042719015187743107499671011865285115 * 10 ^ 70 +
        2634786580072517599897140809030936711506472121321875109658267188657470) * 10 ^ 70 +
        6904036258355055063212050450801942401988162356485962076891209317259858) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_24 :
    recurrence5Scalar0Exceptional.coeff 24 =
      -(((3282511049652482731533783287758974515956488573501 * 10 ^ 70 +
        0685691895641960761554391745497812446917487624765916534739418047853431) * 10 ^ 70 +
        8132724890153811153225689832787160600885916018186410345950977574537385) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_25 :
    recurrence5Scalar0Exceptional.coeff 25 =
      (((2862072889068071674210045255727970842028186246089007 * 10 ^ 70 +
        5916039940795999000561858422640961404659354530185412848931489759541152) * 10 ^ 70 +
        7040024386434664980561118997405685132037513193865627487010284959691062) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_26 :
    recurrence5Scalar0Exceptional.coeff 26 =
      -(((1126985691976915644451624797610203436375417556913890998 * 10 ^ 70 +
        7529612570741438986802925737922872951692179935836443987320753657182389) * 10 ^ 70 +
        0351661836812330999301508973858672522020387884260468952964502282792004) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_27 :
    recurrence5Scalar0Exceptional.coeff 27 =
      (((314965039712125468008125860861616961576275700367694368366 * 10 ^ 70 +
        6317446253764715110763031523636336255568059379821285714500440222534359) * 10 ^ 70 +
        2870928367006208703795552420409928752093936460260891719166040712029328) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_28 :
    recurrence5Scalar0Exceptional.coeff 28 =
      -(((68588353936599551484828428397700076609126591924479806798405 * 10 ^ 70 +
        5217248654270375757241105094937511452382003317776832808226841507530262) * 10 ^ 70 +
        7371738982929979599883837060201987308883315323036719495496930992522732) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_29 :
    recurrence5Scalar0Exceptional.coeff 29 =
      (((11976228480232776364729109890479819511667699067336493634410539 * 10 ^ 70 +
        5808542448093581259323881620756834422394844013943466682880211647707252) * 10 ^ 70 +
        6838076447007028254356641086306084127634266758941151331511364191868598) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_30 :
    recurrence5Scalar0Exceptional.coeff 30 =
      -(((1671361558171939307099440723507793180663073130787906686138702388 * 10 ^ 70 +
        9569575459713648004798110248069536774916898255749327917645941613689743) * 10 ^ 70 +
        9789424675654940433591431679393044340888270468683640805900150258816959) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_31 :
    recurrence5Scalar0Exceptional.coeff 31 =
      (((178114286427088143879641699037467422891108574577284140890885524149 * 10 ^ 70 +
        9343219699947422507651112954689734231576295950486956075386947405476043) * 10 ^ 70 +
        6377739912505370649057702379761368039662794204833113249159718921404057) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_32 :
    recurrence5Scalar0Exceptional.coeff 32 =
      -(((11973278142559817394182790326549452804691446540555453949357447024083 * 10 ^ 70 +
        7823207266707598376862494246872879575042666343136373052354594815817841) * 10 ^ 70 +
        9270593149718615419814288431617212459385531713831315991259085832078477) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_33 :
    recurrence5Scalar0Exceptional.coeff 33 =
      -(((173274601121097714831164684916590392318120028883450643943253257991107 * 10 ^ 70 +
        4110634225802260491320597680549338121839133159561364360803586836293266) * 10 ^ 70 +
        0363766135921866633271430645694813921829604575260292991624471808977205) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_34 :
    recurrence5Scalar0Exceptional.coeff 34 =
      ((((20 * 10 ^ 70 +
        1529416061383284918708521620177679071039556230146428418888695890940826) * 10 ^ 70 +
        1662829930132661886007641857946937446305160046514432588123918774371547) * 10 ^ 70 +
        8792959835603535930855595724651459696967971648696004778870356355328365) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_35 :
    recurrence5Scalar0Exceptional.coeff 35 =
      -((((3670 * 10 ^ 70 +
        9437605485986858546251097980499724901576136366932358565911279768674243) * 10 ^ 70 +
        5274477491035284188448309896176986608673477352595893590499358587836393) * 10 ^ 70 +
        0659933528907273252045714204122111978870479402641885956497178401826005) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_36 :
    recurrence5Scalar0Exceptional.coeff 36 =
      ((((445583 * 10 ^ 70 +
        1568310390155226840729455489322716337074391783851678904848346630416401) * 10 ^ 70 +
        9797563830270806932899796287078175400361289806466578946443965519986096) * 10 ^ 70 +
        0676048376380360369082938748845222493881174464688213863046689187860098) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_37 :
    recurrence5Scalar0Exceptional.coeff 37 =
      -((((40322609 * 10 ^ 70 +
        4951314707360470244198424729006183312950836079853094151899551503694918) * 10 ^ 70 +
        9579658605990197386203276436120672642836773214765996135325386602575807) * 10 ^ 70 +
        0400794012010589640170081855717625435661237557280187070927810531082964) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_38 :
    recurrence5Scalar0Exceptional.coeff 38 =
      ((((2586503180 * 10 ^ 70 +
        8670001222149190371552547320290572968522796228003690432997186653263918) * 10 ^ 70 +
        2095500004694679716655786206298237573548090888417512429042833519901191) * 10 ^ 70 +
        7840820414386737651137326718293773759978028786227067291554682670515691) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_39 :
    recurrence5Scalar0Exceptional.coeff 39 =
      -((((70001680479 * 10 ^ 70 +
        5529428532250010739147462214612634252938111065589003434528040633306441) * 10 ^ 70 +
        6081650524184888698002240234070184779442707263814673111090578959244140) * 10 ^ 70 +
        8447670050743256329749394541025708602916058848118486326042934696821637) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_40 :
    recurrence5Scalar0Exceptional.coeff 40 =
      -((((9749812583661 * 10 ^ 70 +
        9053164348342049375383446007135097067948022548169428167497975461691886) * 10 ^ 70 +
        5523560033244076906767234194285176771819941894580120472777922557686780) * 10 ^ 70 +
        5165841980105888565503526634936609909152014105846746167895845250060848) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_41 :
    recurrence5Scalar0Exceptional.coeff 41 =
      ((((2013361118058735 * 10 ^ 70 +
        9930458481532514618889720036267125068167042576212495316225013233089042) * 10 ^ 70 +
        5761464103577329185657674402833491178094801573029072075966330456051237) * 10 ^ 70 +
        5606676922711627881365829881750361914989344150926217791986477869945448) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_42 :
    recurrence5Scalar0Exceptional.coeff 42 =
      -((((233004559971632552 * 10 ^ 70 +
        5418692781372980581315989544215597994170500994657381663353105163882444) * 10 ^ 70 +
        7678458985624289279117099078874868334172702742287044497834567336335199) * 10 ^ 70 +
        7041826520229418252378593270964095163377861973320683232665968840958700) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_43 :
    recurrence5Scalar0Exceptional.coeff 43 =
      ((((21023322956308088453 * 10 ^ 70 +
        7530319071968596149898923455050271140256881127607746079891975456020499) * 10 ^ 70 +
        5856819365294926299780874157595544212564665443378377030709465507132842) * 10 ^ 70 +
        9192460830028936231861010214290487632815739812135143604140353827749122) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_44 :
    recurrence5Scalar0Exceptional.coeff 44 =
      -((((1605514884205629072821 * 10 ^ 70 +
        7075067318477241828357096956599544745291772231557413587300943709480354) * 10 ^ 70 +
        3229347642341054893885097570122656470346028949626145166710966589784747) * 10 ^ 70 +
        1731211228145771420145490119168269107015289331944038136546115629013428) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_45 :
    recurrence5Scalar0Exceptional.coeff 45 =
      ((((107406300075911229481305 * 10 ^ 70 +
        3488997512318510256300625671934628044098515696500940981631095200479205) * 10 ^ 70 +
        6500728821384189607624801781146326232772269543335444908480988681753694) * 10 ^ 70 +
        6710164853413985823468204438817086357815584274757876969715536839516567) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_46 :
    recurrence5Scalar0Exceptional.coeff 46 =
      -((((6409064810098680407619719 * 10 ^ 70 +
        5908972503182696250884693509655512032646993952742875545032840954609224) * 10 ^ 70 +
        4333262846698301563518671517084907966060116253270798323535058979082483) * 10 ^ 70 +
        7373628999738762827859274594732388440801754725359658360152270538214065) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_47 :
    recurrence5Scalar0Exceptional.coeff 47 =
      ((((344818650390064565908828301 * 10 ^ 70 +
        9062662522283365931136118931548555627721208947581660265799350397360883) * 10 ^ 70 +
        1743939503761998007522878887750812450035697212488173511217058665756920) * 10 ^ 70 +
        9352432318306665301155855726705382161450258438096668881147610736695388) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_48 :
    recurrence5Scalar0Exceptional.coeff 48 =
      -((((16842662095524403584910823439 * 10 ^ 70 +
        1168175528336898332868858200577881314705259702287837213667821501506706) * 10 ^ 70 +
        2056857947649016020745526513243203492880748887265616392352553684893936) * 10 ^ 70 +
        4919518374400151455767063551417338856923490872728223496949663291973389) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_49 :
    recurrence5Scalar0Exceptional.coeff 49 =
      ((((750255279966315855130034924904 * 10 ^ 70 +
        8366066028093816926152887350773870683289915006154457978708369093178677) * 10 ^ 70 +
        3094097283722634977745712311245448021327191801544491083281169207067912) * 10 ^ 70 +
        7697769165904901055374686112881588077548145775611868097461366699248008) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_50 :
    recurrence5Scalar0Exceptional.coeff 50 =
      -((((30563913003230962885513164616270 * 10 ^ 70 +
        1327588849004040806665848723468977485863223300129093724421756377821618) * 10 ^ 70 +
        5049940932844524355276806049035277764060934452031716683549538320483955) * 10 ^ 70 +
        9327246868699546523618887855668521760564800279787830057107018480334057) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_51 :
    recurrence5Scalar0Exceptional.coeff 51 =
      ((((1140346612421750933729817280606938 * 10 ^ 70 +
        4812966334751104240673996425896328876777097624944902267383465138792906) * 10 ^ 70 +
        2260125157796421527337242282566568027261250611951720662923627296196348) * 10 ^ 70 +
        8765689235328912512608652977997695527413984414871813047719853935487270) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_52 :
    recurrence5Scalar0Exceptional.coeff 52 =
      -((((38971373896345884122287432115019008 * 10 ^ 70 +
        8070516981705009289862786667328951004352868343609376919422634006284107) * 10 ^ 70 +
        4901420578290565711889378299703142331324232388473779069353194804040809) * 10 ^ 70 +
        1557216257531427695647721989421190274948687449308815816547269014547603) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_53 :
    recurrence5Scalar0Exceptional.coeff 53 =
      ((((1218247219893383399182317526449509671 * 10 ^ 70 +
        0772307663412478244001113859214312610243242401907492537906418500582844) * 10 ^ 70 +
        4168746454336101965727865558433025576467044087908297635021196273331140) * 10 ^ 70 +
        5732138486965859757798305727839074410951690549272407160602635066330355) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_54 :
    recurrence5Scalar0Exceptional.coeff 54 =
      -((((34716333155889776196639590913075236917 * 10 ^ 70 +
        4186448855641548323971818420059973986209463857976758564755476393041084) * 10 ^ 70 +
        7864953154377871901138326973569200561576768798961834720400347057628640) * 10 ^ 70 +
        5934389946852785267597019437342791483244679661604140104091354058221983) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_55 :
    recurrence5Scalar0Exceptional.coeff 55 =
      ((((896028240591634567187914489465761641546 * 10 ^ 70 +
        1400425723973908706286382562594517834846707742157171675042602456880100) * 10 ^ 70 +
        6918456028003943417173304566863854569453450241498774018153226951120720) * 10 ^ 70 +
        2878249923387998892027689123768360076967346432351512290430108922509586) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_56 :
    recurrence5Scalar0Exceptional.coeff 56 =
      -((((20695845420363236165753566417660407723297 * 10 ^ 70 +
        1316441307794716589061687725482824522035385331720559838064069451966674) * 10 ^ 70 +
        7951606744728594752195559320927199018778796292778331311238896984817585) * 10 ^ 70 +
        3916986802836374005727997286169513742129312797355529181423666031756088) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_57 :
    recurrence5Scalar0Exceptional.coeff 57 =
      ((((417824740165427309152138832248803939020823 * 10 ^ 70 +
        0532459202325053129746329967778898954760958876910975355710916968455961) * 10 ^ 70 +
        6372999761338292395755422990478821455966351129632737906327999686197447) * 10 ^ 70 +
        5139973658065730981492035164120539990182732229169749419966799899856979) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_58 :
    recurrence5Scalar0Exceptional.coeff 58 =
      -((((6987655759957842243180554534748124837208396 * 10 ^ 70 +
        3954215576825023668033493873498284263209385751062856087742393204104095) * 10 ^ 70 +
        0006588417471175409891849087421854147769724045409184695479307338714502) * 10 ^ 70 +
        0392500816601493408292241130077565208243510710567193854401562545068189) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_59 :
    recurrence5Scalar0Exceptional.coeff 59 =
      ((((81518411565188954823433605296168575935611040 * 10 ^ 70 +
        1093114814095042906880680204478578669205263471694015837057359429870344) * 10 ^ 70 +
        0421493316141488325658703783558114658631969226272494357973718378274265) * 10 ^ 70 +
        4160050584269723657101248306670621236668788286607397038314253624476100) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_60 :
    recurrence5Scalar0Exceptional.coeff 60 =
      ((((8103382484867436662262510996383236650417205 * 10 ^ 70 +
        9734343203977549140809546925998774546592692000870896777771265323895208) * 10 ^ 70 +
        9045187518253650238570543949890663130095271191083639039434002470967684) * 10 ^ 70 +
        7701469475244426657499392629596619747356732436424497395999088313340278) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_61 :
    recurrence5Scalar0Exceptional.coeff 61 =
      -((((36090541611761511710502715476300188148826975861 * 10 ^ 70 +
        9539542209695898513885428375520272723947595314795759066955760463075420) * 10 ^ 70 +
        4124009167991090887925643244684859441597238498050298410940431215294006) * 10 ^ 70 +
        6513284540566325897849422333458506735072205002623879206554444312319155) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_62 :
    recurrence5Scalar0Exceptional.coeff 62 =
      ((((1341482452000576320551586085346376259128245782634 * 10 ^ 70 +
        4649426934443742539998450142741942247392393713002748889071770414778688) * 10 ^ 70 +
        5296056330753754099899611251664655474243749200965903938358920460006466) * 10 ^ 70 +
        2983808033954638981672118034370852438115170339075307170868305356250315) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_63 :
    recurrence5Scalar0Exceptional.coeff 63 =
      -((((34335581959609386353570146807837356698633415158004 * 10 ^ 70 +
        5207066998560978725489589469811449588899792213477744794003030173296508) * 10 ^ 70 +
        7031401936644318072261790072783576517285969761604069993216246247697520) * 10 ^ 70 +
        1077616122966407534404682051816381911745891055605155154731252205777813) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_64 :
    recurrence5Scalar0Exceptional.coeff 64 =
      ((((707530649574841726355371679971567854427796678178996 * 10 ^ 70 +
        4081302444159043141787599194366442551551644528963333518348751379599866) * 10 ^ 70 +
        4790679003680610036962776698854645083782174174907905944673465903781766) * 10 ^ 70 +
        3306286236117332270287544989585259187820740148382312655466665130529656) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_65 :
    recurrence5Scalar0Exceptional.coeff 65 =
      -((((12088055171850373819384709826156677208617986176073213 * 10 ^ 70 +
        1590118405415567584480818614691448345357752087886712129062376796125072) * 10 ^ 70 +
        5723458346556968843136703028276059232414830559978472940534605840603893) * 10 ^ 70 +
        4182023806207137532285639283689526303490145817886733533943919173447406) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_66 :
    recurrence5Scalar0Exceptional.coeff 66 =
      ((((166297967652198994901526539148821573594218348012148747 * 10 ^ 70 +
        8715177920934788783162150998501653440668192585831805580237838932952012) * 10 ^ 70 +
        0186750373318022061586149564219124298873414201000560868597626254975954) * 10 ^ 70 +
        3555229542902547315848176629134396689778360507740013024591876737776024) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_67 :
    recurrence5Scalar0Exceptional.coeff 67 =
      -((((1579342057799743233057402064548043170099269868157381560 * 10 ^ 70 +
        9977459390863069746688160942524346468876817630656157369820651507900067) * 10 ^ 70 +
        4130357585881138903405757547322766751260720025535311824029270178504232) * 10 ^ 70 +
        6231895986945837928626139475529432556572888794741330928022162231957644) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_68 :
    recurrence5Scalar0Exceptional.coeff 68 =
      ((((450283811567693803582885052492081371792610225973750706 * 10 ^ 70 +
        4562355321182035321475671243444329436101781083151951208396022116447816) * 10 ^ 70 +
        3895611997375278994400002047175840318461231189281098789332798843263589) * 10 ^ 70 +
        1148618192409539310563915563987541975632252467003412446118542346578448) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_69 :
    recurrence5Scalar0Exceptional.coeff 69 =
      ((((425097528555164424084629654844905203220994313592703580065 * 10 ^ 70 +
        8047188990391260348181404078681300414155223105391938811209055490500427) * 10 ^ 70 +
        2687251833114826715963116608437859216408057551810311311964265021420903) * 10 ^ 70 +
        1465265055610479378269303127781369161658704456178906272656444737207675) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_70 :
    recurrence5Scalar0Exceptional.coeff 70 =
      -((((12716219062891558392098961502157615146083501576056346011477 * 10 ^ 70 +
        7240757664472329175069624105705326390153846020850963477892127606406217) * 10 ^ 70 +
        4738941439305057341806927240523631857843051134732958343131329038692083) * 10 ^ 70 +
        1135259294259642295503630072023429313792268013947879918700968310239734) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_71 :
    recurrence5Scalar0Exceptional.coeff 71 =
      ((((262004013758755404316478749685931059696214670076018515336072 * 10 ^ 70 +
        2246124393432392290085133760793904780013552886653731719557647538079043) * 10 ^ 70 +
        7778215918558920194411377724079487469277178040896415212230551476055727) * 10 ^ 70 +
        8458842186666220813169712673056471870158801432675318989285774716636649) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_72 :
    recurrence5Scalar0Exceptional.coeff 72 =
      -((((4409184032193890911697030825866517742538866702609806506904476 * 10 ^ 70 +
        3994248407844463604822169729798025516596268521539959888753828813994826) * 10 ^ 70 +
        3656832341353681057699423619836754038516140794507614743851942616844841) * 10 ^ 70 +
        3832561304368611307143758901648117259407516964440002795528172808238622) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_73 :
    recurrence5Scalar0Exceptional.coeff 73 =
      ((((63521837361319003762051569537258066276847929923557264352175594 * 10 ^ 70 +
        4512420626365190117940331442254705656088194153743985036328870461657505) * 10 ^ 70 +
        8132870529445316661453189117020010360520039850353176496079067665950156) * 10 ^ 70 +
        9897357994975274453158449646483933796136672145264597681547206563361873) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_74 :
    recurrence5Scalar0Exceptional.coeff 74 =
      -((((792257593814333532100316804759798353905142356001682479536273199 * 10 ^ 70 +
        8863875123942131212689283697424635764417299632968323396393503329863680) * 10 ^ 70 +
        4474410139985236338897656270663667652541827310457435731015776160188334) * 10 ^ 70 +
        6298580917273284560700838200903430837240301419593209943410673602570150) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_75 :
    recurrence5Scalar0Exceptional.coeff 75 =
      ((((8455380575171714340284872200207996100299784476485304005801466672 * 10 ^ 70 +
        1078289049852241948153637188208954844696137839417550834571587554883482) * 10 ^ 70 +
        5207056729186599482910235847052702068985034253360516425485195119778752) * 10 ^ 70 +
        1490861070190499588151961047997251040671662969380849047192383231055371) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_76 :
    recurrence5Scalar0Exceptional.coeff 76 =
      -((((73705219419138713002761268389652055891198285767658853011930064051 * 10 ^ 70 +
        8409726215895668408102843377160987050062537070617318539237408835854973) * 10 ^ 70 +
        8923409007748853664745024776555371976038563078276503462914154472502292) * 10 ^ 70 +
        6559130805434253436040285989601688868047055642494586351933450099022977) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_77 :
    recurrence5Scalar0Exceptional.coeff 77 =
      ((((445674699684262447475556106795564446210878366694089162010015697997 * 10 ^ 70 +
        4455225738301346346255412242772222477163105617071599860781324945982817) * 10 ^ 70 +
        7294365087497198158214277485832221747470355926603146056151091752082914) * 10 ^ 70 +
        0319709455327451489843885139997945329950262032855316992991511021701255) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_78 :
    recurrence5Scalar0Exceptional.coeff 78 =
      -((((91392200370962111984110982884762196205180663953026860512233538295 * 10 ^ 70 +
        3892305344752644182845462462845855730215233693489890982850735590000452) * 10 ^ 70 +
        6785667431807307367484554332458386737422000398469363813284702370170964) * 10 ^ 70 +
        8009217537832823842778633038066390517194453006291136722942121089578877) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_79 :
    recurrence5Scalar0Exceptional.coeff 79 =
      -((((47404489506935989329493302513676621895405887585700272213035802769565 * 10 ^ 70 +
        9571815099229446565655547337684844411426183737432627722709364880071864) * 10 ^ 70 +
        4593366092538276970766845594156401405324994330480963580351636907831976) * 10 ^ 70 +
        7453448579418923346939183631961515241789443473632687128678675716222585) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_80 :
    recurrence5Scalar0Exceptional.coeff 80 =
      ((((869768065925205559836115768384077599336550674656104460117527096412603 * 10 ^ 70 +
        5909982486463458919800219286971308258509621896140085426763216209687917) * 10 ^ 70 +
        4383402256598880013952234859699220947267599120937824864300986281299368) * 10 ^ 70 +
        0716232913908362158929577354948048763495230405697005455824943677373493) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_81 :
    recurrence5Scalar0Exceptional.coeff 81 =
      -(((((1 * 10 ^ 70 +
        0548867463021080337964322304389569904726487990840777603691429763297347) * 10 ^ 70 +
        1271350988953375519245157221143230724221232678484753035665264085546220) * 10 ^ 70 +
        1884837046424683205395032039185142028237916992512658532400878866547544) * 10 ^ 70 +
        5993907485546073830186300434634006539239947360858491326273273373560086) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_82 :
    recurrence5Scalar0Exceptional.coeff 82 =
      (((((9 * 10 ^ 70 +
        6684945576754302243446814802942967604372356184955118481153281347623588) * 10 ^ 70 +
        7692085368577055070702871210397989845930364514964719099098936700654966) * 10 ^ 70 +
        0889643604223085721974572324295014898308489913610778588567451946362421) * 10 ^ 70 +
        7167568001373658375718718727638718511852081833327226018554516197635442) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_83 :
    recurrence5Scalar0Exceptional.coeff 83 =
      -(((((63 * 10 ^ 70 +
        3209982837951522381281836076488302912558305540393804737801855244495659) * 10 ^ 70 +
        2097630490718489246827152511791508821634824218035874460486708272631207) * 10 ^ 70 +
        7919380203729805188702958522411879114229517973352517899134786446016470) * 10 ^ 70 +
        2458230917661126737841478498260466141413828924472141524403026876919669) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_84 :
    recurrence5Scalar0Exceptional.coeff 84 =
      (((((165 * 10 ^ 70 +
        0647632821375360141179318700849800178766320555816662982326715976769141) * 10 ^ 70 +
        2601388191527094462493186822257625649937362171728609218419251250638198) * 10 ^ 70 +
        3289525374910597156601123995052159568643268604871419424581254187936529) * 10 ^ 70 +
        6827625202013334458010792576920621840759533067064755167551271089892710) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
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

theorem recurrence5Scalar0Exceptional_coeff_85 :
    recurrence5Scalar0Exceptional.coeff 85 =
      (((((2848 * 10 ^ 70 +
        6660876136568573146220964437936093407569093199190464504663822473354292) * 10 ^ 70 +
        1070189473337975004824661171410791827722420715272522611440753686660342) * 10 ^ 70 +
        6564779814179212908037904690712149932014945875455225376469995758855691) * 10 ^ 70 +
        9912616824796423529718355552099289473853178360409065981305074162584737) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Exceptional_coeff_86 :
    recurrence5Scalar0Exceptional.coeff 86 =
      -(((((58129 * 10 ^ 70 +
        8793583268041224523319183940879778244620071074917525218239856930575077) * 10 ^ 70 +
        0893914646111856336664699070670551144350467232292347969535024119439704) * 10 ^ 70 +
        8265229784461192847593864491863233313749769171645778858923297293548667) * 10 ^ 70 +
        6405409607161988473746375042558532298750235426772769896543212190565705) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Exceptional_coeff_87 :
    recurrence5Scalar0Exceptional.coeff 87 =
      (((((655823 * 10 ^ 70 +
        4288016340538830769037475533313854552987262458864845921604479134182579) * 10 ^ 70 +
        6646150293150594145470446793641415388638315718967382704740073995082084) * 10 ^ 70 +
        7817028106617128252738933152772583740868749688000512272204240625798476) * 10 ^ 70 +
        8072384339038063595896633400876329476460473864548125707797995391149402) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Exceptional_coeff_88 :
    recurrence5Scalar0Exceptional.coeff 88 =
      -(((((5252816 * 10 ^ 70 +
        6619094643619237320607796180134060335117917311844796583080253430596056) * 10 ^ 70 +
        7483519367656114663848684256057762458268279950379034670487288580235600) * 10 ^ 70 +
        6951145357445940807042168494973192919925317993570804154991263163552546) * 10 ^ 70 +
        4213600925816271947461379274489305153860799151231713224832718990702020) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (89 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_89 :
    recurrence5Scalar0Exceptional.coeff 89 =
      (((((27360813 * 10 ^ 70 +
        7971831689297394373916174338216429001584348021075223859880152454865734) * 10 ^ 70 +
        7346859667362153251446184260058280510053767218861537656807921444551641) * 10 ^ 70 +
        0114948680779054528150007347227541154702079413739974552578286166517789) * 10 ^ 70 +
        0473207218969054304755558315327734315639579930983914866847837906540909) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 90 = 1 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (90 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_90 :
    recurrence5Scalar0Exceptional.coeff 90 =
      -(((((9273032 * 10 ^ 70 +
        9531903636482083899173466826407677318781014937711422350437311617245896) * 10 ^ 70 +
        5117223391861319185433164575138948568252227736476079254118629830776481) * 10 ^ 70 +
        9510139919922667575425756552795818048449740758275529144405892557570869) * 10 ^ 70 +
        9951353293241066408931889960944859596015353932061563780690381107436469) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 91 = 2 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (91 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_91 :
    recurrence5Scalar0Exceptional.coeff 91 =
      -(((((1797787397 * 10 ^ 70 +
        4710237784500413350240851017954020140113359925954168279059300049169148) * 10 ^ 70 +
        6414703511455828191184657714005010826227926952307121497239005228751460) * 10 ^ 70 +
        1473765396255440449560591368891848753302703449660123392519820832357567) * 10 ^ 70 +
        4990469605379390168381620908603148778391595488076887584010338671754287) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 92 = 3 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (92 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_92 :
    recurrence5Scalar0Exceptional.coeff 92 =
      (((((25401575935 * 10 ^ 70 +
        8436840072594208489504657689188534834922015359564691357379468013099990) * 10 ^ 70 +
        3546498980070960419302388193825440144452008534244643632866682362085589) * 10 ^ 70 +
        1504213080754469506400270518838165036550094211272539905245798267451980) * 10 ^ 70 +
        0059046994195610961989491316829264586723542778174753369911762390605460) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 93 = 4 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (93 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_93 :
    recurrence5Scalar0Exceptional.coeff 93 =
      -(((((224715438992 * 10 ^ 70 +
        5855978470631471223609386998860481468942289529536471534857133923104129) * 10 ^ 70 +
        2666574167131143807591573176614920202121757478699331992047465770765101) * 10 ^ 70 +
        0853694469888659806987107885541905684048426852958078560329901794997240) * 10 ^ 70 +
        5360270696223840041642646640160655818987267690052757407356918189159179) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 94 = 5 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (94 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_94 :
    recurrence5Scalar0Exceptional.coeff 94 =
      (((((1357184354862 * 10 ^ 70 +
        0128372777434723431002808421013542429086267108489355971938367407754665) * 10 ^ 70 +
        6967521386917735199703330050222412271043912547589907241794916924962085) * 10 ^ 70 +
        6747452959084860477488718400832363030528504313890298131668374348482281) * 10 ^ 70 +
        8281741155224315900525361349868507271270626258921339380323335328390340) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 95 = 6 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (95 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_95 :
    recurrence5Scalar0Exceptional.coeff 95 =
      -(((((3743440914901 * 10 ^ 70 +
        6080339263138364126453634990018185382703068576576053188884675175827661) * 10 ^ 70 +
        3624373095851158233276810039107259166741677856221948227260743834698051) * 10 ^ 70 +
        8927274417551897373426145831954989639743063049696537391697616406432248) * 10 ^ 70 +
        3702518158862084506291953677908440842018364874167971023245984859198961) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 96 = 7 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_96 :
    recurrence5Scalar0Exceptional.coeff 96 =
      -(((((33929808946245 * 10 ^ 70 +
        8509513035082031643975985886861013450342310595728996569018291564057078) * 10 ^ 70 +
        2980969754378291318877000420219286383361519516799418737664982313613476) * 10 ^ 70 +
        4410018044991736202446329824650316159036739490949260935610557443714288) * 10 ^ 70 +
        8271876885130275499818336809682697495334052509044619771390227398585737) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 97 = 8 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_97 :
    recurrence5Scalar0Exceptional.coeff 97 =
      (((((648984806411145 * 10 ^ 70 +
        1644445043399511911436081411152080132598363596618610309294272462595099) * 10 ^ 70 +
        7838361494477741185510378414245499148551438229633245721855246876658431) * 10 ^ 70 +
        4380693287688115483329040393496966507479928073694745004250212625449665) * 10 ^ 70 +
        0201269784360368294063102029490017716110947904651842906124407672896890) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 98 = 9 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_98 :
    recurrence5Scalar0Exceptional.coeff 98 =
      -(((((6145553174263172 * 10 ^ 70 +
        3062499027079818757413302035038027211586519234155673074930394902305722) * 10 ^ 70 +
        4864902343062089102475790548237626418032888245085423244886265080645640) * 10 ^ 70 +
        9702956190935034072120226573040379124653338464419488910439192912105102) * 10 ^ 70 +
        1284582169888026254758049131395150804498650608524356935954923603806237) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 99 = 10 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_99 :
    recurrence5Scalar0Exceptional.coeff 99 =
      (((((39373817926363715 * 10 ^ 70 +
        2990062568453677186693978472152455812289362448894062335504816417341873) * 10 ^ 70 +
        1043749735679085320945110398581855802707757973807265691812276018942093) * 10 ^ 70 +
        9478542092516579044010836787763914025008426903961253065000602548294195) * 10 ^ 70 +
        4695205714531088326701578540974409186943251713233685519393935165936704) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 100 = 11 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_100 :
    recurrence5Scalar0Exceptional.coeff 100 =
      -(((((144263926688099895 * 10 ^ 70 +
        0127955936039023495062884107603347922650513219171389438802012115473975) * 10 ^ 70 +
        9384749507502953279982116270269183627147265366452833183016880069182841) * 10 ^ 70 +
        6151579848402157869907434444105655386485481531184715662019346534615748) * 10 ^ 70 +
        9879926631401625813876118828044918670683145871206028009638293835498083) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 101 = 12 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_101 :
    recurrence5Scalar0Exceptional.coeff 101 =
      -(((((348533046506105539 * 10 ^ 70 +
        4731284596085772720244320213318330914169297422339685205948558838026261) * 10 ^ 70 +
        1835081193387501750720126194201783008541144676235052610086415335700939) * 10 ^ 70 +
        0664318963238814941850018257396177455881983512036594550799798341146348) * 10 ^ 70 +
        1694512062946544556808912159548208375724513310672317237430089399473618) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 102 = 13 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_102 :
    recurrence5Scalar0Exceptional.coeff 102 =
      (((((11468840935629843579 * 10 ^ 70 +
        6687489566085170862808644565141597497161177335133070127727441836013660) * 10 ^ 70 +
        8630305552693247702936441933681028338408923210052446633261978222729900) * 10 ^ 70 +
        4836489102736726068388272045452962342484922108535490587252223798876528) * 10 ^ 70 +
        2183008579339354614400252430608860030234806204705809757658813107642629) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 103 = 14 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_103 :
    recurrence5Scalar0Exceptional.coeff 103 =
      -(((((115601426894050828507 * 10 ^ 70 +
        5459827017457116117381354503932962969014248146427451317474938241942189) * 10 ^ 70 +
        1852849258753282099574104857684124461298310685302220781804161305364710) * 10 ^ 70 +
        0819618252966899285001338933039634654498885449442543174819008959163423) * 10 ^ 70 +
        6543323706595821127717114251306432871176724742418348969377879073051996) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 104 = 15 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_104 :
    recurrence5Scalar0Exceptional.coeff 104 =
      (((((766464331766672151752 * 10 ^ 70 +
        8984897818682072272981559669865711348287239644592504523758971193508592) * 10 ^ 70 +
        4477161200693396841641830623435796830579248081662224654629400322999895) * 10 ^ 70 +
        8181990557150646759211700980189515267011649087124089253475296146190041) * 10 ^ 70 +
        4296040536900867244968964638532045352746700503801202779163204408021741) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 105 = 16 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_105 :
    recurrence5Scalar0Exceptional.coeff 105 =
      -(((((3194929417398775159123 * 10 ^ 70 +
        2314058352066225207963303183712925766564476891161494642491937227707349) * 10 ^ 70 +
        5353052202291456293468053796779403243054001802976151360939662180357820) * 10 ^ 70 +
        5224886746349362133857595485809377717082893888061594127038850965197854) * 10 ^ 70 +
        2830477584574349637634581929033371285463771752228255280030708352013839) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 106 = 17 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_106 :
    recurrence5Scalar0Exceptional.coeff 106 =
      (((((333669405494952994945 * 10 ^ 70 +
        2532859985177733912866866234964792805313908459121460110124882965222918) * 10 ^ 70 +
        5070666247067716268180320641129389651484575384828050481222843321116400) * 10 ^ 70 +
        6510431262924211618682896147408234846563890447647193268045894595564250) * 10 ^ 70 +
        0612977762054103838765107918848393340372146261144344490230952747084758) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 107 = 18 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_107 :
    recurrence5Scalar0Exceptional.coeff 107 =
      (((((139847493990396195450628 * 10 ^ 70 +
        8431642539205721455152248778502045038060658151201242933253693366098864) * 10 ^ 70 +
        1832386764497621420599085845361965858014715266044161157417193525374261) * 10 ^ 70 +
        6055372522651744814009185380004321527294302105596238281171606172910598) * 10 ^ 70 +
        6697077881137577724302413810046711786473747428197962351858637739288824) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 108 = 19 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_108 :
    recurrence5Scalar0Exceptional.coeff 108 =
      -(((((1537820152408543907521811 * 10 ^ 70 +
        0165956023128640609534030249196401837002078261974266464051335318793759) * 10 ^ 70 +
        1410707736464012713111886511765780489275712320734049463938943160810150) * 10 ^ 70 +
        7572214377544816304101369215520403623537745974437237568914836719838605) * 10 ^ 70 +
        1830529678049933324493226328955354888741726545292848211075556162471137) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 109 = 20 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_109 :
    recurrence5Scalar0Exceptional.coeff 109 =
      (((((10577988348679406566805632 * 10 ^ 70 +
        0070974517335453302103582452499051113659146641691350515519224238312993) * 10 ^ 70 +
        8987654099285294854936052567723935891718246194815249228998118472135219) * 10 ^ 70 +
        3386650088344891887750930256552822936218341316620141396399289678235415) * 10 ^ 70 +
        0699426714411126199109243639636519370555312355380013733591685237701275) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 110 = 21 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_110 :
    recurrence5Scalar0Exceptional.coeff 110 =
      -(((((48437496950405817307296831 * 10 ^ 70 +
        8574179387167086546827565601807308260071817780052292365357851704423066) * 10 ^ 70 +
        1145825594241174549415769214673305472525604152469748524647363491570037) * 10 ^ 70 +
        9723276819402675436594051957795289797026935156294035730797835439182625) * 10 ^ 70 +
        9589940655244077784441059828005666125763968976866383799203546583116302) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 111 = 22 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_111 :
    recurrence5Scalar0Exceptional.coeff 111 =
      (((((79009995427251613986148072 * 10 ^ 70 +
        5452919767209958158257256922796373179738957266332842102973353099483154) * 10 ^ 70 +
        6482996335164314570117847525578453428766628716321414583471405280951195) * 10 ^ 70 +
        1275629247514785479071409638660948826721873579571937261565918692792606) * 10 ^ 70 +
        0707516285555456962331904471816558535798174945329000974204254833265354) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 112 = 23 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_112 :
    recurrence5Scalar0Exceptional.coeff 112 =
      (((((1104880774280823040204930667 * 10 ^ 70 +
        8953138231183013789872739503739472902250235625837132104282079392778418) * 10 ^ 70 +
        8083444488455445853481925574018763799321219474214420615975606514635625) * 10 ^ 70 +
        3819987323241649486515414522732376607603739431567066637923767309491345) * 10 ^ 70 +
        9612347463229900050114843031892980998754437112085724305044043309345006) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 24 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_113 :
    recurrence5Scalar0Exceptional.coeff 113 =
      -(((((14468026686154964166189005669 * 10 ^ 70 +
        0694802218126329301889882843554050013286589113381838542300573334322571) * 10 ^ 70 +
        7260072171299780881426986473396057470595791161471079541632156360781641) * 10 ^ 70 +
        5553931607594072256150248142448047189737513703780119942608337044654928) * 10 ^ 70 +
        7687621341368209577425972612532434236182294218751454265782976155740930) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 25 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_114 :
    recurrence5Scalar0Exceptional.coeff 114 =
      (((((105723714838829024319942507433 * 10 ^ 70 +
        9383989925555265582285106211193813432543893107648890791605946750638017) * 10 ^ 70 +
        6175355793006395146572340174588200899410100922757700093463724778084382) * 10 ^ 70 +
        3238757941403509293526921524333530300974180345596429539058525070467847) * 10 ^ 70 +
        8410775535975408020228062027597507826032404650742866868954467117195470) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 26 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_115 :
    recurrence5Scalar0Exceptional.coeff 115 =
      -(((((531339370582907138657385702563 * 10 ^ 70 +
        6407342016161978396311598525472449675967644870109804965916930534083413) * 10 ^ 70 +
        7746581222699913340367355162412156747453367874952414644935492997884056) * 10 ^ 70 +
        3538442689975873443253825430212119389366791461407664870542310815554879) * 10 ^ 70 +
        2909363181707854360379736225011181953961611968802434660212915038021103) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 27 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_116 :
    recurrence5Scalar0Exceptional.coeff 116 =
      (((((1480003749457405205315994300055 * 10 ^ 70 +
        1937069761053764626381956608896436738150066939435785022133617486930824) * 10 ^ 70 +
        5203772193380966799187365321230008476867434002876635060141501232368685) * 10 ^ 70 +
        4729029781161410171430325097716258379960268072053277830879620934787545) * 10 ^ 70 +
        6633816548560200217428250863000621471540450950702692682763866203696936) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 28 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_117 :
    recurrence5Scalar0Exceptional.coeff 117 =
      (((((4194752586840221997761876842022 * 10 ^ 70 +
        8649790646137378021451949444531832763853508841150428706347200602141703) * 10 ^ 70 +
        7805650925635614190378860400776356688782285954583345537444921986168841) * 10 ^ 70 +
        3823344667236379032327874744463819720211917242531685721172448526375983) * 10 ^ 70 +
        1440463563114179247932795270935826657215250373876476243650412680224517) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 29 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_118 :
    recurrence5Scalar0Exceptional.coeff 118 =
      -(((((92666027141130428401528477468406 * 10 ^ 70 +
        1772515268276874074982672322927810992466979863292551102505114719341855) * 10 ^ 70 +
        9389347053496721211801058861500006847833104850979827891801968223004906) * 10 ^ 70 +
        3092907169408854810337680154674209481061923324174618468387523119021856) * 10 ^ 70 +
        8053676811258020628888495625056134522671870001630996362203707199429458) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 30 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_119 :
    recurrence5Scalar0Exceptional.coeff 119 =
      (((((760137971743796360944392655310933 * 10 ^ 70 +
        8126300129781238062921895967865957504860031477407823642001886915791333) * 10 ^ 70 +
        7542717107261251763740454272155571460425265779145738036971110172639863) * 10 ^ 70 +
        4313298274540222554946777044750817307709317049634759647996567155939634) * 10 ^ 70 +
        5010923366056088722212899905277159069853636211877201966342461512670723) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 31 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_120 :
    recurrence5Scalar0Exceptional.coeff 120 =
      -(((((4257401853940287024141484511589128 * 10 ^ 70 +
        7791158553120336470694283677302785769113174858547936753525258714243271) * 10 ^ 70 +
        5373547225216654073908206486145086823516671546889044800563140279611557) * 10 ^ 70 +
        6493877528073124727779615209156231772251758354622261398275831298215056) * 10 ^ 70 +
        4212776068109801843768850590668397934055351141158199574467797708549857) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 32 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_121 :
    recurrence5Scalar0Exceptional.coeff 121 =
      (((((16005913016390552498228726839409483 * 10 ^ 70 +
        5811244185490589474942847237960497214269916560520931839250917554286588) * 10 ^ 70 +
        6324944825454348088491794895109512659612610335247099284823186954402323) * 10 ^ 70 +
        4350486132885514540583916996364932399541588655325867038230522663291503) * 10 ^ 70 +
        9315712066749271513785840300775083032033937300629999860989122945215867) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 33 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_122 :
    recurrence5Scalar0Exceptional.coeff 122 =
      -(((((16209498422467029099285705693095734 * 10 ^ 70 +
        4725899599557405926026288218999911284372034300257212546300228310402068) * 10 ^ 70 +
        8672281251252646310860678351091663396006981481324224295561632324334187) * 10 ^ 70 +
        6404956979357929313035996756762353382918374395883310621902119912700857) * 10 ^ 70 +
        3468554845354011045824133350226413831362990301639271462420889730683726) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 34 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_123 :
    recurrence5Scalar0Exceptional.coeff 123 =
      -(((((347266389912696859903632415911325688 * 10 ^ 70 +
        5414335730843174046429817852454570576878453660242240956873221659463014) * 10 ^ 70 +
        6166725472905363779305446481714632993031017082104388579364098295759087) * 10 ^ 70 +
        3027251398475301157911302120539233791523102489249125809612967780015227) * 10 ^ 70 +
        9727016045554948173563094944493867740572921696747132162835230425891798) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 35 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_124 :
    recurrence5Scalar0Exceptional.coeff 124 =
      (((((3741277779746653137803312423166139468 * 10 ^ 70 +
        8673223700383172837552162304855769452423956415232016949758440202531294) * 10 ^ 70 +
        2915839134965768124998596393990376354008295911570636553146334690660255) * 10 ^ 70 +
        9635680234304328851805461811938900906481518833444741221421389411303605) * 10 ^ 70 +
        5706063279818182640460343019581278122414992457091639038120032700370581) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 36 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_125 :
    recurrence5Scalar0Exceptional.coeff 125 =
      -(((((24284377304838151755457273176033991854 * 10 ^ 70 +
        0881970033172193948601319671809663413707377638398688534038961985595126) * 10 ^ 70 +
        2785513577723757344206457573753907301576279910311814419604075109495757) * 10 ^ 70 +
        8606912912651943691851422919269896525111165028488230323002326415606611) * 10 ^ 70 +
        4900437444648193113950762093787669850414816097375056871011813210999786) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 37 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_126 :
    recurrence5Scalar0Exceptional.coeff 126 =
      (((((113604807578191660630902342103617802314 * 10 ^ 70 +
        9092956377486510419869255915482636705347342408777282770374105021090144) * 10 ^ 70 +
        9552893516412449198727713067110975138893779337967467506941824884070181) * 10 ^ 70 +
        3013082516273798348874486164056577802329862939173543397439891532283810) * 10 ^ 70 +
        8949274732738188317811004087485633264734682702497081721859925953328855) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 38 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_127 :
    recurrence5Scalar0Exceptional.coeff 127 =
      -(((((338743345484893889645178543321196697054 * 10 ^ 70 +
        4404675008955808039025450949614006332355717995839939503932162119747949) * 10 ^ 70 +
        5240769581298742853586002550259185034401872041366324842547351465515936) * 10 ^ 70 +
        3681878003979495380428878132042051811869997009486091604451051397862088) * 10 ^ 70 +
        0077195593014802253962314759553896987931734597244734700960224683660757) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 39 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_128 :
    recurrence5Scalar0Exceptional.coeff 128 =
      -(((((133503565551409458681214526741047078283 * 10 ^ 70 +
        4071805187288583010283542501267783445030404062292056283401599875863254) * 10 ^ 70 +
        1617060267199987515244949282455389328590760324783115890727735575665640) * 10 ^ 70 +
        8337719828171835184951086217672956053968944579584994232602248898331523) * 10 ^ 70 +
        1427917374952521188480173551295797941165632490996163946296960185466022) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 40 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_129 :
    recurrence5Scalar0Exceptional.coeff 129 =
      (((((10573213321558467658500218475448496726940 * 10 ^ 70 +
        3918003925869018515641816435843998920384889275646860691313212958888849) * 10 ^ 70 +
        7864231960065608311162926414227215876996351692840532877817828234431280) * 10 ^ 70 +
        9869023349036964215295319685382577817810750373085430440930821530456725) * 10 ^ 70 +
        9863928697941836859369231623590124060311620647092831428367761395665186) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 41 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_130 :
    recurrence5Scalar0Exceptional.coeff 130 =
      -(((((90930050871071634321962468066563477054503 * 10 ^ 70 +
        1488789167571382772784485893518020978474399637806264157415915210935499) * 10 ^ 70 +
        2764013215510983686021086388693808966397987694049999232927112362128878) * 10 ^ 70 +
        7066835651923875790012158945319462518771710058843336750649573872998734) * 10 ^ 70 +
        9060818077387483212820726098711764422214367547702134455403214717647761) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 42 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_131 :
    recurrence5Scalar0Exceptional.coeff 131 =
      (((((526348491439777504513919000761750152357460 * 10 ^ 70 +
        8096442514934612473863467076316125445591287833695572539681058572973635) * 10 ^ 70 +
        8141745922450482827777171463577129701335240648202566896311321998674168) * 10 ^ 70 +
        6483227120911636460981935409723117992566621298189430988149163681467063) * 10 ^ 70 +
        1990651594327377805273001266330778455767664766784482508713641554829515) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 43 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_132 :
    recurrence5Scalar0Exceptional.coeff 132 =
      -(((((2271142482640730410131208225951566968802072 * 10 ^ 70 +
        9057114815117080716104273780207567523188393445135136391366656506072691) * 10 ^ 70 +
        6564259493412037506885445510561678275172252075816389212109798654136249) * 10 ^ 70 +
        4822761637505880941441703476518102805074797381601027136277759540398657) * 10 ^ 70 +
        1544189575384869981642987582611128782088442586144486907089277291254271) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 44 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_133 :
    recurrence5Scalar0Exceptional.coeff 133 =
      (((((6433493684854417084826248361559165544154395 * 10 ^ 70 +
        3485392139113147972916215471696330695383869132020888457175861316294786) * 10 ^ 70 +
        1307511814740046234155410167053653059671798657206830022229038060518469) * 10 ^ 70 +
        1156609855516438990216759936317823695650447372845345202345852415459383) * 10 ^ 70 +
        8546906582852564875904500802739753334428733817656361344009075806359977) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 45 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_134 :
    recurrence5Scalar0Exceptional.coeff 134 =
      (((((1011951259214910584337073761131256443290788 * 10 ^ 70 +
        3730294774035908440652611997202534819380345895818179776024711553406678) * 10 ^ 70 +
        6152367424082239121441072688498939100387959961641406086474454182009395) * 10 ^ 70 +
        4204898030936236169912529363479704517853051168592159285782358999882285) * 10 ^ 70 +
        4079360118821031923110312681293700455582202829182724849033300931111820) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 46 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_135 :
    recurrence5Scalar0Exceptional.coeff 135 =
      -(((((167334732688652395230873110004624232449436838 * 10 ^ 70 +
        7134091279639842785270149645280263231190348242376527853336964300047021) * 10 ^ 70 +
        6037196503680204837848729414029419236656090782775186453238984111436217) * 10 ^ 70 +
        5043417280343223185459210916780634883431427933130347349503862252687280) * 10 ^ 70 +
        0442548811812774444836742079901341787211862756866666423421153183009885) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 47 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_136 :
    recurrence5Scalar0Exceptional.coeff 136 =
      (((((1415018711939226040194772028409440812260738085 * 10 ^ 70 +
        1075117670280321308288187237377145862719257800175483595087282176494024) * 10 ^ 70 +
        2873531362425776952160020825927827710242220334769569992483691026826975) * 10 ^ 70 +
        0517796994232295460143296239955891671563927457768043793517607311517560) * 10 ^ 70 +
        3614607090500284694209720390657609225719897904141406031385038473409579) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 48 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_137 :
    recurrence5Scalar0Exceptional.coeff 137 =
      -(((((8126309234369952038477011288252929362803203944 * 10 ^ 70 +
        6894393427157239293437402310961223241275184597877059986444422266171757) * 10 ^ 70 +
        9337878309238944841541287666500862692718904100640246675937714966472429) * 10 ^ 70 +
        3594817980156280835754682329448496180639495084647102898133690466986615) * 10 ^ 70 +
        0992621877821300237591713757850768321192448697096985505629615292447259) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 49 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_138 :
    recurrence5Scalar0Exceptional.coeff 138 =
      (((((36093836761652156229760399898655938744360303185 * 10 ^ 70 +
        5246502943910003876730723087130628385756704782335088524290045981014405) * 10 ^ 70 +
        7082579941833765398058224959042962692588147887940567828934135777327555) * 10 ^ 70 +
        6403461595490504230526838066004171670714194916442384716251868195318660) * 10 ^ 70 +
        2441249181605238519432395456073881062743587079586950135156723943338519) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 50 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_139 :
    recurrence5Scalar0Exceptional.coeff 139 =
      -(((((119065973921396929711923938347197565612754627519 * 10 ^ 70 +
        8569668511534196710042548726207718331033213116991237133357684690322353) * 10 ^ 70 +
        8678968086796375788764787539839452783653850208103545764065104880524284) * 10 ^ 70 +
        5949336849357809115256749104360735529092562071528037775645682534350608) * 10 ^ 70 +
        4974046247317058708363674478949953165450179359772417047834676975583219) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 51 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_140 :
    recurrence5Scalar0Exceptional.coeff 140 =
      (((((189457153594056564608977735758520534721893222335 * 10 ^ 70 +
        3972310349779186723697110556056255673836194850648690410779813812226704) * 10 ^ 70 +
        7242093798466208553314850486164817894757823706013170988996713728748166) * 10 ^ 70 +
        7756680451661534678744014241463484217156424721022429711614874506540014) * 10 ^ 70 +
        6241562569250823622657501495548899338936560622129076033509133340950238) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 52 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_141 :
    recurrence5Scalar0Exceptional.coeff 141 =
      (((((1044456211767639054107931508478307088982195544896 * 10 ^ 70 +
        9584841051454474928439464543611662780905418547578248388291889491377277) * 10 ^ 70 +
        7745686708802592000381369027216273488703353372358181161121810950840493) * 10 ^ 70 +
        1945824940330383293173044302965008091373891187711767121983719558760429) * 10 ^ 70 +
        4856330692034227597831616218787859313914513302744924363325295716370622) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 53 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_142 :
    recurrence5Scalar0Exceptional.coeff 142 =
      -(((((12787879059958233939913400243014811480468859696342 * 10 ^ 70 +
        0435108195113533079210445019508981022917206081218630756275788991078878) * 10 ^ 70 +
        2320103134484302844862006013687498709903643689406605198286514776511624) * 10 ^ 70 +
        3646981136321218484084738534222603839904628714947464120585922478381686) * 10 ^ 70 +
        0553611510847141480519357076957031224120331686152204754109277475235776) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 54 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_143 :
    recurrence5Scalar0Exceptional.coeff 143 =
      (((((83482148941455734061145958113069469229188714001113 * 10 ^ 70 +
        2838183183412045147500838167069615424598344286231601526287492561468139) * 10 ^ 70 +
        8040525865694820280709801945523485947092840508949506535460368410036278) * 10 ^ 70 +
        0083134370441136460798133921159344534163338488378194544798071172678232) * 10 ^ 70 +
        9301107070616782556990491164046841838325900114224347541155934641961242) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 55 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_144 :
    recurrence5Scalar0Exceptional.coeff 144 =
      -(((((419071096205044107623307026454397124018081517968020 * 10 ^ 70 +
        6508521231167292680525098383321534690869892781377802144713146106902327) * 10 ^ 70 +
        9266948543826801255287234300494232085294378409488716264408137083388538) * 10 ^ 70 +
        1108950461455994512839108636597355691584680357162473928177827556356354) * 10 ^ 70 +
        0435404865945810633731725983447130273562132523406270664812821809253928) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 56 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_145 :
    recurrence5Scalar0Exceptional.coeff 145 =
      (((((1713118177403843530162646415006599304054454812454720 * 10 ^ 70 +
        6412642361773187738029424042631108855648339835209443954929509316734100) * 10 ^ 70 +
        3175633475360692746681380757131753346176798495415107828737694475863022) * 10 ^ 70 +
        6365708587151342319459004910206737925079639131845890200190226211820658) * 10 ^ 70 +
        9704607087525138119695960659579532281648556872117420576759654675590154) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 57 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_146 :
    recurrence5Scalar0Exceptional.coeff 146 =
      -(((((5483520256161502296293233482780588549586807554639967 * 10 ^ 70 +
        9993696115497077006600914816210614923875183583778311862719117771877765) * 10 ^ 70 +
        8041717247050154300729841366194163323234377617942731340099684166891865) * 10 ^ 70 +
        1934444891839951934001681753115987035589788304467615726667778314033155) * 10 ^ 70 +
        4710155142612093495710700460174009212965669619869702147214587315693886) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 58 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_147 :
    recurrence5Scalar0Exceptional.coeff 147 =
      (((((10425486673945173634986981709561745187705025063223498 * 10 ^ 70 +
        5585175442397778284735761648612572657654062752403400703238679725503844) * 10 ^ 70 +
        6136370795936600513313442119925097642487003763218960054830044607102924) * 10 ^ 70 +
        6791185234360463460338298589771201195834055330001756242531315855172920) * 10 ^ 70 +
        2676956779855537801016054005378416280395954301776887193070892827573971) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 59 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_148 :
    recurrence5Scalar0Exceptional.coeff 148 =
      (((((22885884442987911215564246266432813753042453680975937 * 10 ^ 70 +
        8670482767643677585160815563930976118527095669170287123162650765237272) * 10 ^ 70 +
        3277875243707608168459640821451504284284844326809402854443871128946874) * 10 ^ 70 +
        5974327627233891165052182031779996360176712043452335228091243945703497) * 10 ^ 70 +
        0825914851368913278622045210698934981245228857016104024577467388710425) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 60 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_149 :
    recurrence5Scalar0Exceptional.coeff 149 =
      -(((((383352199793034888647681465993563489938909627094456300 * 10 ^ 70 +
        6959526768774118009278166691096855185223095744026635496189041306598623) * 10 ^ 70 +
        7369944076423637706877450423484912467592701567633278017474189757351661) * 10 ^ 70 +
        2825610028685856821222327623480273420695056805733850582440347398026301) * 10 ^ 70 +
        2770577501922029740491258398136170781844627828593115397503265851999843) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 61 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_150 :
    recurrence5Scalar0Exceptional.coeff 150 =
      (((((2629425553740252078413257140931190436713587159453202761 * 10 ^ 70 +
        7362916481253439618249531364862316993761605173784511364345263207588438) * 10 ^ 70 +
        4243393800737824755466802122761054618469702080188385852757430027335128) * 10 ^ 70 +
        4166211367402442933951010395020961815550644123697582502228215974118928) * 10 ^ 70 +
        9133226633604831992627451770030022983112755572853358502687019680815133) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 62 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_151 :
    recurrence5Scalar0Exceptional.coeff 151 =
      -(((((13797186723314056186091367480922765664437746908362539086 * 10 ^ 70 +
        4163698098614549905001775103191816214388515921380999403152227411979326) * 10 ^ 70 +
        0803325881460347603041219536378891340485102598176840254415232175420085) * 10 ^ 70 +
        9073227508000900324278949031734495629948350651824327440916879945085330) * 10 ^ 70 +
        7166431420954180896374445134537210555785714687243100565865665797509257) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 63 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_152 :
    recurrence5Scalar0Exceptional.coeff 152 =
      (((((61282865653459130686644247308627522279089493274615467270 * 10 ^ 70 +
        3298504251478896783443317688943149815176559830565195420066965911381179) * 10 ^ 70 +
        9888935142470287862529992866715258642825789772534261834501025878290809) * 10 ^ 70 +
        8077997682176418807284043557993567004148208585263155674972414193325841) * 10 ^ 70 +
        3753929050208842050939297382395663720360428367787787128668151764443508) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 64 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_153 :
    recurrence5Scalar0Exceptional.coeff 153 =
      -(((((235716856910579900792591359083590686022981708936338577058 * 10 ^ 70 +
        4266052369046944544639195453476878847094941404235188634384773851780840) * 10 ^ 70 +
        1686553073047796641415007496625971029351181877788902386197557150890395) * 10 ^ 70 +
        6792526535941514869499674268068048913408710671992439321014225599648189) * 10 ^ 70 +
        4028353198958138427046629293220316295919938976955545408285949080336789) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 65 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_154 :
    recurrence5Scalar0Exceptional.coeff 154 =
      (((((769944116946885254729937801025360941272477293239988111587 * 10 ^ 70 +
        3755504182160993863491228752418182061124858466013070417602964784592452) * 10 ^ 70 +
        9889110703380812414415537502672736103582375282206210621514777395555525) * 10 ^ 70 +
        6794024773011607505133071137583589449555207550773768602721973911909964) * 10 ^ 70 +
        4780964198688425181281970207507108079398100628844313322734102645763278) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 66 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_155 :
    recurrence5Scalar0Exceptional.coeff 155 =
      -(((((1932957111697049574456593582907322785946379850996096655640 * 10 ^ 70 +
        7996367353598944450325971239046370282473635130557249963826820785055628) * 10 ^ 70 +
        7089285469512986357810747611422848132389897388939812364130269815148046) * 10 ^ 70 +
        7395467255286202091540115745089483473812327351460719679950110186342040) * 10 ^ 70 +
        0819278631046607267725421406818058592520451129245797303825260344885403) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 67 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_156 :
    recurrence5Scalar0Exceptional.coeff 156 =
      (((((1928710763112071015487461689161257895118833764618490736230 * 10 ^ 70 +
        2556802441158163078675340893135441972409866967091218674068196209769686) * 10 ^ 70 +
        1438219644379698230986449593579984851581733065377470730124690266593394) * 10 ^ 70 +
        5408401289585541369323719609214213809289374781519998745949724023889033) * 10 ^ 70 +
        5690954654590450913673455362338471399174747692288825071857182119605366) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 68 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_157 :
    recurrence5Scalar0Exceptional.coeff 157 =
      (((((17401578958498116425857120457613758943174664620091865709177 * 10 ^ 70 +
        0927296035238903260040477689482168162129112055565099779416462556084255) * 10 ^ 70 +
        8129740573557803065271358796306988403397631830954906614741813976291466) * 10 ^ 70 +
        0462021925878628588179586950309783193522891150862131536055816319715729) * 10 ^ 70 +
        8172668881560867123125540318848014718516610774059742919408300499513619) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 69 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_158 :
    recurrence5Scalar0Exceptional.coeff 158 =
      -(((((165856902435986118764191065104210795574363288760471887581149 * 10 ^ 70 +
        4664296238226669784838669216379853753983152576237418670632626991216934) * 10 ^ 70 +
        9356081511251957880035911003448118837931138909139109410098920943182249) * 10 ^ 70 +
        7274829137339506953515069077824757380029547798675488463121914857705999) * 10 ^ 70 +
        2626850157424852775159744491993245501089329066103227903359610126795671) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 70 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_159 :
    recurrence5Scalar0Exceptional.coeff 159 =
      (((((991737137257035246427918300618893894859924496607503295851793 * 10 ^ 70 +
        0969186334442918143138644539614260178752677782728955954546727075278346) * 10 ^ 70 +
        1185918333840239151845112755925962315811387315982500279269187970123019) * 10 ^ 70 +
        9558900936389671907288782196774068754333492265165285331464947246277113) * 10 ^ 70 +
        2719658190249908357041993577340095727087798315497548943754317833966207) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 71 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_160 :
    recurrence5Scalar0Exceptional.coeff 160 =
      -(((((4943971955663308312730378544239134851308135712205099567030796 * 10 ^ 70 +
        1253586706184898501918407661302035880115467517580506303860764775952034) * 10 ^ 70 +
        8240376792055793240481052322691691637637579942115627715830289897562958) * 10 ^ 70 +
        8703560705325112950441852115955790469534242971196947281839987088616930) * 10 ^ 70 +
        6724729612018073983608909681811601361609245274294309206650297264507263) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 72 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_161 :
    recurrence5Scalar0Exceptional.coeff 161 =
      (((((22132735456624273767071919719422725498732165830838207416580704 * 10 ^ 70 +
        6254055479969459051568127215553704539163590620338244924677768851178874) * 10 ^ 70 +
        6346190984288510057070246521229547271011471033016972276909057540909710) * 10 ^ 70 +
        2622443636864162240958109054953124671142645841323862482015525305507914) * 10 ^ 70 +
        6875543999472147126739620078425049151701230008882936807684683959954968) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 73 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_162 :
    recurrence5Scalar0Exceptional.coeff 162 =
      -(((((91803168643103489259691268713015531013736266413360905812592782 * 10 ^ 70 +
        8877878468756268546099265813769190537823921878786247002636857680096242) * 10 ^ 70 +
        7653607220156815362594858343245088571301108092024675433364102538920064) * 10 ^ 70 +
        2205765578202135795923897151316711216300574632088273997069028699726575) * 10 ^ 70 +
        7884255569681825465965327012732908253166686735999669948509088957539770) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 74 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_163 :
    recurrence5Scalar0Exceptional.coeff 163 =
      (((((358658257845380123446048570131954987490524535419647947393414786 * 10 ^ 70 +
        0831355960900334390449177621285725696314996721803748561920790780529757) * 10 ^ 70 +
        8524737631071185601600574389931603204994963277200269684043845881210152) * 10 ^ 70 +
        0918623003115818597109692260459500470251775292952020218552694803106783) * 10 ^ 70 +
        8265728299896524376935295731407682002777935285255206985702677245475668) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 75 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_164 :
    recurrence5Scalar0Exceptional.coeff 164 =
      -(((((1332870437747403673633073555999340846400559356213484231869852030 * 10 ^ 70 +
        9813203394513575927574197464783944593748581567564157424449505639610765) * 10 ^ 70 +
        7155165489269107767709820940162018000373058495097159908510751236463959) * 10 ^ 70 +
        6141177864967950615140436543117093363097567009540917756695377669286512) * 10 ^ 70 +
        0916964993565020603657686601094053400025007667931044478348985781677316) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 76 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_165 :
    recurrence5Scalar0Exceptional.coeff 165 =
      (((((4742316206766491899531423326375905940134503283794286580524754317 * 10 ^ 70 +
        4111222368438804540706197879817552043759174618528998123863156133088826) * 10 ^ 70 +
        6085329705758926377979701352118030953553277002472007846128253497398982) * 10 ^ 70 +
        8137389318835833480539201623060000763379626334928348130533641322079996) * 10 ^ 70 +
        0987380670656188981146934470571757690071284704909970921711376717962946) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 77 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_166 :
    recurrence5Scalar0Exceptional.coeff 166 =
      -(((((16227698221409909674230801461984090485953833234568348030251186078 * 10 ^ 70 +
        2237036954795139709040987639956693208451306592989970026555335309252616) * 10 ^ 70 +
        1787441313155619934955855725199636907583006768341069360339630773451017) * 10 ^ 70 +
        8128477526442294677355730009287588636747332373513895759876274602073646) * 10 ^ 70 +
        6182205769098306269367368129628364984140102402977198544806263236131220) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 78 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_167 :
    recurrence5Scalar0Exceptional.coeff 167 =
      (((((53583831255329113079837624218549867213489791843981206976650050405 * 10 ^ 70 +
        4319775531939129958400594641839893798412045771702140633280250419813570) * 10 ^ 70 +
        8661689076123956681994903486350577827805438601869079704488645090403103) * 10 ^ 70 +
        6991154072276859549962461990891075040355570573649314785793054491274965) * 10 ^ 70 +
        8316705781533720360170745525737526851792152376247582206663893167210292) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 79 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_168 :
    recurrence5Scalar0Exceptional.coeff 168 =
      -(((((171168945085937591938621001163024436413822147730217396849802689313 * 10 ^ 70 +
        8343376448683425265167085814100913424342642173705047386716460021070321) * 10 ^ 70 +
        0298655179424696388870458702292185037060711840503756040869714242200374) * 10 ^ 70 +
        5273586570705205936073378815550286113597419598691819233273601341158542) * 10 ^ 70 +
        3119592277437799906655841320592735016841825154986552567978115800948833) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 80 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_169 :
    recurrence5Scalar0Exceptional.coeff 169 =
      (((((530027813875093355411503857173046452695027639031112459630100522740 * 10 ^ 70 +
        7189825752640446786447006436551894492300394450286396433306768235231186) * 10 ^ 70 +
        6406777067811995316244750488663931043328569428214583704503583154049451) * 10 ^ 70 +
        1076681557976970385935351852618696390095708098267886391907866072268131) * 10 ^ 70 +
        6120285863452366399648867301483600656475743246469440987466201826805047) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 81 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_170 :
    recurrence5Scalar0Exceptional.coeff 170 =
      -(((((1593508003251467639626182832005391814556411482029073402154222791841 * 10 ^ 70 +
        1368999734013672869711017660116290696848858365598620278054484610416921) * 10 ^ 70 +
        1553292643884044001070282469445567690689221544524615775043293550054287) * 10 ^ 70 +
        7976921926044558950423992280244427873802339566184506594389299474970631) * 10 ^ 70 +
        9593938708356204029563884308045362328957160099338894480954052359349105) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 82 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_171 :
    recurrence5Scalar0Exceptional.coeff 171 =
      (((((4657647684097225035243641264973447207287863913860151962586782777223 * 10 ^ 70 +
        8235113929749958977843497856162235779078648217988774592137756158642555) * 10 ^ 70 +
        0567136561636581768260705122178551760889860750763060169622885799121421) * 10 ^ 70 +
        6910290152175540456864916824691203004143249517301038226474681108410351) * 10 ^ 70 +
        9673081642240915490764178297748414116921730079419205173508150483453598) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 83 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_172 :
    recurrence5Scalar0Exceptional.coeff 172 =
      -(((((13250011843095014681565639033661190004630458626690290760263550320533 * 10 ^ 70 +
        0278257126122656374390265564713743937350155750067527322703285875056634) * 10 ^ 70 +
        3743947487363350287457892694471545296562248765127618348007870312456261) * 10 ^ 70 +
        8872298670732432941193561978453307335401163083129485692521642297761784) * 10 ^ 70 +
        2465130937236743389879709221105674707207692597746987201963069277293090) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 84 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_173 :
    recurrence5Scalar0Exceptional.coeff 173 =
      (((((36720645510162508235401999515204803480864036637460539548297002954111 * 10 ^ 70 +
        2533225351270785617873394607288083805771600693901324310946957868942892) * 10 ^ 70 +
        7857596555759251815775474072000993887912507102798985821081367475005260) * 10 ^ 70 +
        2454008886632816012378728012459760296580208685980011455886934860403171) * 10 ^ 70 +
        2294444408244269370106108753436154496662361579238192655252575693078049) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 85 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_174 :
    recurrence5Scalar0Exceptional.coeff 174 =
      -(((((99219698444416109434048646677652982252042199830831758816900332080747 * 10 ^ 70 +
        4314912996937172356065705478423842172466423584895007959450486098467210) * 10 ^ 70 +
        2249038683382030767051113998999033502249494280892625631797524968019467) * 10 ^ 70 +
        4557119883774617690428778828480963830820042746723681901685292065818992) * 10 ^ 70 +
        5444268659313244113232936013905769039110488201502496195601271499145716) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 86 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_175 :
    recurrence5Scalar0Exceptional.coeff 175 =
      (((((261566106267409736701735585899844117648758272788979762898773712971197 * 10 ^ 70 +
        1770227296198727473267337986426022822072568899469115862368872412751659) * 10 ^ 70 +
        1095743234057406130472195584449929102397168501904796871687829620432334) * 10 ^ 70 +
        3613364518731950210624020636061417435804072838304848454792935586459367) * 10 ^ 70 +
        1368608126081636974963625309988594058304949448470751044109937197222827) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 87 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_176 :
    recurrence5Scalar0Exceptional.coeff 176 =
      -(((((673170666716529464923735465887377497740041733703139860568479118096853 * 10 ^ 70 +
        7061767086026575456762577743379612471865092174030692585489363987179124) * 10 ^ 70 +
        2259297166015269804897470067350938020601422005632933921549719339005635) * 10 ^ 70 +
        5112508627442655847328603004347158876314070938905253038600111207373972) * 10 ^ 70 +
        0734858774638231155307831051878301258058680447360630088236971195356104) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 88 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_177 :
    recurrence5Scalar0Exceptional.coeff 177 =
      (((((1692238302342390273689948611703760951425312820895379200023939632725067 * 10 ^ 70 +
        8385832291593907726995658680635018444847493807586115036124781748363570) * 10 ^ 70 +
        2996378867784342063985429805465927289360828245220700414835919525927968) * 10 ^ 70 +
        4693848601455599414424939958503460762673369748412721410442918823733472) * 10 ^ 70 +
        7119392238511475409534305431507669024080689318401266173407847383834984) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 89 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_178 :
    recurrence5Scalar0Exceptional.coeff 178 =
      -(((((4157155911704409876725091647701692617290920458542747690492278978755029 * 10 ^ 70 +
        7092452495889195894584985175417997651489172758078464953930867280852454) * 10 ^ 70 +
        7223858845686775492332561909701211714664535350323941976128159020155654) * 10 ^ 70 +
        8011783497036169733205715071320994816694193383678530249203432902970655) * 10 ^ 70 +
        2229125260474561589537869272332584391374355432875531752819310752346513) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 90 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_179 :
    recurrence5Scalar0Exceptional.coeff 179 =
      (((((9984188290166810625155517972984421420812532414411315125639077807372186 * 10 ^ 70 +
        5669508270336450295414185613683087495563924505452067763291748481878336) * 10 ^ 70 +
        4394393547768883942992371528156801726514916736093789650100856395973238) * 10 ^ 70 +
        2501161561473714777521771572328730007190683643832371254353846181281118) * 10 ^ 70 +
        2946410943566120130316537167111250568650957168122420793309251156058858) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 91 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_180 :
    recurrence5Scalar0Exceptional.coeff 180 =
      -((((((2 * 10 ^ 70 +
        3451716882772655971595197490276495414860167852170163207205539541134154) * 10 ^ 70 +
        5832608447398688516223894452917258673470035488140829201828462695202712) * 10 ^ 70 +
        0305963979165280686905710354899722934470666840102875110760837589467674) * 10 ^ 70 +
        0024996073333339979887477271806000781658928735462619088664320630782896) * 10 ^ 70 +
        1984090802068374651695650566309833905477456529693302964218568074664203) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 92 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_181 :
    recurrence5Scalar0Exceptional.coeff 181 =
      ((((((5 * 10 ^ 70 +
        3892567631162289205378113337879714359350427576318873520641525341958618) * 10 ^ 70 +
        5794373357611008252694746316671773646418663265649067884584322933373347) * 10 ^ 70 +
        1255811251111439404830301865176697034095781833966097678392181634527560) * 10 ^ 70 +
        1710805991704188435605070508077933578651015606150175619229302401441516) * 10 ^ 70 +
        1913889039690825095954339738844073813972645280478739754460490623644036) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 93 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_182 :
    recurrence5Scalar0Exceptional.coeff 182 =
      -((((((12 * 10 ^ 70 +
        1201400250748368219827950401203816831523279636161199267400170381379682) * 10 ^ 70 +
        5819841262793207382752848929782868003566149570202786590015962400181762) * 10 ^ 70 +
        3957236334308742890602123733024696380022250621267173754990002487985401) * 10 ^ 70 +
        3893277707371549924310757483615644111291105350086923327435758730733194) * 10 ^ 70 +
        9907752243303387763503801179071874371792424965147127056344848246761698) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 94 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_183 :
    recurrence5Scalar0Exceptional.coeff 183 =
      ((((((26 * 10 ^ 70 +
        6827190015662802641183313670790428327271209039974249185566148159847975) * 10 ^ 70 +
        8918517864414230752101230898243742700192447465464759942912591546461294) * 10 ^ 70 +
        3291392627203295694399097456952588679873320054851096379493603850168704) * 10 ^ 70 +
        3578001568499059316168597323982365851823180245304663299230222060346287) * 10 ^ 70 +
        0098623445991543382690357793574981735494313602478599461983619292046191) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 95 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_184 :
    recurrence5Scalar0Exceptional.coeff 184 =
      -((((((57 * 10 ^ 70 +
        5179989086523446644180795599745525219511545506364940335681939319200376) * 10 ^ 70 +
        0502490872727088469780642625412123589791713370780510199248031190850526) * 10 ^ 70 +
        7293206863760373046169706494255206525740955936525865346115103441909626) * 10 ^ 70 +
        2969486125985123885954968113756636731249210021523780080071603985146672) * 10 ^ 70 +
        8657710657165058880310745756107403283770867060976591089577549822209666) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 96 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_185 :
    recurrence5Scalar0Exceptional.coeff 185 =
      ((((((121 * 10 ^ 70 +
        4299552935600502712812194525951334574809571489533425168005513686187408) * 10 ^ 70 +
        3561995624877278662873549072201417250834470674995483785468863420249949) * 10 ^ 70 +
        1597927057966084528028542294391966012435741028431512114842803952595665) * 10 ^ 70 +
        3915794282385812913861651009264111699317720772850916614050418805980962) * 10 ^ 70 +
        5790655582809190499215544951177985120411791647861744899982704391477670) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 97 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_186 :
    recurrence5Scalar0Exceptional.coeff 186 =
      -((((((251 * 10 ^ 70 +
        1215551750229611937624250645284491896191328879925927529660199227149402) * 10 ^ 70 +
        7778659628190026237605068342411913803018549197220305208492809003058741) * 10 ^ 70 +
        4688349835791985578373329114701341931833479948661143772576281570780448) * 10 ^ 70 +
        3397478855125423282911431891600830545763119917066902787668883064381488) * 10 ^ 70 +
        9570461135527033775991928343267548720095293153202165684265437713338064) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 98 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_187 :
    recurrence5Scalar0Exceptional.coeff 187 =
      ((((((508 * 10 ^ 70 +
        8119895043011357031628029079089525139561726265312631424716745822514849) * 10 ^ 70 +
        2655106443214303720463384515958265669540253551264987849137142366427174) * 10 ^ 70 +
        7535066712164364289647251896184627530950402988672672555453193292370136) * 10 ^ 70 +
        0938004465917715868934386552854375743233439189576543464824002715837717) * 10 ^ 70 +
        5057460788854983229097212851062865051668133736618139684129424141417970) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 99 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_188 :
    recurrence5Scalar0Exceptional.coeff 188 =
      -((((((1010 * 10 ^ 70 +
        2224948494269363478389414809649317799075560330710068539195177700598121) * 10 ^ 70 +
        6517954328261416182122036186800908073668131336060861793255822897169086) * 10 ^ 70 +
        5481157782117681392637814443137897175695678679120212356371635388809235) * 10 ^ 70 +
        5255078986618238655826762043384429548669613085655783785880230281016477) * 10 ^ 70 +
        7340704104827488100828921238070945051163067562139789760887762118771875) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 100 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_189 :
    recurrence5Scalar0Exceptional.coeff 189 =
      ((((((1965 * 10 ^ 70 +
        7436979284926022443687136206676173551722609569213630430210694340132868) * 10 ^ 70 +
        2367649481241741915408765394729036778874479039964509073835261513562012) * 10 ^ 70 +
        8471953969489427896372020577146122618312630644227858609405969010958403) * 10 ^ 70 +
        5972457786356028648229267126415778251204669413073180672469347542201821) * 10 ^ 70 +
        1820097260647894184714389494836379356527465534117539452118759403728834) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 101 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_190 :
    recurrence5Scalar0Exceptional.coeff 190 =
      -((((((3749 * 10 ^ 70 +
        2449515214815627357476573396697403270181195143110577403228997413796056) * 10 ^ 70 +
        9783479720847991044557564006875144431214587893291086969392485574974708) * 10 ^ 70 +
        0466906401578536619646511472180493878738131944380258728796282833535198) * 10 ^ 70 +
        7415160929110819142282945998676894358398805204196007037162142485578743) * 10 ^ 70 +
        5562515184721451140458298396684286188669296716985294752221455813600024) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 102 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_191 :
    recurrence5Scalar0Exceptional.coeff 191 =
      ((((((7010 * 10 ^ 70 +
        0028294504068573265345503608729700482066230899817442776327842244887380) * 10 ^ 70 +
        6206343186988612339336802618743265457922662239412519142078212630460537) * 10 ^ 70 +
        3373579125628609508208586482385031715266025357575777668414421862970886) * 10 ^ 70 +
        5161625857243165210412634800540866036784278150694309323622431109712403) * 10 ^ 70 +
        9532376834228015318289642041285495833028226086402851321677785812517659) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 103 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_192 :
    recurrence5Scalar0Exceptional.coeff 192 =
      -((((((12849 * 10 ^ 70 +
        7356887032872058675390116377083681834588876240436833079846416237498973) * 10 ^ 70 +
        5005614013063304548089891610915683450903870074239387781663399145018959) * 10 ^ 70 +
        9262853080373558745730621193959372073390075279484971147352696409131855) * 10 ^ 70 +
        5934980043257090111030756077424034098613292777913311521323494793395951) * 10 ^ 70 +
        5365674318939281778284190592349510590397258398506475911970636078549118) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 104 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_193 :
    recurrence5Scalar0Exceptional.coeff 193 =
      ((((((23094 * 10 ^ 70 +
        5761529180307573572727220998720918088705242326271160877790676525433459) * 10 ^ 70 +
        0782293598226317446122410864838193019569932670386999980312708661970169) * 10 ^ 70 +
        0700800747430708315576947158082272303139675520707647223983538427613060) * 10 ^ 70 +
        3464487389342690231149860185020601705944967461914759034058843467775561) * 10 ^ 70 +
        1452135293403025088656711689846891601696681012810252011923259123531737) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 105 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_194 :
    recurrence5Scalar0Exceptional.coeff 194 =
      -((((((40700 * 10 ^ 70 +
        3312173727303083823561882609326966757232339435802397222692298079870748) * 10 ^ 70 +
        5781797439926024499868540461230003173309078649392643357174544714001346) * 10 ^ 70 +
        8249061369878922088992846130888699609826098987973197519418612724516916) * 10 ^ 70 +
        6855070369606594474009638233584307066200514046101606031170579894915989) * 10 ^ 70 +
        3653939343557818566492210423932502418324616716483449562308901874271617) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 106 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_195 :
    recurrence5Scalar0Exceptional.coeff 195 =
      ((((((70337 * 10 ^ 70 +
        1304923228558340427633516570405537647659590499423407300945436094492841) * 10 ^ 70 +
        3633775260648523660560522284999108034877894619251027392512264305399948) * 10 ^ 70 +
        2202679417551694020218756002838298818987416506172645160943995689630791) * 10 ^ 70 +
        2962736773307678484416823763676338462091715088845488846977866392539526) * 10 ^ 70 +
        2165274985997934748317966759214062947938436677630641782295262787313545) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 107 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_196 :
    recurrence5Scalar0Exceptional.coeff 196 =
      -((((((119204 * 10 ^ 70 +
        0506008476381416230178707847482922857598485510912105911053667126859094) * 10 ^ 70 +
        2691354175801587028017952453703385714322049979509022644113887192956096) * 10 ^ 70 +
        6490799352742246760779279028419042363297122970857665997059500365361896) * 10 ^ 70 +
        4507628221794753490399687317468327341632241136533319674503316610592126) * 10 ^ 70 +
        3197516982022303885759539876862976995075735731985910748128985668437389) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 108 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_197 :
    recurrence5Scalar0Exceptional.coeff 197 =
      ((((((198121 * 10 ^ 70 +
        7777156940139854754207740026499873960992207254538868799501420934007685) * 10 ^ 70 +
        2777563034268786389547550704442375372436541596157578359415158063687247) * 10 ^ 70 +
        9931711459258663385651219587830817023374384895246183247903608829134059) * 10 ^ 70 +
        2648155029049740498078253620453326107257170438658748988229389934557424) * 10 ^ 70 +
        5538882094340938769600500398965971024398545377833672243108450243096208) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 109 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_198 :
    recurrence5Scalar0Exceptional.coeff 198 =
      -((((((322936 * 10 ^ 70 +
        8431748250666965143916560334733544174041887694887880077341375784317228) * 10 ^ 70 +
        1921586781145898466426322300143963381328376882693747309881641166707028) * 10 ^ 70 +
        5027850981617380420341400510673391102748074473234102705431920987070311) * 10 ^ 70 +
        3560706609973169438752349146433601640033133824482105761982203416262637) * 10 ^ 70 +
        7145750050332584639644917261055422450169537879349171866694165201118220) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 110 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_199 :
    recurrence5Scalar0Exceptional.coeff 199 =
      ((((((516238 * 10 ^ 70 +
        6145418803508960184575571813951722966811360786425559676656188094996534) * 10 ^ 70 +
        9812930713353770494044580364125003896656457808993760409237421687566725) * 10 ^ 70 +
        6193307384244145338307442996633192952370783498919758110597210195661271) * 10 ^ 70 +
        3857507807108707675673365666139799631915038210089000696889328172850657) * 10 ^ 70 +
        8830194145377637168948831250592383250435964073727898224842703174821325) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 111 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_200 :
    recurrence5Scalar0Exceptional.coeff 200 =
      -((((((809334 * 10 ^ 70 +
        3420483145815168916942547149015242619006477323584219014312964306234185) * 10 ^ 70 +
        7721990448547050626687740595933900049582833955606934033244493719240068) * 10 ^ 70 +
        5433275882913759878918666483426646958756461345240757606797625506742511) * 10 ^ 70 +
        1213588892606733591846002311381637075504911201958795150370848815861468) * 10 ^ 70 +
        3236153503703687639466432017274791769792078324934263254134055825222394) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 112 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_201 :
    recurrence5Scalar0Exceptional.coeff 201 =
      ((((((1244344 * 10 ^ 70 +
        1962815801213687409324504525336680580013631890502242323346895598003548) * 10 ^ 70 +
        6419069230017071392701551390274656246366059103031993952121968680986032) * 10 ^ 70 +
        3537225884872898883493311268274435652910145430191292138804186564500451) * 10 ^ 70 +
        2201634199753196969532717734286999467517776535860941735590317490358945) * 10 ^ 70 +
        3575671413896479496934092147881257525391457623012466931021589175134184) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 113 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_202 :
    recurrence5Scalar0Exceptional.coeff 202 =
      -((((((1876167 * 10 ^ 70 +
        4748102031442464986196564016652589317951575900292581128309700678035769) * 10 ^ 70 +
        4637939946889056568320986979967134282305235593069734245687538631253012) * 10 ^ 70 +
        0788362003889591203445055379172288420089806848355872072330136303218067) * 10 ^ 70 +
        3433100415114956978543805986859607843906026119550735088188249445447044) * 10 ^ 70 +
        7723777609072993571749828837148023918528288033900248263229171550365834) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 114 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_203 :
    recurrence5Scalar0Exceptional.coeff 203 =
      ((((((2773939 * 10 ^ 70 +
        8190148507410516962695481869333117650570572266429706067213245367431269) * 10 ^ 70 +
        0393134126488044327098003419590475842256662163196762174966407915208317) * 10 ^ 70 +
        8344699798507938047104961224315783403503636118934037783211218953707279) * 10 ^ 70 +
        2824503221277845748058755422807017112028956883890299611654050557656292) * 10 ^ 70 +
        5892420708180656050002667035995601001132311418663616671349965792423072) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 115 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_204 :
    recurrence5Scalar0Exceptional.coeff 204 =
      -((((((4021465 * 10 ^ 70 +
        4472954730348406766908643149641589080579034171402069580070204690200950) * 10 ^ 70 +
        4229867505533661774084885191307405648270994171107788877960094773614949) * 10 ^ 70 +
        8803117567453206346893551235526491908044032491326861186227400399953615) * 10 ^ 70 +
        3226841878907354243248097923980615425876466621096259361474184602383172) * 10 ^ 70 +
        1482254645377583732279734166357899885793402572768717560367409558479776) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 116 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_205 :
    recurrence5Scalar0Exceptional.coeff 205 =
      ((((((5715994 * 10 ^ 70 +
        9339031471891675142222890807189560562985816729374189602127532291702784) * 10 ^ 70 +
        4124384802656960279474209569799614523418758783782403967885439431496097) * 10 ^ 70 +
        2306737622657687427102416857902918714647020123339419134986753682019496) * 10 ^ 70 +
        4598932298974136652189416998112011559288166331961296996046232961802374) * 10 ^ 70 +
        0669143887981895955141398828277209156807745712638541388399665023726789) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 117 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_206 :
    recurrence5Scalar0Exceptional.coeff 206 =
      -((((((7964664 * 10 ^ 70 +
        9880622964789147860857341698375388619885069650386245188239477285932011) * 10 ^ 70 +
        5284266610084337833563075714026102325194069785016362130716365780009688) * 10 ^ 70 +
        7585481271203177051260768898885217812117916788639181099027242014395496) * 10 ^ 70 +
        0239809123976833784764845590460892195432549928719272275992603882743198) * 10 ^ 70 +
        7442397242491486174806067772373510998515599110853317186422378307912175) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 118 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_207 :
    recurrence5Scalar0Exceptional.coeff 207 =
      ((((((10877965 * 10 ^ 70 +
        4962531864268599940649550822492108495982570799598287953409466742495143) * 10 ^ 70 +
        7739533072834070769250312966514504408458685756304941127429520440974063) * 10 ^ 70 +
        1507888899953610574850730958988484693245667868302778603131445542338366) * 10 ^ 70 +
        8939895300979171310497291684884874903802452894824374864743906309326321) * 10 ^ 70 +
        3792805356329971137960857265557427330688443184221146289318451474906905) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 119 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_208 :
    recurrence5Scalar0Exceptional.coeff 208 =
      -((((((14559793 * 10 ^ 70 +
        1232552169639476311273887449369229758138625895435761141837253874499678) * 10 ^ 70 +
        3363565391413021613927551668094945397321255118707926355478556823428020) * 10 ^ 70 +
        3474708565295561216624798318023445119612316688323430590052499368535442) * 10 ^ 70 +
        2797325359956437378164694758240465010773109401722184375462700211357258) * 10 ^ 70 +
        0898958933311088903263783380556972714069918859666691620273160805320329) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 120 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_209 :
    recurrence5Scalar0Exceptional.coeff 209 =
      ((((((19094020 * 10 ^ 70 +
        0017683511269361751185880621554562160647260969059045687136834975231754) * 10 ^ 70 +
        7678947403575438145062979605034104748803457620339870422867623387050250) * 10 ^ 70 +
        3449659326054843202922017352817148107323161498075215739168801264727330) * 10 ^ 70 +
        1033757974180401951779456063138510103237820882070863917992730690331488) * 10 ^ 70 +
        3512276574202057327644770711539056778856088166721283508229511135096216) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 121 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_210 :
    recurrence5Scalar0Exceptional.coeff 210 =
      -((((((24528054 * 10 ^ 70 +
        6076183140589851027978957875340008403947805665469122864379139398889596) * 10 ^ 70 +
        0578306253006404133501491415602285689947076851516562688785604478590713) * 10 ^ 70 +
        4963862937973692229579389109136528019767398148940298559988892012577506) * 10 ^ 70 +
        6866608840873669051212187258866221035172500350437142651675371272607548) * 10 ^ 70 +
        5738732992052200550527812874974430387738482479405718024181762757794808) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 122 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_211 :
    recurrence5Scalar0Exceptional.coeff 211 =
      ((((((30854565 * 10 ^ 70 +
        1514450777907399384072491253614454889963620579356627345035384751080670) * 10 ^ 70 +
        4652566246782781237605605329945668318802164037148088341275573650746970) * 10 ^ 70 +
        0664809987619680005972111472067141187021559629168215186393018015190790) * 10 ^ 70 +
        5614829873167161150478440358785272226252639319176752004393920557778989) * 10 ^ 70 +
        5617740055932153724517253120900009366994492047470549069395951535251008) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 123 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_212 :
    recurrence5Scalar0Exceptional.coeff 212 =
      -((((((37993291 * 10 ^ 70 +
        7656168616049666382298081648134388381319944291881934627740903221490391) * 10 ^ 70 +
        8255876311323372326454980518832211994792327744542016208409230264597361) * 10 ^ 70 +
        4614005174858990521629687421221298052940215811118425891434217486760931) * 10 ^ 70 +
        6412233632271254052824820321413304482743111202514774997935106307866632) * 10 ^ 70 +
        0236757729436993895759720487711734893746715885737851413993641280210502) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 124 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_213 :
    recurrence5Scalar0Exceptional.coeff 213 =
      ((((((45775563 * 10 ^ 70 +
        5111018309558120496381795706831852894627983863179534834576822043297644) * 10 ^ 70 +
        8352531783198322418045725472267231256796190805677312510504046578409171) * 10 ^ 70 +
        7735868248964940440127595021179584501017572261175651229499182280762804) * 10 ^ 70 +
        4508632003018063891772994707384591046257046776319099778137500638121161) * 10 ^ 70 +
        3161331870126471984172378647496558035883421322719587342659067754553840) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 125 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_214 :
    recurrence5Scalar0Exceptional.coeff 214 =
      -((((((53934596 * 10 ^ 70 +
        5837283369037940225220609055681973731213469144325714849465820197278540) * 10 ^ 70 +
        9548291907170165235265000711914205430067723781106714788233734486860438) * 10 ^ 70 +
        4805161655387318222070932710135280401456420402439983537299808350744748) * 10 ^ 70 +
        3348994271048830159984143989098235698142997553546535590975087412132186) * 10 ^ 70 +
        0090640853486450450650467892456501443424066795475533207311255008270769) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 126 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_215 :
    recurrence5Scalar0Exceptional.coeff 215 =
      ((((((62104709 * 10 ^ 70 +
        9609378863655903853449523525782014018687677949902437294052522040934615) * 10 ^ 70 +
        9135991164457849464383973006120699766176753410217660329811266416052944) * 10 ^ 70 +
        2273055541553267192038239377903029401707725667406774699832656154961570) * 10 ^ 70 +
        0883353252864966415668299379349852566166871263758337686364965274690945) * 10 ^ 70 +
        7726413507557173558742766437658823236726719973811379871232991509943137) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 127 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_216 :
    recurrence5Scalar0Exceptional.coeff 216 =
      -((((((69832112 * 10 ^ 70 +
        8898913853680158476820900138048437893817965529052039493445925538507785) * 10 ^ 70 +
        3181489408516156837808548709013311371958774121896551889418682583236975) * 10 ^ 70 +
        5712775343910708277982393481518176405688236698784128534612489699028951) * 10 ^ 70 +
        2149097110048074952848268996073204512295395446302695603530172603395917) * 10 ^ 70 +
        4811757589006641515794265628734501871177448272359788245211043649390631) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 128 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_217 :
    recurrence5Scalar0Exceptional.coeff 217 =
      ((((((76598826 * 10 ^ 70 +
        6405368873578925982842642545096032273544700757169999202279518774203182) * 10 ^ 70 +
        1668473577009538886067613925183259038907258805816107895954825299580829) * 10 ^ 70 +
        7881249350703877940120484060383017470093461080477759899955576794654958) * 10 ^ 70 +
        5618891358218594805382204252107835225844262375964754453697659219267196) * 10 ^ 70 +
        9241371170010141759901004842915780357459591723334939105066804514739803) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 129 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_218 :
    recurrence5Scalar0Exceptional.coeff 218 =
      -((((((81859643 * 10 ^ 70 +
        1548089593908338397904972442219785249049482412703495366885023963392831) * 10 ^ 70 +
        3302340382355147861927806653904774039362682279039540728465143773728664) * 10 ^ 70 +
        5843418497555932511257876807054077839949683065667112796019267022482483) * 10 ^ 70 +
        4514698245193690275740559517654945354787810296473721264541759064787462) * 10 ^ 70 +
        1351062839558912586589317629050864417275679028650804027868457254440719) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 130 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_219 :
    recurrence5Scalar0Exceptional.coeff 219 =
      ((((((85089970 * 10 ^ 70 +
        0841018599604080666416080552889860851145914220137349765275709861175428) * 10 ^ 70 +
        3077661823374036748840610815816239541498667705774986451046555041971432) * 10 ^ 70 +
        1875479019052224093363585277498976655909713784426132779637457913701627) * 10 ^ 70 +
        1303835031586932377218254775243362704159543253523151942410747524034660) * 10 ^ 70 +
        2234938217202014235504511712389119963507453525484194396637991460119653) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 131 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
