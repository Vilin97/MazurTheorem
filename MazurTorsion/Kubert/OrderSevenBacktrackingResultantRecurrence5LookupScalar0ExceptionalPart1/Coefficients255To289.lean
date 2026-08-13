/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Exceptional coefficient convolution

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

private theorem recurrence5Scalar0Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_255 :
    recurrence5Scalar0Exceptional.coeff 255 =
      ((((((779825 * 10 ^ 70 +
        0808417969438452345960826725796097779678647998538146070099022800924348) * 10 ^ 70 +
        5150604394713651160415178821404264161884808559005276998299929389963921) * 10 ^ 70 +
        9136184455185865261421004606704782544404942864738343473461496487590590) * 10 ^ 70 +
        7037851312874690429278946902260189916610617238579904328000711108435453) * 10 ^ 70 +
        7740692367668375115638480577653681226037877763974499045953445536283990) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 167 +
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
  rw [recurrence5Scalar0Exceptional_coeff_255_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_256 :
    recurrence5Scalar0Exceptional.coeff 256 =
      -((((((545541 * 10 ^ 70 +
        8770036587577033449782008098452834670630620730094179801697557710506552) * 10 ^ 70 +
        3092284289832930800865169501503413110769323245511604117076297286188166) * 10 ^ 70 +
        8251379928802739093501002369147335642153305551170574071731567134807933) * 10 ^ 70 +
        3537244212659380737934552128477253311534286009894219735547392065552508) * 10 ^ 70 +
        7637616208717231703113448484961115404135282032336832952136241099797984) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 168 +
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
  rw [recurrence5Scalar0Exceptional_coeff_256_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_257 :
    recurrence5Scalar0Exceptional.coeff 257 =
      ((((((370180 * 10 ^ 70 +
        0499413355368911741170904319683293715090722679116633581222184819976682) * 10 ^ 70 +
        1233078309779657716912500622729403400694145277256621586993209538768555) * 10 ^ 70 +
        6670515944922045889831980138628032689282190575261643742748022844410757) * 10 ^ 70 +
        4955785558003698800023008272663808711333139502869868777193313849355917) * 10 ^ 70 +
        9424320742484097617136527907889958514155697338703399194801264084052535) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 169 +
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
  rw [recurrence5Scalar0Exceptional_coeff_257_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_258 :
    recurrence5Scalar0Exceptional.coeff 258 =
      -((((((243575 * 10 ^ 70 +
        5458862720069739592551727994033082149017312747865321749109450270905122) * 10 ^ 70 +
        5869639904909428664337046221322518389988589432251249481245652021735757) * 10 ^ 70 +
        9820669943673439082495192747324340929578341385646349656530868268441389) * 10 ^ 70 +
        0174257351795252265528274954279152467710981368526603555783932458260249) * 10 ^ 70 +
        1518686541176236673771001530757856351966690994416695501975063157663160) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 170 +
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
  rw [recurrence5Scalar0Exceptional_coeff_258_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_259 :
    recurrence5Scalar0Exceptional.coeff 259 =
      ((((((155274 * 10 ^ 70 +
        2212389478055452281891297839131102484158604081544789431905123901905963) * 10 ^ 70 +
        0431844193858437600183874620508837959613809556902326500180877951928387) * 10 ^ 70 +
        5900376136764897258093233270935932618109359530897352012589708722913551) * 10 ^ 70 +
        6365666554895847450532638768051619565019240112334675343460297710402423) * 10 ^ 70 +
        8606876811659582668630295960294927545237091920192874634944697720614029) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 171 +
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
  rw [recurrence5Scalar0Exceptional_coeff_259_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_260 :
    recurrence5Scalar0Exceptional.coeff 260 =
      -((((((95736 * 10 ^ 70 +
        6074934386732764247459941837537494114732439145456902320363191321179239) * 10 ^ 70 +
        8903667528818962935196964412738902337815503030694148004949485670323441) * 10 ^ 70 +
        4234859035137780291616223183524268788315892055011359358791081497738708) * 10 ^ 70 +
        4346250080310468032603511408060960523322890680709525872522772666215675) * 10 ^ 70 +
        1593851439424983865124957160704724774265116424774599500338807057286582) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 172 +
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
  rw [recurrence5Scalar0Exceptional_coeff_260_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_261 :
    recurrence5Scalar0Exceptional.coeff 261 =
      ((((((56932 * 10 ^ 70 +
        6166418383807289310649054340094022582098476587861197725885183009858469) * 10 ^ 70 +
        3817675495552508592071489785403095182684927493162497283138484872880088) * 10 ^ 70 +
        3493080925209962565810798823292042918767555067941008531066219324788804) * 10 ^ 70 +
        9132642971392321423603603047477327841637151687079660705450999130730444) * 10 ^ 70 +
        9298863547202335728326513666969748412614682166453243114595101879883616) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 173 +
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
  rw [recurrence5Scalar0Exceptional_coeff_261_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_262 :
    recurrence5Scalar0Exceptional.coeff 262 =
      -((((((32509 * 10 ^ 70 +
        2646498111140800413705784916290232964613554604211906465583041703688222) * 10 ^ 70 +
        8566993893250532812372346486354151388355724309787411857094476546995891) * 10 ^ 70 +
        3612831121732986063248438088898384954328189570630258476409932177362026) * 10 ^ 70 +
        6479069977829362312541264447808858270621998144306990757219650045499356) * 10 ^ 70 +
        7347595812902106254481924166776149733934128988829078129649096135782416) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 174 +
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
  rw [recurrence5Scalar0Exceptional_coeff_262_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_263 :
    recurrence5Scalar0Exceptional.coeff 263 =
      ((((((17694 * 10 ^ 70 +
        3628826451571084545418029281126725104808817520952376729831766896111840) * 10 ^ 70 +
        5995495175137333548705221309088299445422462069879937750419468881497046) * 10 ^ 70 +
        7859202053174356352621486111045397819509185973876728697204473708540506) * 10 ^ 70 +
        1727379116543537166324203563986891017941361725144705436354651675404918) * 10 ^ 70 +
        2718396324213706845237080191908312308628839879509623983780151117134530) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 175 +
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
  rw [recurrence5Scalar0Exceptional_coeff_263_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_264 :
    recurrence5Scalar0Exceptional.coeff 264 =
      -((((((9064 * 10 ^ 70 +
        1719683200544388286840678672566257917742094575468192749831135995269294) * 10 ^ 70 +
        1405384222445034106068695586978668570089611582061819606893211201966073) * 10 ^ 70 +
        0444174280094523925172973199070028052815356922042242894083788032575955) * 10 ^ 70 +
        3061001647868465927233001839520657016060489166282494362736239510610680) * 10 ^ 70 +
        2547039756211737392754561748155066075015239160652583115114501250040953) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 176 +
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
  rw [recurrence5Scalar0Exceptional_coeff_264_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_265 :
    recurrence5Scalar0Exceptional.coeff 265 =
      ((((((4264 * 10 ^ 70 +
        8001453095266641121116584896543055324477816940594159474784842310953181) * 10 ^ 70 +
        5393082958380036101974535271187239878183718344256359656571650380232866) * 10 ^ 70 +
        1023624092722034922432143890006876852095071973160177887026819854137554) * 10 ^ 70 +
        3846978630720032364631741398921614488004970864359289799470988523741854) * 10 ^ 70 +
        9973145686527364533383813636507549308051231988958534661414287373648028) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 177 +
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
  rw [recurrence5Scalar0Exceptional_coeff_265_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_266 :
    recurrence5Scalar0Exceptional.coeff 266 =
      -((((((1742 * 10 ^ 70 +
        9059198139911590431114404301453754844889068813199721680563694226850694) * 10 ^ 70 +
        0800376083451263134499388550120685637954470091566427082920076217659023) * 10 ^ 70 +
        6435854388029384681102584621527506030045522903687511160296324753876237) * 10 ^ 70 +
        1436915111960074454477707134353319296816385101862153361743713441755000) * 10 ^ 70 +
        5708552899662795306723030756396309795378334480402596121007565305381768) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 178 +
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
  rw [recurrence5Scalar0Exceptional_coeff_266_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_267 :
    recurrence5Scalar0Exceptional.coeff 267 =
      ((((((514 * 10 ^ 70 +
        5079966859034356395470624530653209832114071158213158900056607161887526) * 10 ^ 70 +
        1373489824094236707887313898901197213716043778910661757919280489843385) * 10 ^ 70 +
        4940425037566871091134739142990374491715744699392812001762785690772507) * 10 ^ 70 +
        9514805180433892163912854532608208702914660793065730331076336684810040) * 10 ^ 70 +
        2461345853673296108443089395753179976737958614816023927969738904995376) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 179 +
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
  rw [recurrence5Scalar0Exceptional_coeff_267_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_268 :
    recurrence5Scalar0Exceptional.coeff 268 =
      ((((((17 * 10 ^ 70 +
        8614813593292298344496647742525252179022563536643077012488591589852349) * 10 ^ 70 +
        0012266211254808735494441268598024633942677456352669245980347063870799) * 10 ^ 70 +
        5473921801860817297391562095824656005166748533533825064286588265038492) * 10 ^ 70 +
        9884948774808100053857272630664113594166271200669091163327517229465706) * 10 ^ 70 +
        1186110800991225624612780302696888867017797221215032324544027801330253) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 180 +
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
  rw [recurrence5Scalar0Exceptional_coeff_268_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_269 :
    recurrence5Scalar0Exceptional.coeff 269 =
      -((((((200 * 10 ^ 70 +
        7379080002611428390410801385677102743841557411068183427823749914546087) * 10 ^ 70 +
        2780187019656503702180826037452198998079146262260301812483540933735326) * 10 ^ 70 +
        1712143522802727110937322066238945718043961706642907243877050359475043) * 10 ^ 70 +
        9371471115752945445769435070056883142193932766492269916670232123194593) * 10 ^ 70 +
        7021320647953017375272179753980363925094392765240535571246229987548383) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 181 +
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
  rw [recurrence5Scalar0Exceptional_coeff_269_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_270 :
    recurrence5Scalar0Exceptional.coeff 270 =
      ((((((224 * 10 ^ 70 +
        8614769319275318108530373518744409177769895887358566655029472450250434) * 10 ^ 70 +
        8071834798836000508291327559999998916412487265259746871273057910449475) * 10 ^ 70 +
        0384811921252425643175351771169708057899036907912413939230384939408528) * 10 ^ 70 +
        7634136304842245754627886636648872735393372158687536155511899563576319) * 10 ^ 70 +
        1321815843020687893357034288061918176817954394205903219665636086009065) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 182 +
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
  rw [recurrence5Scalar0Exceptional_coeff_270_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_271 :
    recurrence5Scalar0Exceptional.coeff 271 =
      -((((((188 * 10 ^ 70 +
        6637920003834135867674387956554209487895166184848166412139374680437768) * 10 ^ 70 +
        3474625154239651466790913111381912419308725499303027764393928383589839) * 10 ^ 70 +
        5106258398644329735201108703173738947858287042592153518474475125721695) * 10 ^ 70 +
        7550183639577248020629472255763886956772498098026676912002820615846535) * 10 ^ 70 +
        5290161595133759579109186063355536267814734008057259943589238035551475) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 183 +
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
  rw [recurrence5Scalar0Exceptional_coeff_271_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_272 :
    recurrence5Scalar0Exceptional.coeff 272 =
      ((((((138 * 10 ^ 70 +
        6387613161801658840136037787220730833819750227560159482603057775934616) * 10 ^ 70 +
        9942190764596056919535236098104089884770476533853431853630420385081670) * 10 ^ 70 +
        6846842868232556786359598375708696171755798710022051211530335252013017) * 10 ^ 70 +
        2569140065357304733320048107261716155241369967241021804621002475841308) * 10 ^ 70 +
        2810726712763814189509210320685269781407717579684268219845722414295206) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 184 +
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
  rw [recurrence5Scalar0Exceptional_coeff_272_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_273 :
    recurrence5Scalar0Exceptional.coeff 273 =
      -((((((93 * 10 ^ 70 +
        7941753409941404240444650789848506827902976185849964720258276827444930) * 10 ^ 70 +
        4420984436476465223516949922674487123680822596866971905611236490027984) * 10 ^ 70 +
        0748650235959905677968284833746303297989816996096770648363295262587334) * 10 ^ 70 +
        2618522510105709580601734342330876063950719590036437766416011073676520) * 10 ^ 70 +
        8227756411287685121287896426862812884908093601169809198492267798084442) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 185 +
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
  rw [recurrence5Scalar0Exceptional_coeff_273_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_274 :
    recurrence5Scalar0Exceptional.coeff 274 =
      ((((((59 * 10 ^ 70 +
        7115056333923836235782315820971382046246681263011604204820361795765463) * 10 ^ 70 +
        3037348485200031762093203030866521355393374947793261732403454457178768) * 10 ^ 70 +
        4538029696241688478003733117353086284424001197096592810571087936987422) * 10 ^ 70 +
        9440818912708589880871670597032549087394282751590443242022746701789073) * 10 ^ 70 +
        3352486067857359571258643644645121555722092854147112524960296698605438) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 186 +
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
  rw [recurrence5Scalar0Exceptional_coeff_274_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_275 :
    recurrence5Scalar0Exceptional.coeff 275 =
      -((((((36 * 10 ^ 70 +
        1647263399594236553749976498350552563575096717689838912267943561260937) * 10 ^ 70 +
        3470204156788463261793727742056145773079231311831163035059995937527274) * 10 ^ 70 +
        9143998350763212139609103917222381190351419250713287282275674862363127) * 10 ^ 70 +
        2671279683541304482503382721944827176034678111606910091446878500772346) * 10 ^ 70 +
        0608785153712406902966013221271110583437280837256902406947257674899162) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 187 +
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
  rw [recurrence5Scalar0Exceptional_coeff_275_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_276 :
    recurrence5Scalar0Exceptional.coeff 276 =
      ((((((20 * 10 ^ 70 +
        9538461440370069986505155279642730064190254523488983314129151357454965) * 10 ^ 70 +
        6473288705292821894574376585202236338539419005321043242170680812890913) * 10 ^ 70 +
        3101209456788384400056124711600045658055424334269318097449778838918381) * 10 ^ 70 +
        2736942809507481216795598625528811466693674374927294560142214375474155) * 10 ^ 70 +
        1996375376606074144173547953768460517234145003027670758692243720922887) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 188 +
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
  rw [recurrence5Scalar0Exceptional_coeff_276_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_277 :
    recurrence5Scalar0Exceptional.coeff 277 =
      -((((((11 * 10 ^ 70 +
        6402454746389040047162690238430710330731719008737678983939089596176504) * 10 ^ 70 +
        6684527469245138297057163335871239157881959162328200766173924711861888) * 10 ^ 70 +
        1553994335086115070289658148682315916999559355067193512642348890286012) * 10 ^ 70 +
        5047069219534694250620251282037828215938769575057170711305397530865510) * 10 ^ 70 +
        0277317016846361167541444230275799803906054255468663684364549714779464) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 189 +
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
  rw [recurrence5Scalar0Exceptional_coeff_277_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_278 :
    recurrence5Scalar0Exceptional.coeff 278 =
      ((((((6 * 10 ^ 70 +
        1976323733171381961620585493335965181433042724380915310824155610873769) * 10 ^ 70 +
        9653984928175089691050415978203215902645056931171304447282172768577792) * 10 ^ 70 +
        6135716073386560407828548689766791709747793125769827766889825082025548) * 10 ^ 70 +
        0635535923927558698370788945450918528390579922320768275136111047352926) * 10 ^ 70 +
        9132642002741538464951358223786657313467981167987010953522066362513183) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 190 +
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
  rw [recurrence5Scalar0Exceptional_coeff_278_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_279 :
    recurrence5Scalar0Exceptional.coeff 279 =
      -((((((3 * 10 ^ 70 +
        1531069922812740045427755980637725964469751341132159896802663067023343) * 10 ^ 70 +
        4266527510519030930105773929769959887181015886946113324651965881984734) * 10 ^ 70 +
        9727793631888941061676032931092082508662010406241007647392267073983628) * 10 ^ 70 +
        2238191356009058100870703579962560500881601191233921337870389000474913) * 10 ^ 70 +
        8494338394844138195713496934514982653419742203837368176663515391155811) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 191 +
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
  rw [recurrence5Scalar0Exceptional_coeff_279_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_280 :
    recurrence5Scalar0Exceptional.coeff 280 =
      ((((((1 * 10 ^ 70 +
        5226616168999460030427739816621652582531999831690157329142959089232947) * 10 ^ 70 +
        6257621384533024021340859093098804971796187239627792632152811044865121) * 10 ^ 70 +
        6727350189124478466593358158595644197786322910949175493333112685080466) * 10 ^ 70 +
        4459873870077907477142368941744360250679916154248005726554589314556402) * 10 ^ 70 +
        2588838824396229827524537218941000797460299727111085134260646001241361) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 192 +
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
  rw [recurrence5Scalar0Exceptional_coeff_280_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_281 :
    recurrence5Scalar0Exceptional.coeff 281 =
      -(((((6889768018083371028670633566571540941032012068757255126269035345983775 * 10 ^ 70 +
        8687334723895176746055581237253062734214036958291973103718685119214373) * 10 ^ 70 +
        9268345062516246196017108134725172215504114281786958259870766236000845) * 10 ^ 70 +
        3227106558211801222659816050351792632890211884646074604330059042272825) * 10 ^ 70 +
        5147498507195506267068079950525987609621690938088242322284388544999453) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 193 +
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
  rw [recurrence5Scalar0Exceptional_coeff_281_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_282 :
    recurrence5Scalar0Exceptional.coeff 282 =
      (((((2845440244570482218846254807004037133507690479810171369706939613260539 * 10 ^ 70 +
        1907308226829830919913786813993928118140899926039713725086059923768880) * 10 ^ 70 +
        1056638205135620382961160503579843225575237163224963291886456490379064) * 10 ^ 70 +
        6212312154327274578432412339264940473176036068331204071957111247551461) * 10 ^ 70 +
        7494675916057743710646911499617953920079428040668322262917710049250453) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 194 +
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
  rw [recurrence5Scalar0Exceptional_coeff_282_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_283 :
    recurrence5Scalar0Exceptional.coeff 283 =
      -(((((1007209215560642040169586751673491003632085268974798270449389469845430 * 10 ^ 70 +
        0580625802605954540672265433044023719810436362783838173164730214552908) * 10 ^ 70 +
        4469670381993067995654622346534162401551725795074651855471820155546214) * 10 ^ 70 +
        6636206381478633528511588407010488939851250089962916409626139318395607) * 10 ^ 70 +
        4834990927661068311555328664266676118920675663880462133750056898157405) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 195 +
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
  rw [recurrence5Scalar0Exceptional_coeff_283_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_284 :
    recurrence5Scalar0Exceptional.coeff 284 =
      (((((244065136359568000093842825154992310226793660241644583555159945983218 * 10 ^ 70 +
        9696817363067570720088163571941210393405934754220928833612477195876854) * 10 ^ 70 +
        5623599776762064270971595004936476837163606463154683976544001944197269) * 10 ^ 70 +
        6590212290965373446941988996479206352398802665814631405322661456173758) * 10 ^ 70 +
        9747730645955493895886487654624412230523895613862881516142545574404243) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 196 +
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
  rw [recurrence5Scalar0Exceptional_coeff_284_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_285 :
    recurrence5Scalar0Exceptional.coeff 285 =
      (((((28288038323035477932883863519319826605222888161852820788508473286134 * 10 ^ 70 +
        5149972246772256533679894686172482910611889995276551569072124367867585) * 10 ^ 70 +
        1450787051966536587016531476183827053040397580655425028236207079767202) * 10 ^ 70 +
        7547220402788943053294369646270687531889980212188577161670795418058030) * 10 ^ 70 +
        8804191981792928673647367988593929110209131491550076789234659807335939) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 197 +
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
  rw [recurrence5Scalar0Exceptional_coeff_285_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_286 :
    recurrence5Scalar0Exceptional.coeff 286 =
      -(((((95888840537029312493592202046159183264004375353780025403046267797909 * 10 ^ 70 +
        5248837793030529669040126640130439670087685998648860298406600070481427) * 10 ^ 70 +
        7035131622754386757640045154351829508016572022362905682655774169297156) * 10 ^ 70 +
        4690760204424344105877313375590560357953888788741256530112919840466286) * 10 ^ 70 +
        3760378330442752858177123920353362976636327575226280674335783220181580) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 198 +
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
  rw [recurrence5Scalar0Exceptional_coeff_286_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_287 :
    recurrence5Scalar0Exceptional.coeff 287 =
      (((((89874919858216498964504785138281642019644356246435507060492627577906 * 10 ^ 70 +
        2219174334155690807439686703986519438334771319430615201410521621477118) * 10 ^ 70 +
        9875957301452737731877625685786092775133674648937624013301580043483726) * 10 ^ 70 +
        2180825772651730886749130391454301833566392887063419207727973818425052) * 10 ^ 70 +
        4179162932774556314419867608039345410733040611875305065799512069342900) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 199 +
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
  rw [recurrence5Scalar0Exceptional_coeff_287_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_288 :
    recurrence5Scalar0Exceptional.coeff 288 =
      -(((((65207880504948520473279947305864972824316724276851017071947420673136 * 10 ^ 70 +
        7451280036890335040377122866537676206710564402109266628538629525845816) * 10 ^ 70 +
        6973415464974723344146728168484281425934274750946335232600127709362400) * 10 ^ 70 +
        2794088642465785236764919773807934461362108682312830941869752707437606) * 10 ^ 70 +
        5477281636476184279678535027430490828111244116373318931575338599998990) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 200 +
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
  rw [recurrence5Scalar0Exceptional_coeff_288_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_289 :
    recurrence5Scalar0Exceptional.coeff 289 =
      (((((41780198995733693422676260369709601746176515342667572968546404173513 * 10 ^ 70 +
        6629523467909702225339959732191845936185924328713360071619204192632961) * 10 ^ 70 +
        0756264690665988273442530107415480124646652057922376743066768889466525) * 10 ^ 70 +
        2739782851917154182103055963151958328167674289790337503221072842425549) * 10 ^ 70 +
        3326355257300704265388429719840242267740609179202702572146662281594712) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 201 +
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
  rw [recurrence5Scalar0Exceptional_coeff_289_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
