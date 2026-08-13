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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
