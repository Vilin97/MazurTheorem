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

private theorem recurrence5Scalar0Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_220 :
    recurrence5Scalar0Exceptional.coeff 220 =
      -((((((85840266 * 10 ^ 70 +
        2455331457885766437075491568336515225685238860812437379557192298249666) * 10 ^ 70 +
        3764903930833486668445532006281474531360168976700184246694365525640845) * 10 ^ 70 +
        8995023384895150624351336932905237357034546174596902983442326673541554) * 10 ^ 70 +
        2058821827688113620674093180569205014124470847544717727177950214963611) * 10 ^ 70 +
        6446479821842498892970972691907233511177564466487104392938782069419247) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 132 +
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
  rw [recurrence5Scalar0Exceptional_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_221 :
    recurrence5Scalar0Exceptional.coeff 221 =
      ((((((83790923 * 10 ^ 70 +
        1676645935090146837858139814703507127158523246179022458962576490303527) * 10 ^ 70 +
        8178855418160275056647764561392490494054093667481192571933615503400298) * 10 ^ 70 +
        5933287734283086773539335842864461821485613245889165069833797944061153) * 10 ^ 70 +
        8426829384396434876317827786054175947708613780582810884261295906337260) * 10 ^ 70 +
        5053609808941265274864333233159254171439308182932905798960970148428978) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 133 +
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
  rw [recurrence5Scalar0Exceptional_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_222 :
    recurrence5Scalar0Exceptional.coeff 222 =
      -((((((78800306 * 10 ^ 70 +
        3950913732320820747914647044112403887669544639838416867565419663982408) * 10 ^ 70 +
        3489919123942837023490921722779293801127912489093434371993401457726429) * 10 ^ 70 +
        1256079736120468630829108014895810065609729283396461547804694837064460) * 10 ^ 70 +
        6799003769090501798599968855544317089916750049430005648461999856747042) * 10 ^ 70 +
        3618854700165852716412796342566406448081427341452336593132568495729172) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 134 +
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
  rw [recurrence5Scalar0Exceptional_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_223 :
    recurrence5Scalar0Exceptional.coeff 223 =
      ((((((70938575 * 10 ^ 70 +
        8053417065244554873590915807919164843769923187040178859376628851512724) * 10 ^ 70 +
        6919646021289459958571383063151260601638953989714137235900533497413835) * 10 ^ 70 +
        7843682106242810202778667270602880872189920354468057769770415793906887) * 10 ^ 70 +
        6782240814586214627493108136957047905660617224167738863407246945163301) * 10 ^ 70 +
        2629625503117830957576148842775921441943501239051317492603677084677759) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 135 +
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
  rw [recurrence5Scalar0Exceptional_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_224 :
    recurrence5Scalar0Exceptional.coeff 224 =
      -((((((60501042 * 10 ^ 70 +
        2103333702527924646509060942781570125619024001326566598953137378628957) * 10 ^ 70 +
        6328053641923848183245620168038094437650506929592747356242134588515041) * 10 ^ 70 +
        5521817118381194027777095486718186818453268018365468238885654529068839) * 10 ^ 70 +
        7827936380374014185268257867075262870095393354816165221465835925485394) * 10 ^ 70 +
        3547205651470035954510196570411311950183277617019436026392435440241720) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 136 +
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
  rw [recurrence5Scalar0Exceptional_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_225 :
    recurrence5Scalar0Exceptional.coeff 225 =
      ((((((47997150 * 10 ^ 70 +
        1831242393798877646608475938465841310298866132379063093736433323179027) * 10 ^ 70 +
        6068969932450667409857517267286526168591457840906341281432636492190698) * 10 ^ 70 +
        2905648478501854766128300056032295669138585603862125729665625169132883) * 10 ^ 70 +
        7537832926640032957616013123379438701023989325099132756174820531318122) * 10 ^ 70 +
        1296864524544585506716151547857661898426927470106489104847925072118947) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 137 +
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
  rw [recurrence5Scalar0Exceptional_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_226 :
    recurrence5Scalar0Exceptional.coeff 226 =
      -((((((34114420 * 10 ^ 70 +
        2752460869509869890033745883164799187898889085198994214555304854328153) * 10 ^ 70 +
        5790683813852957021614789978928638284130036010797629669209544797709904) * 10 ^ 70 +
        2363765998853948414630632415967266398341531471223719906546117288787738) * 10 ^ 70 +
        8062922597035439717775211378813570760531549054349776124392839043916122) * 10 ^ 70 +
        0811981929717713479421438929989081703560941492354190340394404972483738) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 138 +
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
  rw [recurrence5Scalar0Exceptional_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_227 :
    recurrence5Scalar0Exceptional.coeff 227 =
      ((((((19660338 * 10 ^ 70 +
        2574898244128920080717503537624187858802696727028781425016045186034739) * 10 ^ 70 +
        5652888185263254458421038108349160398212089282013858332601703071880941) * 10 ^ 70 +
        7152872000295440410718417076508331949714389077863002057835760102261720) * 10 ^ 70 +
        2962638263446296300006227017484670918165553455849951923223973434236819) * 10 ^ 70 +
        2863876948821376273780545844371494214227000108439231987386866650080831) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 139 +
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
  rw [recurrence5Scalar0Exceptional_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_228 :
    recurrence5Scalar0Exceptional.coeff 228 =
      -((((((5488615 * 10 ^ 70 +
        2183220932700908546624796398941086508884246340193501414420204525746718) * 10 ^ 70 +
        4483904588149722877748417972414749364612984179601478860790322618629652) * 10 ^ 70 +
        5351359711987560774594104008888428773145586949129028097843795555443947) * 10 ^ 70 +
        4477063882087083842331156034821374524576339268900250454969439260194486) * 10 ^ 70 +
        3486507022534010755645512034400646045197504762316737037501927484025505) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 140 +
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
  rw [recurrence5Scalar0Exceptional_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_229 :
    recurrence5Scalar0Exceptional.coeff 229 =
      -((((((7581175 * 10 ^ 70 +
        7371226567215651479568109305358811124315315667385822144048233885011037) * 10 ^ 70 +
        7907268246483660862048779115316523369053775958097346357827797980788296) * 10 ^ 70 +
        8227346052111308677452004699432317969857615192732700765106859708070696) * 10 ^ 70 +
        9103594632229324608101217787979768486364656354359026432735555831515802) * 10 ^ 70 +
        5088441899250848610775874307603650316533158769357660961412665584983761) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 141 +
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
  rw [recurrence5Scalar0Exceptional_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_230 :
    recurrence5Scalar0Exceptional.coeff 230 =
      ((((((18840360 * 10 ^ 70 +
        0725081188228548642676100581612669348026674007903937439785158553607601) * 10 ^ 70 +
        3338694412009367183688062115953351815184268288574609917681028630661775) * 10 ^ 70 +
        7617111626639290297659635703681531114241692069701163320122065186990358) * 10 ^ 70 +
        7323109552584639063867550717094258255421960893593940840042361474991116) * 10 ^ 70 +
        9488797988234567418783502050634551818482697750836216705201152799866583) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 142 +
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
  rw [recurrence5Scalar0Exceptional_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_231 :
    recurrence5Scalar0Exceptional.coeff 231 =
      -((((((27754498 * 10 ^ 70 +
        6346013579964132565297952288444687905942110158992441051203099243250426) * 10 ^ 70 +
        7595642263006686852297637038484329018901599259489387295113427358341032) * 10 ^ 70 +
        3072170689615516213776267996890537404914388317311684335619355115440906) * 10 ^ 70 +
        8124356284691272269267353244934932222380881320810758039883222203264654) * 10 ^ 70 +
        9517191113533436365493966086762812725833897559254664509125678694286348) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 143 +
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
  rw [recurrence5Scalar0Exceptional_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_232 :
    recurrence5Scalar0Exceptional.coeff 232 =
      ((((((34005465 * 10 ^ 70 +
        9532611399172574582890794918084343664057952855129999848344483732589735) * 10 ^ 70 +
        2866527944750106705026578708588961845100108908501899885865167538687845) * 10 ^ 70 +
        4227711955415907273903348178322339042308744330110999202893127977840621) * 10 ^ 70 +
        4376498706789355313205494443459645527505835131702637821006315403884185) * 10 ^ 70 +
        8852449515936714787878288875750902453938982460995287888049994203534971) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 144 +
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
  rw [recurrence5Scalar0Exceptional_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_233 :
    recurrence5Scalar0Exceptional.coeff 233 =
      -((((((37507653 * 10 ^ 70 +
        3976561871486781258101095992618038628935619188090391256739307678817527) * 10 ^ 70 +
        9684876371993243138075540668872799202982235270799383244133985641664606) * 10 ^ 70 +
        5583614446217185217854809252658549533106825037204999803790679171374307) * 10 ^ 70 +
        0737206315019764566125361717894418317061168828129542134490253574289654) * 10 ^ 70 +
        1480861821613720271217212359809596317976969223837093924741747820714472) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 145 +
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
  rw [recurrence5Scalar0Exceptional_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_234 :
    recurrence5Scalar0Exceptional.coeff 234 =
      ((((((38397547 * 10 ^ 70 +
        0038202124625140109739153584031786362971980193238650033280733277142035) * 10 ^ 70 +
        7623455593730540774836971559331056934108077438337796098859617530802301) * 10 ^ 70 +
        1292871385607138141609529216246555384269423151699728256058356734255038) * 10 ^ 70 +
        1066454604122252081661067512765991455497764631739411616714178785979553) * 10 ^ 70 +
        0905519456176959580469650406881454927176853841654916956233851319132130) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 146 +
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
  rw [recurrence5Scalar0Exceptional_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_235 :
    recurrence5Scalar0Exceptional.coeff 235 =
      -((((((36999750 * 10 ^ 70 +
        2858112768608636732377909648538313321443715953459331493594712106072450) * 10 ^ 70 +
        1436136494972353350200560930618689192362345719170138051570518881939135) * 10 ^ 70 +
        5092998109198936206697322147251926932444341861784116311673795014583675) * 10 ^ 70 +
        7508035832623120995151451018632351593212978305586889907711143845431580) * 10 ^ 70 +
        5970549974149890279929225781188695574960563996525873319619132793253377) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 147 +
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
  rw [recurrence5Scalar0Exceptional_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_236 :
    recurrence5Scalar0Exceptional.coeff 236 =
      ((((((33775637 * 10 ^ 70 +
        3084845272230811473732433659573535827757687534636158507653879283199856) * 10 ^ 70 +
        3043656742666084859731364276035478422943226413231828919802776324611651) * 10 ^ 70 +
        2429167974133547488954425746374794423479700462089225273982108868232612) * 10 ^ 70 +
        9417129154786638786751549057650286098138950699582137671703204911463594) * 10 ^ 70 +
        2827386885098298417429444825735734037661729724571389369292284142507487) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 148 +
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
  rw [recurrence5Scalar0Exceptional_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_237 :
    recurrence5Scalar0Exceptional.coeff 237 =
      -((((((29262738 * 10 ^ 70 +
        8195184203436298885738881893072446337990127160063228429039163345521149) * 10 ^ 70 +
        5591352880311807604929554779554179357504726595193910048466794110633067) * 10 ^ 70 +
        7116913210506184111804080995679679412503590916282315853893494930757523) * 10 ^ 70 +
        5402533631377208656479872210173477698262585727756167454118758655429524) * 10 ^ 70 +
        4706462652555915388747426800692961009480416043329321966960894963873319) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 149 +
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
  rw [recurrence5Scalar0Exceptional_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_238 :
    recurrence5Scalar0Exceptional.coeff 238 =
      ((((((24013449 * 10 ^ 70 +
        8967197252210505896626613182189139383603574454192802025587829924671376) * 10 ^ 70 +
        4785876459182000367257652518871591993270534564691888162773397210019735) * 10 ^ 70 +
        9030069570505017806858851152976421665288147192393628676675686609169670) * 10 ^ 70 +
        7036252304795019879450340400134951949889821910306138810061020296517994) * 10 ^ 70 +
        6134406412954990956882495283647906765527130763326100251959063376563377) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 150 +
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
  rw [recurrence5Scalar0Exceptional_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_239 :
    recurrence5Scalar0Exceptional.coeff 239 =
      -((((((18540752 * 10 ^ 70 +
        6322533697603068401581670192212542621590387191187230797256155129486745) * 10 ^ 70 +
        6859689924959695665202751534130423126597316379184441289693948376446250) * 10 ^ 70 +
        8280066438016168665789953874768094196108540289257511625529086082894973) * 10 ^ 70 +
        4702751065623151353889321309434068573621838303825140716754186617644550) * 10 ^ 70 +
        5053937735193329586568686164466016050908628178150809418464757757331987) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 151 +
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
  rw [recurrence5Scalar0Exceptional_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_240 :
    recurrence5Scalar0Exceptional.coeff 240 =
      ((((((13276673 * 10 ^ 70 +
        1628098427117805450107004364527953689508598132631717306661427106409289) * 10 ^ 70 +
        3595331498193077834741722985200878846824759179994967645977940526795972) * 10 ^ 70 +
        8152478894497789833387246203078745228618073463396547111829645004312148) * 10 ^ 70 +
        6798101329785628550264179629143019424712119532842610905159560234617647) * 10 ^ 70 +
        8570130156166589491289752948588738070724306646388658987239093505542197) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 152 +
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
  rw [recurrence5Scalar0Exceptional_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_241 :
    recurrence5Scalar0Exceptional.coeff 241 =
      -((((((8546604 * 10 ^ 70 +
        3800538632934538863978242779962362576943799656787490505356015442703828) * 10 ^ 70 +
        6892705286250382057046645814920318473833922972316011847591806466388399) * 10 ^ 70 +
        3182945922553405327235101384662993947504295483887918760899977255472393) * 10 ^ 70 +
        7764209136392894306050088459133953929807072403065537122659031457394980) * 10 ^ 70 +
        8727081322504230851606587717843520111684205075348077064031575436899447) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 153 +
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
  rw [recurrence5Scalar0Exceptional_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_242 :
    recurrence5Scalar0Exceptional.coeff 242 =
      ((((((4559942 * 10 ^ 70 +
        1745354523599762782697880005812281291050385877101138182180177206687482) * 10 ^ 70 +
        1621894428553426476235539340983465875441905838239128133738975105413878) * 10 ^ 70 +
        2151539284668837455016893821142735083963768060888831010127414280722272) * 10 ^ 70 +
        0533475342307626643591481028068218552500860721718726256828090869651423) * 10 ^ 70 +
        5344395562547584761664499231525683848938731940653516861780624956572709) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 154 +
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
  rw [recurrence5Scalar0Exceptional_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_243 :
    recurrence5Scalar0Exceptional.coeff 243 =
      -((((((1415166 * 10 ^ 70 +
        1808779588521034541324768638949330635769389997973994560409793720557775) * 10 ^ 70 +
        6482220850643367993680437306372494194154890092138443644476906264792205) * 10 ^ 70 +
        0299998033650797157339014189274206993109983919965201146296068709247007) * 10 ^ 70 +
        1890937986697407518658702622264464583953020317947366086057912520771683) * 10 ^ 70 +
        7767590394172024210864092801878276524786460159366699743319464694006115) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 155 +
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
  rw [recurrence5Scalar0Exceptional_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_244 :
    recurrence5Scalar0Exceptional.coeff 244 =
      -((((((884130 * 10 ^ 70 +
        4740149889891664569671915905747379862322363662425316542654347537911670) * 10 ^ 70 +
        0392869999764815559551526000989705486598250592620708847039465428230815) * 10 ^ 70 +
        5511950337809357368711878387264642289608584987980677242650979696611732) * 10 ^ 70 +
        7593928492089225508691431869475342221852969137866344041773624931484572) * 10 ^ 70 +
        7172883178790731572371975927975061136846472036062070364893076980554014) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 156 +
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
  rw [recurrence5Scalar0Exceptional_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_245 :
    recurrence5Scalar0Exceptional.coeff 245 =
      ((((((2406549 * 10 ^ 70 +
        2050635600024809546631885831855790790926671709107236247544090149467025) * 10 ^ 70 +
        3228253607714488219417031352046170587091006344739857170717653778530515) * 10 ^ 70 +
        9112849359575394572376857551468313269394712911899290815099144160779034) * 10 ^ 70 +
        8787241120932336186224618038708740795343720372191643986958801780066874) * 10 ^ 70 +
        8011064014492902435548949935507502686042169594241584414703064146261576) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 157 +
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
  rw [recurrence5Scalar0Exceptional_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_246 :
    recurrence5Scalar0Exceptional.coeff 246 =
      -((((((3267805 * 10 ^ 70 +
        8092136285703403408980980100645182831384508063000739259004767062075962) * 10 ^ 70 +
        2561611872944733212926492078070283722944266227123024287327655126405129) * 10 ^ 70 +
        5630789873638748226197809214631200332961999867862327767717030378003884) * 10 ^ 70 +
        0811556844716833571751162267760955780742070964472598923179150988544031) * 10 ^ 70 +
        7998052494221628656152456430368812890822269072517401208207489349955402) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 158 +
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
  rw [recurrence5Scalar0Exceptional_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_247 :
    recurrence5Scalar0Exceptional.coeff 247 =
      ((((((3606887 * 10 ^ 70 +
        3791631443728910185047832383833905391637417539487406639454356299185207) * 10 ^ 70 +
        3312561606115915256283904115160333117572686351037473721812385750621179) * 10 ^ 70 +
        9661447890013930915574770502419910723845582964566536247417836885785790) * 10 ^ 70 +
        7385049179914207308531452664399835568236439237442490964340187403148612) * 10 ^ 70 +
        4555032750424182145997927527260356474905058945388450467445678461833518) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 159 +
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
  rw [recurrence5Scalar0Exceptional_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_248 :
    recurrence5Scalar0Exceptional.coeff 248 =
      -((((((3566032 * 10 ^ 70 +
        1497795437880098950518418336124149419964839492265341834146855513690651) * 10 ^ 70 +
        3742342527036566070097466661427997871723286782410798355592496337090384) * 10 ^ 70 +
        5393424277030133649441320703155723173390471832981746364910796198473185) * 10 ^ 70 +
        4207422009291861528703355221105526246975720248263083680092720777402922) * 10 ^ 70 +
        2135247755684050475627692615367506821068614629876795581847587973949492) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 160 +
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
  rw [recurrence5Scalar0Exceptional_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_249 :
    recurrence5Scalar0Exceptional.coeff 249 =
      ((((((3275947 * 10 ^ 70 +
        5025778582503324121358064535733184363223423208260441767172562699163057) * 10 ^ 70 +
        8653464452117427724286663175328592590369572638225879726219196627688474) * 10 ^ 70 +
        4647834837213388237419638772005344916626801336331580782574376304500481) * 10 ^ 70 +
        3916743198654534247687474022639979296805777424987876523294537629256603) * 10 ^ 70 +
        6423365437144123969053256520803091839422086845259360343855882985628846) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 161 +
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
  rw [recurrence5Scalar0Exceptional_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_250 :
    recurrence5Scalar0Exceptional.coeff 250 =
      -((((((2846600 * 10 ^ 70 +
        7139790463914812890543336685293501175554390160162705112641642020636912) * 10 ^ 70 +
        6823224750317020163635197450264320197548666320174747013691232143775278) * 10 ^ 70 +
        7739562832312370228709932878561639625663628030677455372056665206135664) * 10 ^ 70 +
        5769690618529625674722747059045811035733643947869272427116326216394613) * 10 ^ 70 +
        2487123254152925018287834911704393000465956939002930596028129520096196) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 162 +
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
  rw [recurrence5Scalar0Exceptional_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_251 :
    recurrence5Scalar0Exceptional.coeff 251 =
      ((((((2363076 * 10 ^ 70 +
        9023204808544958039037921448465037799887214505914440773057458746203169) * 10 ^ 70 +
        6788814599128018060858896924734689923790325514967129182308380310139198) * 10 ^ 70 +
        7557775331193245954535189379565104514099027970461691831380345925072802) * 10 ^ 70 +
        9739544294381939551277753755901983951691826073053549903761611305451229) * 10 ^ 70 +
        5550577074032364760290203205576869464845851330956297468062701419480341) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 163 +
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
  rw [recurrence5Scalar0Exceptional_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_252 :
    recurrence5Scalar0Exceptional.coeff 252 =
      -((((((1885468 * 10 ^ 70 +
        4464606525258990156940897908696483082216933053343317773319718143348194) * 10 ^ 70 +
        3324060670457568793213106277736956063022768710108174943299724755073870) * 10 ^ 70 +
        0577755766876330892570451630065100886983778531810112022410938356513365) * 10 ^ 70 +
        5165259958254735291491799247055742558910941744376798764798708412181452) * 10 ^ 70 +
        0670550867544780419299132287207854877483682367188612956106963826665578) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 164 +
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
  rw [recurrence5Scalar0Exceptional_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_253 :
    recurrence5Scalar0Exceptional.coeff 253 =
      ((((((1451536 * 10 ^ 70 +
        7809927786806527691094252519996815671287570524926458109112874717721843) * 10 ^ 70 +
        7588175155177206911859446120295986828380952211632152719009760587518734) * 10 ^ 70 +
        9423208863843773787262940116392869570635929658628146178379601789998742) * 10 ^ 70 +
        4901134821927648513632012670003489750754185130036293126586630007351900) * 10 ^ 70 +
        2470125481540162920682299850416109537444570395720159515548765421922013) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 165 +
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
  rw [recurrence5Scalar0Exceptional_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_254 :
    recurrence5Scalar0Exceptional.coeff 254 =
      -((((((1080915 * 10 ^ 70 +
        8758517576829717571285139673249299910983829674307345831016774232819063) * 10 ^ 70 +
        9310580269130853409734643183723391658435086499872642401813569336072595) * 10 ^ 70 +
        6381174914674237792796684353726681867470148157265892474011631246538922) * 10 ^ 70 +
        3999600043848220527595940729254210259740922475828656053291367877830472) * 10 ^ 70 +
        8211531328539027007855145707342266480898238874085614920865277628887098) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 166 +
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
  rw [recurrence5Scalar0Exceptional_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_290 :
    recurrence5Scalar0Exceptional.coeff 290 =
      -(((((24722620589150451596371093064716616228177240890335095669791292921066 * 10 ^ 70 +
        2115607264055578969825431971211362128829108206605806893396030248958601) * 10 ^ 70 +
        0123352958021903730145352335456750204614417707541024399457849460596119) * 10 ^ 70 +
        0455303902327404502111348005715497723307251504618555135573636562251813) * 10 ^ 70 +
        6086074486480857973626904560942274182450180825560898551921174842154276) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 202 +
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
  rw [recurrence5Scalar0Exceptional_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_291 :
    recurrence5Scalar0Exceptional.coeff 291 =
      (((((13791009410196858424015138957812760272326047685552166473537813944456 * 10 ^ 70 +
        9396121897932381359407458680110210415470515984078881638850239934749560) * 10 ^ 70 +
        0844503059104220618273948626942214010142666819865546256362958013833881) * 10 ^ 70 +
        1785552672495564824762606251218562011693661415980999396667527495042052) * 10 ^ 70 +
        8394720777972978847596090946044137168251771666039681976806811941010188) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 203 +
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
  rw [recurrence5Scalar0Exceptional_coeff_291_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_292 :
    recurrence5Scalar0Exceptional.coeff 292 =
      -(((((7333679922879434521961650637071297423907016268641410954903060486645 * 10 ^ 70 +
        5963872304239661564801913661663626161943325144058539021994375222662530) * 10 ^ 70 +
        6160414281687979805035581808115499592370668352228940586305453522236302) * 10 ^ 70 +
        2304045252731674898888941476215762579301354188692457706102960424232148) * 10 ^ 70 +
        2212011838479572709472549704757141876248843765712744002638190041974770) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 204 +
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
  rw [recurrence5Scalar0Exceptional_coeff_292_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_293 :
    recurrence5Scalar0Exceptional.coeff 293 =
      (((((3743710810339187791618851037335031400404755643554099237086356827480 * 10 ^ 70 +
        4657280569290090941398155171538969823269564314602736498448437065073614) * 10 ^ 70 +
        1800473965333919848698920765480396172729638422223453260943248690531711) * 10 ^ 70 +
        8982120046656423043957744147202941901120332743502647636007168952874765) * 10 ^ 70 +
        5782351454377425347817472936143244373550201666429185278969861266709403) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 205 +
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
  rw [recurrence5Scalar0Exceptional_coeff_293_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_294 :
    recurrence5Scalar0Exceptional.coeff 294 =
      -(((((1844232845641172689445171637230410124985821124100453069661081305449 * 10 ^ 70 +
        0356235981208039737831609378866909590185019812718080131986629558922593) * 10 ^ 70 +
        9781697845257525247676650326957940970787067862849789331764933648073714) * 10 ^ 70 +
        6414240469015697155034990502277623860033683901199066228900610077302786) * 10 ^ 70 +
        1402077523732349858679493818157227730041164778322132287399662257108067) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 206 +
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
  rw [recurrence5Scalar0Exceptional_coeff_294_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_295 :
    recurrence5Scalar0Exceptional.coeff 295 =
      (((((881242169603997078532045454434369174560627358867835868991331154746 * 10 ^ 70 +
        9151058178844620888682378485750684124475338709184776662322169767465435) * 10 ^ 70 +
        1051430461519702461285472148490121913521351596672832831073208175971032) * 10 ^ 70 +
        8296329820251156808614234786115156471118246103375345174290643086029536) * 10 ^ 70 +
        0613721452183714305304187753726385625111864752989019571771256348477896) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 207 +
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
  rw [recurrence5Scalar0Exceptional_coeff_295_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_296 :
    recurrence5Scalar0Exceptional.coeff 296 =
      -(((((411145686232349655761625633805962541812582239173597470729856649628 * 10 ^ 70 +
        8981023096656427532788925815739487469798792270745870585951940286210956) * 10 ^ 70 +
        8586881696141730005662395120529986132604169392329089928932265397890287) * 10 ^ 70 +
        2497138441900073923842398442265736253532268358822231866469683665371637) * 10 ^ 70 +
        7547712086389800333540827763362546226308986700292536200056036573633102) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 208 +
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
  rw [recurrence5Scalar0Exceptional_coeff_296_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_297 :
    recurrence5Scalar0Exceptional.coeff 297 =
      (((((189125508959352663183068074722102979480097736693364775412433084682 * 10 ^ 70 +
        6038110462894922113916698823624217681816883042184222254245640445279356) * 10 ^ 70 +
        7047727501981869677478208005110823952019641327784172322735466976420732) * 10 ^ 70 +
        5526369654111973410103459953776723168716857413034772077336866512190537) * 10 ^ 70 +
        5852870141572723086012090451425435100307703362109797116007706276756373) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 209 +
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
  rw [recurrence5Scalar0Exceptional_coeff_297_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_298 :
    recurrence5Scalar0Exceptional.coeff 298 =
      -(((((87038062398099127225169966629281617507426854345348502440471921453 * 10 ^ 70 +
        6045332949576185218731328303337775812035859314790852828655241119818249) * 10 ^ 70 +
        1665514041848936381961285038276670605165607767539770683443040070619588) * 10 ^ 70 +
        5313840309685168018473668972213813104948051498578330299112777299778869) * 10 ^ 70 +
        0808817755298005574486677364978443736905639607091092478645622678300369) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 210 +
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
  rw [recurrence5Scalar0Exceptional_coeff_298_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_299 :
    recurrence5Scalar0Exceptional.coeff 299 =
      (((((40879210519236798616187921294481150417137442255301763969063491208 * 10 ^ 70 +
        6643002999520272128022228094288858590379137658850133590280261388486745) * 10 ^ 70 +
        8491485552228363689695428583467457913891718127103198859125799043504153) * 10 ^ 70 +
        4913924068648605577889643300614285260520557429941934514267971798318273) * 10 ^ 70 +
        2698526939194106286974719778334794375060285337719299194800868862524642) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 211 +
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
  rw [recurrence5Scalar0Exceptional_coeff_299_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_300 :
    recurrence5Scalar0Exceptional.coeff 300 =
      -(((((20024195758781286138121119871853313861861571873519502487564337480 * 10 ^ 70 +
        0803512235393501727953976285775462612574037877458039774415034009016057) * 10 ^ 70 +
        9150900693269235556820128842584120845683924306958846226272729724204778) * 10 ^ 70 +
        9298770718399146739739027128738799583682221331974503916644395106885776) * 10 ^ 70 +
        3614516984073726472053485250625152616312511060194769901808150750158323) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 212 +
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
  rw [recurrence5Scalar0Exceptional_coeff_300_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_301 :
    recurrence5Scalar0Exceptional.coeff 301 =
      (((((10387108956453945571349453192631125509224796257105331505081803814 * 10 ^ 70 +
        9958122594290910949939285971910612764623713086168424433868079148794810) * 10 ^ 70 +
        9561122565270086674026931816617214491468409859648673320855429485787506) * 10 ^ 70 +
        1272870422093066417170968313093148057330692553360824169695260617811668) * 10 ^ 70 +
        3091561162157191890238072420067305453275088357018102978888741324834555) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 213 +
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
  rw [recurrence5Scalar0Exceptional_coeff_301_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_302 :
    recurrence5Scalar0Exceptional.coeff 302 =
      -(((((5709035313961992552418868417253382609641539774602119368489464297 * 10 ^ 70 +
        8788640164574503859760148891291989424695773049596598398120303033707879) * 10 ^ 70 +
        1260930980958387045585401717064629529971718038790141435177732882520294) * 10 ^ 70 +
        4917566668794430925441387903189524198183238086002358568816093710748966) * 10 ^ 70 +
        8073822456700638553147606200291748005383294015104531097270649465089199) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 214 +
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
  rw [recurrence5Scalar0Exceptional_coeff_302_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_303 :
    recurrence5Scalar0Exceptional.coeff 303 =
      (((((3277591506828756424513924009532440942434511225672222296257500981 * 10 ^ 70 +
        5610547743766948929691242150677446136793452584645774809127035127000975) * 10 ^ 70 +
        3796207565747420815093388795673826168658723002086014375813106457928395) * 10 ^ 70 +
        4898082223008908083719711282313398797241884731158824402732622004782660) * 10 ^ 70 +
        9744592537164768303032575089427947220913286142626357680212023394815041) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 215 +
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
  rw [recurrence5Scalar0Exceptional_coeff_303_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_304 :
    recurrence5Scalar0Exceptional.coeff 304 =
      -(((((1924730772044749420296808629702460508666335745502130332641847308 * 10 ^ 70 +
        5419142844751798356435675692655180033603627346179722307190053019291819) * 10 ^ 70 +
        2165723684732445498295849059610216362637325331736902519755795610791719) * 10 ^ 70 +
        1337674565062430059342298994138413010663966917855208663715032791628413) * 10 ^ 70 +
        7748644537692546145824121438452987476475267952411304579771250904230984) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 216 +
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
  rw [recurrence5Scalar0Exceptional_coeff_304_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_305 :
    recurrence5Scalar0Exceptional.coeff 305 =
      (((((1134175417342568652139945989063510116460875441160178226444397704 * 10 ^ 70 +
        0913364729699319225877323717299643481384030402961262579443007570813368) * 10 ^ 70 +
        2635432412297002207145565782271279277431712053230737533192010823332331) * 10 ^ 70 +
        6785064336148416049835937776069865529705461582854054396886012921859801) * 10 ^ 70 +
        3786781067232596292875849879115720633963009486985301611489868632650049) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 217 +
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
  rw [recurrence5Scalar0Exceptional_coeff_305_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_306 :
    recurrence5Scalar0Exceptional.coeff 306 =
      -(((((661482148586567267790183092104803328263166701325990936030293571 * 10 ^ 70 +
        5820981817839964257449320560369147090787856478614880876468113600232016) * 10 ^ 70 +
        6459029070089068513544705688550661972014636170527609874693827598876572) * 10 ^ 70 +
        2413094988386587850828037304520473559349568339980527617243832202577627) * 10 ^ 70 +
        9695115449477193619216585973787280428059585963224502723741864819686547) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 218 +
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
  rw [recurrence5Scalar0Exceptional_coeff_306_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_307 :
    recurrence5Scalar0Exceptional.coeff 307 =
      (((((378618175783139515669943989899025179780607168776699388472881649 * 10 ^ 70 +
        9636910469444335649390621869116759213641423092594044491085467029121570) * 10 ^ 70 +
        0743133356806934492605798670926390853620985146566069912043801120634852) * 10 ^ 70 +
        3720928376373013176799585573237411834238499853253118113609160241814290) * 10 ^ 70 +
        4192386896292730742068066952023640458138907142339552541686457922273487) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 219 +
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
  rw [recurrence5Scalar0Exceptional_coeff_307_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_308 :
    recurrence5Scalar0Exceptional.coeff 308 =
      -(((((211679083780959522155967141375993754704019985523051335319960185 * 10 ^ 70 +
        5701178303876512769788322392654487934638581145136853650358115015507005) * 10 ^ 70 +
        5276169318821288283251989974045120572478434636841687475775900613698656) * 10 ^ 70 +
        5937297689761319237322158551536135954854687221602966792266405849895940) * 10 ^ 70 +
        0905662464555114821823355683215516124977208748162599367381939416472148) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 220 +
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
  rw [recurrence5Scalar0Exceptional_coeff_308_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_309 :
    recurrence5Scalar0Exceptional.coeff 309 =
      (((((115317073255441670154405910078761397302168383294592003955066503 * 10 ^ 70 +
        9335991188680859062598158104667861124414937134007638316015647387991056) * 10 ^ 70 +
        0106805306489139687638899281976589533747559532028095973281003489011276) * 10 ^ 70 +
        8924748384927610627874615343246245863524992094757256190558555108996992) * 10 ^ 70 +
        2129430683758094948122444962635803814684847587089704295316749941893906) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 221 +
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
  rw [recurrence5Scalar0Exceptional_coeff_309_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_310 :
    recurrence5Scalar0Exceptional.coeff 310 =
      -(((((61142865331752720584812133640202433631610291262973447430531841 * 10 ^ 70 +
        2687528980769122832037608946243090721691606885380908654257759084734088) * 10 ^ 70 +
        4252967910149003766077527068797368284366569043038245633272633093725926) * 10 ^ 70 +
        1042467685778563282481803499162965146799124732055104248943508502174170) * 10 ^ 70 +
        2651670455021524055252753445569606240491912441909868552670603003523346) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 222 +
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
  rw [recurrence5Scalar0Exceptional_coeff_310_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_311 :
    recurrence5Scalar0Exceptional.coeff 311 =
      (((((31535723147730538168813821902500695878590726317437469084709115 * 10 ^ 70 +
        5301983660186980094388108505922742268781254083124392981156548665198019) * 10 ^ 70 +
        6781437581173281278115432989200424086778937177360363747930115478080116) * 10 ^ 70 +
        4075989883199081259997430186559003265162660312462485278278299660062152) * 10 ^ 70 +
        1186483430121491200780962946107485886156912162881009097986962607267542) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 223 +
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
  rw [recurrence5Scalar0Exceptional_coeff_311_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_312 :
    recurrence5Scalar0Exceptional.coeff 312 =
      -(((((15817432736291557850370306105345623850037644823254945785632534 * 10 ^ 70 +
        4078830223966639358182635069124934949181942085975640653593514147271552) * 10 ^ 70 +
        0687247787459124299464846931251550593113792291293525625859019308178584) * 10 ^ 70 +
        4993094638995036499605759315257240346838584724420524470363316256597800) * 10 ^ 70 +
        4980828103684687402315407823122966381197211180625508321614527067615522) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 224 +
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
  rw [recurrence5Scalar0Exceptional_coeff_312_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_313 :
    recurrence5Scalar0Exceptional.coeff 313 =
      (((((7712917081703915820834388465966708785328693766584848030167109 * 10 ^ 70 +
        3980596348530257101893949848163723667942996614122442732868495684467157) * 10 ^ 70 +
        5970028462796360358497588250012288208479139775869762079198419207989014) * 10 ^ 70 +
        7239398134429902503160990657011207466399105257509073760381378661601529) * 10 ^ 70 +
        8576382132180630369148572448267325064829591698028701993701017433696878) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 225 +
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
  rw [recurrence5Scalar0Exceptional_coeff_313_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_314 :
    recurrence5Scalar0Exceptional.coeff 314 =
      -(((((3654776562652703976098999439983512130264775974178148615620008 * 10 ^ 70 +
        0637807247923263729492664089281729119752675184629281935878885637298160) * 10 ^ 70 +
        6234014052372585945330779821409402851450104317026910155362857004084898) * 10 ^ 70 +
        8581626174724051161752860908319915095291578578294820622468471972512150) * 10 ^ 70 +
        5321711534284001859442176826723009979827234045683882779234783875125163) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 226 +
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
  rw [recurrence5Scalar0Exceptional_coeff_314_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_315 :
    recurrence5Scalar0Exceptional.coeff 315 =
      (((((1681745302405033943191709878013283534516020149822401673499908 * 10 ^ 70 +
        7625437028591556848759858139504985668399456856887917463772674483714394) * 10 ^ 70 +
        2947782137824340953887949622407795935001805461131227770418899995626979) * 10 ^ 70 +
        8447356713418442524140606535152635519456879795786898473473978444367173) * 10 ^ 70 +
        5008923632000685465135415100634738633737545026302293140682512649954358) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 227 +
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
  rw [recurrence5Scalar0Exceptional_coeff_315_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_316 :
    recurrence5Scalar0Exceptional.coeff 316 =
      -(((((750680549857883327206906369872067053394753716047755595409396 * 10 ^ 70 +
        2173374474249180498136643542953037342726618179687928201107169862664171) * 10 ^ 70 +
        1994898208872983543206060134544693284047935808896693602481642967673710) * 10 ^ 70 +
        8975926904603240422284674606218505432444924773219456198218293142748589) * 10 ^ 70 +
        3332483133290855075736650478191728327909132953457097088858499780621114) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 228 +
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
  rw [recurrence5Scalar0Exceptional_coeff_316_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_317 :
    recurrence5Scalar0Exceptional.coeff 317 =
      (((((324539113501787527603945096520658281415831696072988775226566 * 10 ^ 70 +
        8778824189028080208928016923893831147880938902059452331658989146491617) * 10 ^ 70 +
        4825711959652050097448891369883768295577818553388319167129930979524188) * 10 ^ 70 +
        9387000269812398438132820210685795725830091314408747086842296306293339) * 10 ^ 70 +
        2547988946785137077116854786158529644388801029676728967315895337011866) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 229 +
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
  rw [recurrence5Scalar0Exceptional_coeff_317_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_318 :
    recurrence5Scalar0Exceptional.coeff 318 =
      -(((((135586657479854144047734857095896135207952051737647885335952 * 10 ^ 70 +
        1837461872376133390864581029060340717278925921887408377234986903841741) * 10 ^ 70 +
        1032151652401066036188130158056499010894369026716398201464996984776383) * 10 ^ 70 +
        6210267030132236695120551049000440289231463714613494315118525937009214) * 10 ^ 70 +
        7386107014265770908936355677862521003933522522129342714756214306820450) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 230 +
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
  rw [recurrence5Scalar0Exceptional_coeff_318_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_319 :
    recurrence5Scalar0Exceptional.coeff 319 =
      (((((54562133415976708010974191690478460656243058577995858738979 * 10 ^ 70 +
        8088499418286161287477147009368560524225847525433308850246646977600869) * 10 ^ 70 +
        9792895112818388448799298866872988104184287901475102095268459707706112) * 10 ^ 70 +
        3142504470596380617573693218936315249772192894124333726897230149744446) * 10 ^ 70 +
        6203457957994205316261315137762446732961486154655466452964358324934293) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 231 +
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
  rw [recurrence5Scalar0Exceptional_coeff_319_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_320 :
    recurrence5Scalar0Exceptional.coeff 320 =
      -(((((21047854582011576884204830599461970911571504703064039800446 * 10 ^ 70 +
        9192750649813190853932421678568437342471701410110825847813880532893883) * 10 ^ 70 +
        3638743049477574078120693857828506383278046156222398425918994977533473) * 10 ^ 70 +
        1980092911512121345030486330601495629036190676896992712290860530826169) * 10 ^ 70 +
        7086138835998861011257190582894807359309019979734662169322142056473152) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 232 +
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
  rw [recurrence5Scalar0Exceptional_coeff_320_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_321 :
    recurrence5Scalar0Exceptional.coeff 321 =
      (((((7726322124143510053023181625793540422048468600887814415634 * 10 ^ 70 +
        4747500440460644707076212229350437555529387199772069125615707735595681) * 10 ^ 70 +
        2897605841753580400961450003853906241521561291455190965949456541417156) * 10 ^ 70 +
        2869731657156129919823917715705720651441166674216338417156902599585748) * 10 ^ 70 +
        1145340942699363150011829005541508150995130968841977435820764941397198) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 233 +
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
  rw [recurrence5Scalar0Exceptional_coeff_321_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_322 :
    recurrence5Scalar0Exceptional.coeff 322 =
      -(((((2666601683414083705401385201283953996981870085774309884796 * 10 ^ 70 +
        5216196585050436669226433756524102984579953638421325173955870520965140) * 10 ^ 70 +
        2577442383400529104525955696527277675491688755013533611526236827109043) * 10 ^ 70 +
        6956829794772145204008802113389812984407597152228503524877113535548083) * 10 ^ 70 +
        5479972505328072885291448538449254394524960738777511913378992752287887) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 234 +
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
  rw [recurrence5Scalar0Exceptional_coeff_322_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_323 :
    recurrence5Scalar0Exceptional.coeff 323 =
      (((((846622687239348650989671443183887642627166137635530106051 * 10 ^ 70 +
        1051683824467930970940583384480562629136117032314449174321764151834031) * 10 ^ 70 +
        8111775142420732178121871862882020836961363200332743218590910024322405) * 10 ^ 70 +
        6497671232829657278367167915434910129022906698113138534421784629319251) * 10 ^ 70 +
        6929237767721978010903703703202699007723748097297648574117956780596976) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 235 +
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
  rw [recurrence5Scalar0Exceptional_coeff_323_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_324 :
    recurrence5Scalar0Exceptional.coeff 324 =
      -(((((236003265463297973882594331515357916698005118265971110298 * 10 ^ 70 +
        0011671161321572847213656281445303213865147661221542680095133568913810) * 10 ^ 70 +
        0000926806383691638917049651002267741518562023387980746067914532201129) * 10 ^ 70 +
        8641699728125373269131086236678316410620709602435905771007323446251241) * 10 ^ 70 +
        9562827374879386868385989065571107899230701752125525590530897533250384) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 236 +
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
  rw [recurrence5Scalar0Exceptional_coeff_324_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_325 :
    recurrence5Scalar0Exceptional.coeff 325 =
      (((((50419685678096344297879130393702632818566388524600350682 * 10 ^ 70 +
        4685914447341956834345083084127291435312799851498548644307690453776406) * 10 ^ 70 +
        8589343686137524710635829041304756723813014372946407938025598558652512) * 10 ^ 70 +
        6673959629544932916712770297770156490126757914784124597149066107641560) * 10 ^ 70 +
        0204725039447540590763197747843634432162619898226556517462358953368730) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 237 +
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
  rw [recurrence5Scalar0Exceptional_coeff_325_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_326 :
    recurrence5Scalar0Exceptional.coeff 326 =
      -(((((2747066439999998182314063750687787517089238948446408412 * 10 ^ 70 +
        4710870516419908567256867597558720149659376464014148086195273142224624) * 10 ^ 70 +
        6499083878058408064111307399844626144959461108570938060444234661836642) * 10 ^ 70 +
        7307398806841384753118389645472647058809095690641197381473385917179571) * 10 ^ 70 +
        3771112787119018186692129271132454064546397031795299573297027147823369) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 238 +
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
  rw [recurrence5Scalar0Exceptional_coeff_326_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_327 :
    recurrence5Scalar0Exceptional.coeff 327 =
      -(((((5257791222540839090525844434169109943097859178380198960 * 10 ^ 70 +
        8840083293094225938163626609479618960668227330839252378785624617332645) * 10 ^ 70 +
        7107456327938064196046409227274411530979234212117643477109777832751932) * 10 ^ 70 +
        6663815146761677419055471281337948098234357098907928644069943759461941) * 10 ^ 70 +
        6974388436852402057922691698729027109944734997695805739237370278653244) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 239 +
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
  rw [recurrence5Scalar0Exceptional_coeff_327_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_328 :
    recurrence5Scalar0Exceptional.coeff 328 =
      (((((4207600939650010721166137943377894034463956696803954666 * 10 ^ 70 +
        3165351155148441500575163954742032106226023005116937317465940637806340) * 10 ^ 70 +
        7163559765410214108227191398839274179740263979479698327154167697730847) * 10 ^ 70 +
        8617934319757079251275440115069219571852020960413689404926216570180145) * 10 ^ 70 +
        8330899903750590020679947803642169738118430396922551698002220653217757) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 240 +
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
  rw [recurrence5Scalar0Exceptional_coeff_328_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_329 :
    recurrence5Scalar0Exceptional.coeff 329 =
      -(((((2291312484886300727949346656819812139824920739353260353 * 10 ^ 70 +
        3385174843312891272126628167851175267794735239789433383017031837920280) * 10 ^ 70 +
        3324294352636435746623447671086723802300273625930927226302400684752028) * 10 ^ 70 +
        0036186105591723896277849989565630503769667430526889968649358738347011) * 10 ^ 70 +
        8696945329356206408959006769841468481123053120049706635479344648425876) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 241 +
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
  rw [recurrence5Scalar0Exceptional_coeff_329_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_330 :
    recurrence5Scalar0Exceptional.coeff 330 =
      (((((1053633269861100662312289168378689525430116001173365677 * 10 ^ 70 +
        7241171074143187591136473246368803293100604525042827882310196490047931) * 10 ^ 70 +
        1029545741755281899328749290916421886457108213355404611367875155328845) * 10 ^ 70 +
        7335224534191776922810267232656286000867842610198691240863621052431659) * 10 ^ 70 +
        4561633540297257528834588463143797818200470560335486537968023659992479) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 242 +
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
  rw [recurrence5Scalar0Exceptional_coeff_330_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_331 :
    recurrence5Scalar0Exceptional.coeff 331 =
      -(((((433440892111342343754419234352947064714946700478875277 * 10 ^ 70 +
        9441169383038366124243332741438989161233532514378486315966443425647651) * 10 ^ 70 +
        1704717333904184184504022512955930733297655740427711569617258238248908) * 10 ^ 70 +
        5537383701298630980888748931227631455682434709417994752569747911346176) * 10 ^ 70 +
        2639240522320818392602026635793633767879184024260705226580388414705938) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 243 +
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
  rw [recurrence5Scalar0Exceptional_coeff_331_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_332 :
    recurrence5Scalar0Exceptional.coeff 332 =
      (((((162708593673511922762926200639687423518398199222110655 * 10 ^ 70 +
        4049980401110212915977927910552582190895038015218591670333647195944035) * 10 ^ 70 +
        8142495429915810156521563754307270078420993964032580189306181017209905) * 10 ^ 70 +
        9886120262322629035367010922035585908320659165858292036187481522906399) * 10 ^ 70 +
        8538474747280269702518805219284348413021538627485287798822421969705508) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 244 +
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
  rw [recurrence5Scalar0Exceptional_coeff_332_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_333 :
    recurrence5Scalar0Exceptional.coeff 333 =
      -(((((55900819516718846813199283165808005656198380656340195 * 10 ^ 70 +
        8641112253780348511829354720973442201675164685767235662682165659381898) * 10 ^ 70 +
        1318483993205898649598788112535357858764122803045030123696750939692751) * 10 ^ 70 +
        2201980157112944456952910659279839740474329701755106577170117426593472) * 10 ^ 70 +
        8768563910935421033405963086086104609369302496514915802423766464439399) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 245 +
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
  rw [recurrence5Scalar0Exceptional_coeff_333_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_334 :
    recurrence5Scalar0Exceptional.coeff 334 =
      (((((17381808424787047168766027133976260892244495651668037 * 10 ^ 70 +
        8849501773617063787528638600659328102316904360083197519330030125324561) * 10 ^ 70 +
        9863036471757725328031658548553984767152543772670950937452938733927926) * 10 ^ 70 +
        5751334678323282095344200926081570496068608525156472527085198415460134) * 10 ^ 70 +
        4959409175721016931653683870861430506652916191879497582580004009094341) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 246 +
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
  rw [recurrence5Scalar0Exceptional_coeff_334_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_335 :
    recurrence5Scalar0Exceptional.coeff 335 =
      -(((((4723607119970059416665411408610425831584319944485460 * 10 ^ 70 +
        1743648096478615868572162733566105141565535049495763165563360964315201) * 10 ^ 70 +
        5186906354234721625570193077358411355655730647665220155076173276885751) * 10 ^ 70 +
        2387382072267664729022090585073701504929992983084810787825172123723827) * 10 ^ 70 +
        4441838260422485590651843088570961239942428404705445475921697358708938) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 247 +
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
  rw [recurrence5Scalar0Exceptional_coeff_335_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_336 :
    recurrence5Scalar0Exceptional.coeff 336 =
      (((((1008625452996816710256352021388569452559022697004204 * 10 ^ 70 +
        7417217074556125535847912107432104808864330744365023867275864912418728) * 10 ^ 70 +
        3283019310917930971496265258757014633146049494313221445689004143999563) * 10 ^ 70 +
        8562892228535906904848041477799136680991889096418918531247458582599719) * 10 ^ 70 +
        9750944621021646470519487070909537440256622239608899446615355431178776) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 248 +
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
  rw [recurrence5Scalar0Exceptional_coeff_336_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_337 :
    recurrence5Scalar0Exceptional.coeff 337 =
      -(((((89559642193133773083295626153164857165461018737163 * 10 ^ 70 +
        1728837989519725224895308244110614257957490559847349543887955150193202) * 10 ^ 70 +
        3365286188179069683271370114782105740197181751907098152980117076699207) * 10 ^ 70 +
        9826371371509741339666192706474962190142604959611727745978197945396178) * 10 ^ 70 +
        1952234210331675711379636417116863419151515178312520367700323887368287) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 249 +
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
  rw [recurrence5Scalar0Exceptional_coeff_337_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_338 :
    recurrence5Scalar0Exceptional.coeff 338 =
      -(((((65251682967914524085371561373188515806221714650081 * 10 ^ 70 +
        9648547974339788636223487776971368966594928561788297070441239258621886) * 10 ^ 70 +
        4166624865158228090961723671133534566220408741275434543623476575054373) * 10 ^ 70 +
        5428395497147636172814755640602383529548604914167878369339788122063783) * 10 ^ 70 +
        8316479361027504228676599084850991218481538024931964719782302419477806) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 250 +
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
  rw [recurrence5Scalar0Exceptional_coeff_338_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_339 :
    recurrence5Scalar0Exceptional.coeff 339 =
      (((((55035479176481824197680201306821440472307537942000 * 10 ^ 70 +
        2605647627511603481696899374989190320689457073067505047865876149508544) * 10 ^ 70 +
        0775721879193847904036831151104664056448453979358701152297210038866521) * 10 ^ 70 +
        7527944501924388767373936432054698440716351280317241890489529118979116) * 10 ^ 70 +
        0261566628664459875553556472500906318918396978961172027523821690461040) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 251 +
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
  rw [recurrence5Scalar0Exceptional_coeff_339_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_340 :
    recurrence5Scalar0Exceptional.coeff 340 =
      -(((((29002147947758642213612956414151589841684951023111 * 10 ^ 70 +
        5258751861408631932490852462882515515164360713261894727804961778757112) * 10 ^ 70 +
        9423583309030528569656950716815187686582520531037262040766288206738356) * 10 ^ 70 +
        8713622133172503533080156535133704729666854878384159507605695369711923) * 10 ^ 70 +
        5678224339378571548301044630625654438414596333483066090662745542906562) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 252 +
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
  rw [recurrence5Scalar0Exceptional_coeff_340_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_341 :
    recurrence5Scalar0Exceptional.coeff 341 =
      (((((12774012295603323444425643566115996107288216169393 * 10 ^ 70 +
        2151088543878326580021044269421898803327952645802848210829868844086000) * 10 ^ 70 +
        8082884563707668615797222134556571532064985437791039374389759446882643) * 10 ^ 70 +
        9911583165104746821359415178206200569025407136111007683621286186437012) * 10 ^ 70 +
        5323106215507298664946597956635946464541557814539491944703768197579912) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 253 +
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
  rw [recurrence5Scalar0Exceptional_coeff_341_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_342 :
    recurrence5Scalar0Exceptional.coeff 342 =
      -(((((5063569260817300277435314368566006146125208848686 * 10 ^ 70 +
        5419069859902879688015698549541056029061265847397034333799323228889359) * 10 ^ 70 +
        5612436354241187336660873851832423034482463096916674250689615721744126) * 10 ^ 70 +
        6394771706433597555974791195680632428464336515262325132843022988495309) * 10 ^ 70 +
        9260334819533940268642086518581409659942331022781114396007213001517553) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 254 +
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
  rw [recurrence5Scalar0Exceptional_coeff_342_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_343 :
    recurrence5Scalar0Exceptional.coeff 343 =
      (((((1860600738519427965115696059908107669335999198315 * 10 ^ 70 +
        6596934125668360852964439487818408563305291056534185938820301524289003) * 10 ^ 70 +
        8525996082627763913950862523641456700241969287968250844726046819215676) * 10 ^ 70 +
        9643354130763586409750402417807621014852792390923660253307439958660639) * 10 ^ 70 +
        9117577189620815843048074239226907730645413349733257411065764530812369) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 255 +
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
  rw [recurrence5Scalar0Exceptional_coeff_343_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_344 :
    recurrence5Scalar0Exceptional.coeff 344 =
      -(((((642096390938862448510795983394480983444136232008 * 10 ^ 70 +
        3297233644950357083563029188052708482686303967866689606757545790485368) * 10 ^ 70 +
        8597760674122472546494235985932009087424214108208535940526829195935741) * 10 ^ 70 +
        1669268205241753714021691152532232189635958386365867841374437623447932) * 10 ^ 70 +
        5042066132409290688440716773039945630730457829403686674277973325150895) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 256 +
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
  rw [recurrence5Scalar0Exceptional_coeff_344_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_345 :
    recurrence5Scalar0Exceptional.coeff 345 =
      (((((208861938808014664846618004280586552698238668410 * 10 ^ 70 +
        4068965427007496849104616463812078135710500220301193119844814677400965) * 10 ^ 70 +
        9088859993926516957838788529130727878604292820355307039947916441224428) * 10 ^ 70 +
        1939220637764347515402140358868839954394083418361057202658682521614645) * 10 ^ 70 +
        7486863576788984685139671735320468195399272376688646386523832359020466) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 257 +
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
  rw [recurrence5Scalar0Exceptional_coeff_345_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_346 :
    recurrence5Scalar0Exceptional.coeff 346 =
      -(((((63692719109363950480920720904738826916493374887 * 10 ^ 70 +
        3051488601156912611122379433733907459897187052590935883730106777752935) * 10 ^ 70 +
        6786618744617734725378032552226299328480152588428285217476192165972136) * 10 ^ 70 +
        3448947261287312166706250538262652270732358026032743181573025294301132) * 10 ^ 70 +
        9076268703620895990399771500260542505349560428035570473352919495889854) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 258 +
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
  rw [recurrence5Scalar0Exceptional_coeff_346_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_347 :
    recurrence5Scalar0Exceptional.coeff 347 =
      (((((17865354980729119336343271776243638521048802271 * 10 ^ 70 +
        4662625892180522395063121082846531769365253296469570438691662901548118) * 10 ^ 70 +
        1950324934660229185744502418242092693125585569826555092393287911269623) * 10 ^ 70 +
        7624902141341438833948777276408685736508195878540404572712485140773620) * 10 ^ 70 +
        8285599640557357823381835087500772754473230944206169349982636239381953) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 259 +
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
  rw [recurrence5Scalar0Exceptional_coeff_347_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_348 :
    recurrence5Scalar0Exceptional.coeff 348 =
      -(((((4383263500393211992565853612954283929070813713 * 10 ^ 70 +
        9424782541748996906048638030692726294899613645538847460408704249146473) * 10 ^ 70 +
        0871916476152364712590076026499974214916893524164199498735459938300336) * 10 ^ 70 +
        0300231923960606509014749333578257641500487675821063162550732492651173) * 10 ^ 70 +
        7149375537585993008356064417670190429763736483505726723479817697611974) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 260 +
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
  rw [recurrence5Scalar0Exceptional_coeff_348_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_349 :
    recurrence5Scalar0Exceptional.coeff 349 =
      (((((797053299766139099346288203769713459144599455 * 10 ^ 70 +
        6090145655689067351480170997768183007578297066055130897049562508113983) * 10 ^ 70 +
        6431720627254133064595632332348195361727426049825267328570525370741924) * 10 ^ 70 +
        3974070746742490793848477750369289565172598351124028809395240006107573) * 10 ^ 70 +
        0237571708239250889215422226610118957008680738544263479932034065904934) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 261 +
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
  rw [recurrence5Scalar0Exceptional_coeff_349_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_350 :
    recurrence5Scalar0Exceptional.coeff 350 =
      -(((((4201634400321408944451603950553309736771346 * 10 ^ 70 +
        0719750106495410271037773199482631864561393283405025552946085579952301) * 10 ^ 70 +
        1109196581005503164551278488792443942990628323355910791466990824585630) * 10 ^ 70 +
        1335731421265945996746759016269590526695362478146254472453515808199350) * 10 ^ 70 +
        4777270987454789717404325581847481756542675863428724640314753726257531) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 262 +
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
  rw [recurrence5Scalar0Exceptional_coeff_350_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_351 :
    recurrence5Scalar0Exceptional.coeff 351 =
      -(((((95379688430304620326908602977069052505101876 * 10 ^ 70 +
        5555103290758720223905471512622289665141259465869198005297537215242137) * 10 ^ 70 +
        3005288652516389734321157200486766412505793964295706899545515016982779) * 10 ^ 70 +
        0568465096362248659679562215773571175998138189950354858327586423564632) * 10 ^ 70 +
        8080347275009504953278273528800900957120172745033412165257177789690236) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 263 +
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
  rw [recurrence5Scalar0Exceptional_coeff_351_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_352 :
    recurrence5Scalar0Exceptional.coeff 352 =
      (((((65381653205322653450602271643130929563547520 * 10 ^ 70 +
        4463935005585376002303021315888824998228460575565812791740866981672564) * 10 ^ 70 +
        4037852669776227978087589365431506694510394845469900034219126716040796) * 10 ^ 70 +
        0774038884481593290402394664298969773072213398996668733407098975401021) * 10 ^ 70 +
        7641221297117096365777483939908082632180532490496138204397035408543334) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 264 +
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
  rw [recurrence5Scalar0Exceptional_coeff_352_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_353 :
    recurrence5Scalar0Exceptional.coeff 353 =
      -(((((32606386177886934842437961116508112844295730 * 10 ^ 70 +
        0231533944060761435334507738526919208945709997673918798475417223566335) * 10 ^ 70 +
        4198760422524541669988333561064095917753733660090818217926579629146703) * 10 ^ 70 +
        4265735233866281089815278278381769445700091406237566205022868131089893) * 10 ^ 70 +
        4171527190515817089195225868619857758174850018593679500431605334873361) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 265 +
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
  rw [recurrence5Scalar0Exceptional_coeff_353_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_354 :
    recurrence5Scalar0Exceptional.coeff 354 =
      (((((14022394768169069107385869225036453572107249 * 10 ^ 70 +
        9301684146889411159744896391256444510074608304611199879580327025559663) * 10 ^ 70 +
        4819415436021977228919490704339901310187425828219243118092647408708778) * 10 ^ 70 +
        4813652423991094029595986235399347892049711015101714170621817354717386) * 10 ^ 70 +
        0948408984348113051541396311205571095066431304844524142214911906382746) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 266 +
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
  rw [recurrence5Scalar0Exceptional_coeff_354_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_355 :
    recurrence5Scalar0Exceptional.coeff 355 =
      -(((((5463664266547542739049268512751724497510170 * 10 ^ 70 +
        9547237394064220852139689617604632408745320563786470637308289719686776) * 10 ^ 70 +
        2371953719021611279938411750018343674727894975508517814320700443895891) * 10 ^ 70 +
        5979548053860607930701303710751007010775083550835696358623873352533092) * 10 ^ 70 +
        3695703584968132260575551727650329859367713640337434031633852282778397) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 267 +
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
  rw [recurrence5Scalar0Exceptional_coeff_355_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_356 :
    recurrence5Scalar0Exceptional.coeff 356 =
      (((((1963853466239695736447519615276673527520707 * 10 ^ 70 +
        7123857850303783729613845374003184173918824195947153695497550224397428) * 10 ^ 70 +
        8473931890896579627313543590350691676072401686840529306729067343803590) * 10 ^ 70 +
        4184267366238331882352123431095455989509294344766572105268042968111869) * 10 ^ 70 +
        7151321226955832898052795847274925788112929512106039803286706238834176) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 268 +
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
  rw [recurrence5Scalar0Exceptional_coeff_356_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_357 :
    recurrence5Scalar0Exceptional.coeff 357 =
      -(((((653971634208236508422508507482731349223005 * 10 ^ 70 +
        9462576974595850565416683807578660067094770978369801599709749544144014) * 10 ^ 70 +
        4009132329280724037102087229997374483529250835217387430284137907510223) * 10 ^ 70 +
        6839084304256968131371640873699628632545820520866966940315142825531272) * 10 ^ 70 +
        5337450570723488743361211900770319751550108799911535378728545043698514) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 269 +
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
  rw [recurrence5Scalar0Exceptional_coeff_357_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_358 :
    recurrence5Scalar0Exceptional.coeff 358 =
      (((((200603519916932424337079802430646815605006 * 10 ^ 70 +
        2150453700678051852972275826468032403918620155687882916821309660211010) * 10 ^ 70 +
        6372831484237862204895765521459018788502624972647195369685937593848593) * 10 ^ 70 +
        0934787980964951773367111967933540501921412459160999624843399541442449) * 10 ^ 70 +
        5599369989371081414006281454520920865838190129180734190635852269779939) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 270 +
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
  rw [recurrence5Scalar0Exceptional_coeff_358_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_359 :
    recurrence5Scalar0Exceptional.coeff 359 =
      -(((((55611451859368627370791150994710356789099 * 10 ^ 70 +
        1013167271010743486190444871182089347972008492659616956664819296903723) * 10 ^ 70 +
        6228752667118953882474266985360532739729827424553030808783281131842723) * 10 ^ 70 +
        6380300746922897611893057887930909851125861619738528662100244548602522) * 10 ^ 70 +
        2787616516886421832562766722309604396757801457334166373809759090317707) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 271 +
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
  rw [recurrence5Scalar0Exceptional_coeff_359_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_360 :
    recurrence5Scalar0Exceptional.coeff 360 =
      (((((13269212390137662647129610774040432331272 * 10 ^ 70 +
        4079156245765851015502873874971423426917032651910897544201607297647207) * 10 ^ 70 +
        0731141687177513374414492813273870358670199811722724832337169311873170) * 10 ^ 70 +
        7209743163873237970606437274581418801978878633993459135330600832006889) * 10 ^ 70 +
        8594331261879659473786790619657959815179427464008547478789968949464851) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 272 +
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
  rw [recurrence5Scalar0Exceptional_coeff_360_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_361 :
    recurrence5Scalar0Exceptional.coeff 361 =
      -(((((2325141261842626191789332210481143943264 * 10 ^ 70 +
        2970544947113445245456878968718740596331819150961395131228477334600094) * 10 ^ 70 +
        8907589780040692554292535835500722007755100697382175315515385516817963) * 10 ^ 70 +
        5935778336705626103082949249733043924326615807765278902117806927844952) * 10 ^ 70 +
        0150975927391128972862031335227593715463577256691357138722966278126257) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 273 +
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
  rw [recurrence5Scalar0Exceptional_coeff_361_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_362 :
    recurrence5Scalar0Exceptional.coeff 362 =
      (((((29435116235383485643576584559783213294 * 10 ^ 70 +
        7480776512814967545508399224625389051902536798126603268977840176676870) * 10 ^ 70 +
        1330007441146709897478473792138285457366735466434922782122700889416959) * 10 ^ 70 +
        7746132473737738903383706792360804075945435243784803377801818970745948) * 10 ^ 70 +
        9925481255381758636873272411761322039834673649251300624743488566954579) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 274 +
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
  rw [recurrence5Scalar0Exceptional_coeff_362_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_363 :
    recurrence5Scalar0Exceptional.coeff 363 =
      (((((230544999427900837796670210252842949650 * 10 ^ 70 +
        6510194054173244544195726608438597311097906231808213280916107522508892) * 10 ^ 70 +
        2240278030685340083834649045398278564625377562465780803773952289871291) * 10 ^ 70 +
        0829021351837148945011073227759166444735806887455053980606013380951921) * 10 ^ 70 +
        1769007776238892933281273146559230113731406367734479485146590531934602) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 275 +
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
  rw [recurrence5Scalar0Exceptional_coeff_363_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_364 :
    recurrence5Scalar0Exceptional.coeff 364 =
      -(((((147204207766264857430637660396011262893 * 10 ^ 70 +
        4842428774714491092265181919234577503958828057588365235921665210308837) * 10 ^ 70 +
        5638665970856630125347058674458673450704251059062161173169830461236771) * 10 ^ 70 +
        6013192755949987592494473890028027803235429717819915686158539268203382) * 10 ^ 70 +
        3761562400281370068964097290236851482156735967474582456198448460221711) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 276 +
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
  rw [recurrence5Scalar0Exceptional_coeff_364_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_365 :
    recurrence5Scalar0Exceptional.coeff 365 =
      (((((67523499025016574210911733795238724341 * 10 ^ 70 +
        9408467215869091669208882652678813175368975268186011133807915528153578) * 10 ^ 70 +
        1837254260791131239261844414021133773506787573855067873407613048706273) * 10 ^ 70 +
        1378824269501147413773725250523992799372471500733344198776440952029477) * 10 ^ 70 +
        5152740517540266316088366582697313122126720824781861102998145719186866) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 277 +
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
  rw [recurrence5Scalar0Exceptional_coeff_365_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_366 :
    recurrence5Scalar0Exceptional.coeff 366 =
      -(((((26672762425658689260559784422586516222 * 10 ^ 70 +
        5838853247578691995809566803740801997538090187734957552625336535870218) * 10 ^ 70 +
        9660677329524746494175057441508113186578559833832439951366270434610495) * 10 ^ 70 +
        0360647563274143929858719462463039796173388230134198416558933011609503) * 10 ^ 70 +
        7555248534707541115642156024099955215305495752808048208495299407123949) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 278 +
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
  rw [recurrence5Scalar0Exceptional_coeff_366_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_367 :
    recurrence5Scalar0Exceptional.coeff 367 =
      (((((9595170259841593304962793195665539570 * 10 ^ 70 +
        1306411296491244387257025975527972623785901419909929844298064504571656) * 10 ^ 70 +
        9904583984925863069513573819598686411031345251043409390175613306115433) * 10 ^ 70 +
        0226924864501653685034481564717392511466156174769371924797812818885576) * 10 ^ 70 +
        4181642385252948038202381764015237304787426763523387047354309655161957) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 279 +
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
  rw [recurrence5Scalar0Exceptional_coeff_367_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_368 :
    recurrence5Scalar0Exceptional.coeff 368 =
      -(((((3220026989510210781337270039812384757 * 10 ^ 70 +
        7739772329814458321795932713812463436940394537948732089608418012195669) * 10 ^ 70 +
        7159428490507344993199400629314942866467615643972423651446178621103738) * 10 ^ 70 +
        9118530382179672360081354135580795005209340979763931353159834863193376) * 10 ^ 70 +
        8282682667543111683670776114567293004749518705990324440323790809967395) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 280 +
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
  rw [recurrence5Scalar0Exceptional_coeff_368_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_369 :
    recurrence5Scalar0Exceptional.coeff 369 =
      (((((1018736858636595180858051455269715758 * 10 ^ 70 +
        8598487109093052213000453506306374889459445646248247340909168861185327) * 10 ^ 70 +
        0813195536673366965270923690465274494539243376292691423030301984236351) * 10 ^ 70 +
        5050320434871848499733267571636258589394933527419961283031046584821142) * 10 ^ 70 +
        4618789061412235334885924753883657347638991595579926622266994261297142) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 281 +
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
  rw [recurrence5Scalar0Exceptional_coeff_369_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_370 :
    recurrence5Scalar0Exceptional.coeff 370 =
      -(((((304261830944006150323033164881006578 * 10 ^ 70 +
        3026271810163068497407730783068095471087687854356117036942215215847135) * 10 ^ 70 +
        4765565775726013195356858542850611513720869701863760254129971778253492) * 10 ^ 70 +
        1394720168293790839030803654539682217284366504525575554314226589240651) * 10 ^ 70 +
        0511765761107076672920932849206071436554477983684755141045614952775346) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 282 +
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
  rw [recurrence5Scalar0Exceptional_coeff_370_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_371 :
    recurrence5Scalar0Exceptional.coeff 371 =
      (((((85032183177046526251924220752063365 * 10 ^ 70 +
        2035059336269639827191851999285495794380501564051095609505968071260683) * 10 ^ 70 +
        1751002016200294600304979276163442850344593597377979509199761262682734) * 10 ^ 70 +
        7259925812252699883713382692496323559215383149649727673541654526327939) * 10 ^ 70 +
        4722395280872996265092503706730607199396018283528396512573437218096929) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 283 +
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
  rw [recurrence5Scalar0Exceptional_coeff_371_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_372 :
    recurrence5Scalar0Exceptional.coeff 372 =
      -(((((21662477599760598223180497525966910 * 10 ^ 70 +
        3609707277979837562585004566092391006931471335930570329423754253230957) * 10 ^ 70 +
        2039886252527123147591498085253916722227582291743713436809306065025017) * 10 ^ 70 +
        0450046985030109049081728449551533546425179916699646624545358953368315) * 10 ^ 70 +
        1054542899024917252985884471339856550617925627162054289203984359347774) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 284 +
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
  rw [recurrence5Scalar0Exceptional_coeff_372_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_373 :
    recurrence5Scalar0Exceptional.coeff 373 =
      (((((4687747999504633125682281632226211 * 10 ^ 70 +
        6840672591405040769798541584720656844465472317122469474981939330432838) * 10 ^ 70 +
        6749745446005726795252679483925529532719499223014402189420627522685604) * 10 ^ 70 +
        6677032040412663459879506827556174235108803145834181086188235565676224) * 10 ^ 70 +
        8246146257167614795942084530227195684444034348922240319756195813795889) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 285 +
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
  rw [recurrence5Scalar0Exceptional_coeff_373_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_374 :
    recurrence5Scalar0Exceptional.coeff 374 =
      -(((((652315460367372049590862177992190 * 10 ^ 70 +
        8251256325873004243161420080673400592814307370948551549274794758000061) * 10 ^ 70 +
        2895818527708670031968424719566622317403579864925412382167265631702458) * 10 ^ 70 +
        2111029224472498663514853045961274141652576713708595198795956484383300) * 10 ^ 70 +
        2973332251550589884557034628898358706740567358481385504194459093035235) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 286 +
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
  rw [recurrence5Scalar0Exceptional_coeff_374_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_375 :
    recurrence5Scalar0Exceptional.coeff 375 =
      -(((((93802550869644877153174871730824 * 10 ^ 70 +
        4411677630706956525034044976204030125773172098803800047703330009000139) * 10 ^ 70 +
        6857979310909813792709569736580943970450366797933336277838939517227393) * 10 ^ 70 +
        1293288778177337034869654287249504307714982396890358888412259207747134) * 10 ^ 70 +
        7878159973653456354697076761417044096001030326318014697657436135766656) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 287 +
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
  rw [recurrence5Scalar0Exceptional_coeff_375_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_376 :
    recurrence5Scalar0Exceptional.coeff 376 =
      (((((132069877565798136906606980398866 * 10 ^ 70 +
        9426967394931623540695851186621321219817073233469202768587482571603755) * 10 ^ 70 +
        7400550309337486638545196042941421813925529090109357368728163872327006) * 10 ^ 70 +
        8655957457994951356058344603073582829646014894199105880248897646417720) * 10 ^ 70 +
        4536445133466809736369600416716640271673455416987901425115998121127238) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 288 +
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
  rw [recurrence5Scalar0Exceptional_coeff_376_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_377 :
    recurrence5Scalar0Exceptional.coeff 377 =
      -(((((74590397132807205247050435219055 * 10 ^ 70 +
        9473593636318913509291794030090039871943502581723403982870745103478250) * 10 ^ 70 +
        9492658478452233602224985885151397081041022543157886319159864277148603) * 10 ^ 70 +
        8288921608773664284655506905773544950482107312857247587290697839219720) * 10 ^ 70 +
        5591269381258091288938224616315264181064598469031769643277702970727692) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 289 +
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
  rw [recurrence5Scalar0Exceptional_coeff_377_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_378 :
    recurrence5Scalar0Exceptional.coeff 378 =
      (((((33348297839078275692822459238432 * 10 ^ 70 +
        7963734300042268940361470680813574117466761654083157050757215922699607) * 10 ^ 70 +
        7334003599511597363752718197613331441761337162251465734858418429673310) * 10 ^ 70 +
        8074253279035798517551617369639673685880803957895222342269902061026846) * 10 ^ 70 +
        9379709858183660041460662676329827804722714380001923656830286089781059) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 290 +
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
  rw [recurrence5Scalar0Exceptional_coeff_378_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (379 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_379 :
    recurrence5Scalar0Exceptional.coeff 379 =
      -(((((13169158377498703682131436313743 * 10 ^ 70 +
        5268638314800270182545513984117022842091393761898873811001238250836051) * 10 ^ 70 +
        3998447139785200949032076201345112013259126792701897173178562950781686) * 10 ^ 70 +
        7019492699706551114132301935361717090321089225751072176650649119544098) * 10 ^ 70 +
        2184529165340450118044688077569202702958953996901332772290713753158430) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 291 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (380 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_380 :
    recurrence5Scalar0Exceptional.coeff 380 =
      (((((4764600176481747876416243417584 * 10 ^ 70 +
        1563138393846190167270557638859209016542224693253883396213720451021661) * 10 ^ 70 +
        0395041327176849005860435057920340989603982472324531418399219247621617) * 10 ^ 70 +
        8715583865637690970278808126464400125843337500230420290769834236536448) * 10 ^ 70 +
        2592776281488552345101098290574915501643381442600667890305229611941720) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 292 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 23 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (381 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_381 :
    recurrence5Scalar0Exceptional.coeff 381 =
      -(((((1602142210554909815100350092927 * 10 ^ 70 +
        7110935810627654301050848411290031637997986441482418508618102767086017) * 10 ^ 70 +
        9243149839996026080441365336555548114528822952644210332313555634435834) * 10 ^ 70 +
        7444887663560322321432064256322213424953838542173393680508778181343368) * 10 ^ 70 +
        3483753536793608377373524085129006184600607487718014385936160421191486) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 293 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 22 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (382 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_382 :
    recurrence5Scalar0Exceptional.coeff 382 =
      (((((502884225920038284793405117175 * 10 ^ 70 +
        3292503288746644354325846643376635628861751326018644620825144558159438) * 10 ^ 70 +
        6448929860915360983838406807285391225255913785315554056825680147370323) * 10 ^ 70 +
        3246738488688475202856888920291396711724241680382510600072865844456824) * 10 ^ 70 +
        6746436635183340426435570373624519187796104085886265003886109566965004) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 294 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 21 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (383 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_383 :
    recurrence5Scalar0Exceptional.coeff 383 =
      -(((((147043811698067326139349782062 * 10 ^ 70 +
        3810514685936280727180163384328640194813481650065273276491121452741488) * 10 ^ 70 +
        4333333274512990429961686033433632378284405701559515772345690410269534) * 10 ^ 70 +
        2968645395834178724968168643851311726645935172464437294653331231787936) * 10 ^ 70 +
        7926392626452305793785438882881926162856094362519798611025030963695787) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 295 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 20 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (384 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_384 :
    recurrence5Scalar0Exceptional.coeff 384 =
      (((((39722614000488723137422403879 * 10 ^ 70 +
        5297124402268475247691473398164674000665490199231414048706503079313491) * 10 ^ 70 +
        6497456406216679333988598604221279261691675890868447432019862833157282) * 10 ^ 70 +
        6550091027626338471294211525504580919675127453978032476504101974127388) * 10 ^ 70 +
        4957474331219357837566701695825256529069979709263547653972019133111579) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 296 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 19 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (385 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_385 :
    recurrence5Scalar0Exceptional.coeff 385 =
      -(((((9738031536481593487408595886 * 10 ^ 70 +
        6083397042099186172668776949472583633206594271743481782871636606323878) * 10 ^ 70 +
        7823337506676822451195343064321186361338416660324656056216481422415346) * 10 ^ 70 +
        1920918160029127062764352838055018856285252804774303366526364487406606) * 10 ^ 70 +
        0397486022143183512920517588493357529197919030909892574527708444579068) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 297 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 18 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (386 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_386 :
    recurrence5Scalar0Exceptional.coeff 386 =
      (((((2083218240720392110161925835 * 10 ^ 70 +
        2933339635912842845392562804748027197430798025348871428427525349718205) * 10 ^ 70 +
        5267464570526660716056861808898410890498402278679511393711293904197382) * 10 ^ 70 +
        4819235717700674068208136120760940362348716250710741188339804899635125) * 10 ^ 70 +
        4411790115293222696206023959979331282233186356170598474136189079145823) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 298 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 17 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (387 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_387 :
    recurrence5Scalar0Exceptional.coeff 387 =
      -(((((349005891280190077831267613 * 10 ^ 70 +
        8039912816329514569519998977286796270134486233688233282998729722094707) * 10 ^ 70 +
        8540059501024221521212427739558584292206471558105448011242182607188593) * 10 ^ 70 +
        9167905149851523328269808885565011187167640911880187425254273933477670) * 10 ^ 70 +
        8257268253399712533956151127531070373482260706909225288230070484068847) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 299 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 16 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (388 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_388 :
    recurrence5Scalar0Exceptional.coeff 388 =
      (((((24719094239362693484655835 * 10 ^ 70 +
        8130215491967299731276148547873019296733005252533128354506939097111398) * 10 ^ 70 +
        5345707335855240948837928864337056429191930667686777759250527657797606) * 10 ^ 70 +
        0351666527598995913949077151692964398194275244336062796619521470759104) * 10 ^ 70 +
        0267439424127186576723507234649634584945017147929196647939042769339899) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 300 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 15 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (389 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_389 :
    recurrence5Scalar0Exceptional.coeff 389 =
      (((((13009571709633189562178538 * 10 ^ 70 +
        2882067338403296393535389135414591210716609021100904424616028202878120) * 10 ^ 70 +
        2018347293071131324651326161180145734811871543238780884835077933266481) * 10 ^ 70 +
        7560410506230401757451192639146734854671052672470722258792425537062413) * 10 ^ 70 +
        0686348558889324163263700296925520003225722488258123249810886823339682) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 301 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 14 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (390 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_390 :
    recurrence5Scalar0Exceptional.coeff 390 =
      -(((((8387202528664712999057215 * 10 ^ 70 +
        9341252891276837356134616612672614219191482509329040694061949200223906) * 10 ^ 70 +
        0497606554620433819813851542577272771520918453808928590680154833222625) * 10 ^ 70 +
        5885577883673488870588559860444833150701387581244140082939999801561064) * 10 ^ 70 +
        2376361722103181069336585556720345514619391623502569769812303968605315) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 302 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 13 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (391 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_391 :
    recurrence5Scalar0Exceptional.coeff 391 =
      (((((3295945726678888733323231 * 10 ^ 70 +
        8858598057159331958152429997519349360114425156294340751709472818540361) * 10 ^ 70 +
        5228591099280028991104288363257134890788490208435390470077722623567501) * 10 ^ 70 +
        2158823854540521586616494063076345916660369017930859421679481936858556) * 10 ^ 70 +
        7403140628401945779833982459436478509212668265952740251402356611007462) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 303 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 12 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (392 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_392 :
    recurrence5Scalar0Exceptional.coeff 392 =
      -(((((1061168075422358459703778 * 10 ^ 70 +
        4218763869607527299928823954158561585002048628700376071590013839926162) * 10 ^ 70 +
        8693782527817322045455265509238114704533079165506783152647300000507008) * 10 ^ 70 +
        8071780222235051045518236893800092573338705844286190541150337215894630) * 10 ^ 70 +
        8869380715481310974197855246423514269372705374439232949044342440275558) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 304 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 11 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Exceptional_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient0.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C0_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Exceptional_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient0.coeff (393 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Exceptional_coeff_393 :
    recurrence5Scalar0Exceptional.coeff 393 =
      (((((301010381383318213134657 * 10 ^ 70 +
        8814673231089049479094781391446383021458184833787119902436878634254770) * 10 ^ 70 +
        8672243180861193602700325147916794115819028780848825418595999119677665) * 10 ^ 70 +
        9038246821782433914351374880741484164137533014810113702468408344511808) * 10 ^ 70 +
        1632783777245059125958053777550390738184606358481760902133413485366457) : ℚ) := by
  unfold recurrence5Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 305 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 10 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Exceptional_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Exceptional_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
