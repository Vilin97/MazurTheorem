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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
