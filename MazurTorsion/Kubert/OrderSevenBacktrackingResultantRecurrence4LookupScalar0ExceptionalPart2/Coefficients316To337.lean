/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0ExceptionalPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C0_coeff_1
  recurrence4C0_coeff_10
  recurrence4C0_coeff_100
  recurrence4C0_coeff_101
  recurrence4C0_coeff_102
  recurrence4C0_coeff_103
  recurrence4C0_coeff_104
  recurrence4C0_coeff_105
  recurrence4C0_coeff_106
  recurrence4C0_coeff_107
  recurrence4C0_coeff_108
  recurrence4C0_coeff_109
  recurrence4C0_coeff_11
  recurrence4C0_coeff_110
  recurrence4C0_coeff_111
  recurrence4C0_coeff_112
  recurrence4C0_coeff_113
  recurrence4C0_coeff_114
  recurrence4C0_coeff_115
  recurrence4C0_coeff_116
  recurrence4C0_coeff_117
  recurrence4C0_coeff_118
  recurrence4C0_coeff_119
  recurrence4C0_coeff_12
  recurrence4C0_coeff_120
  recurrence4C0_coeff_121
  recurrence4C0_coeff_122
  recurrence4C0_coeff_123
  recurrence4C0_coeff_124
  recurrence4C0_coeff_125
  recurrence4C0_coeff_126
  recurrence4C0_coeff_127
  recurrence4C0_coeff_128
  recurrence4C0_coeff_129
  recurrence4C0_coeff_13
  recurrence4C0_coeff_130
  recurrence4C0_coeff_131
  recurrence4C0_coeff_132
  recurrence4C0_coeff_133
  recurrence4C0_coeff_134
  recurrence4C0_coeff_135
  recurrence4C0_coeff_136
  recurrence4C0_coeff_137
  recurrence4C0_coeff_138
  recurrence4C0_coeff_139
  recurrence4C0_coeff_14
  recurrence4C0_coeff_140
  recurrence4C0_coeff_141
  recurrence4C0_coeff_142
  recurrence4C0_coeff_143
  recurrence4C0_coeff_144
  recurrence4C0_coeff_145
  recurrence4C0_coeff_146
  recurrence4C0_coeff_147
  recurrence4C0_coeff_148
  recurrence4C0_coeff_149
  recurrence4C0_coeff_15
  recurrence4C0_coeff_150
  recurrence4C0_coeff_151
  recurrence4C0_coeff_152
  recurrence4C0_coeff_153
  recurrence4C0_coeff_16
  recurrence4C0_coeff_17
  recurrence4C0_coeff_18

attribute [local simp]
  recurrence4C0_coeff_19
  recurrence4C0_coeff_2
  recurrence4C0_coeff_20
  recurrence4C0_coeff_21
  recurrence4C0_coeff_22
  recurrence4C0_coeff_23
  recurrence4C0_coeff_24
  recurrence4C0_coeff_25
  recurrence4C0_coeff_26
  recurrence4C0_coeff_27
  recurrence4C0_coeff_28
  recurrence4C0_coeff_29
  recurrence4C0_coeff_3
  recurrence4C0_coeff_30
  recurrence4C0_coeff_31
  recurrence4C0_coeff_32
  recurrence4C0_coeff_33
  recurrence4C0_coeff_34
  recurrence4C0_coeff_35
  recurrence4C0_coeff_36
  recurrence4C0_coeff_37
  recurrence4C0_coeff_38
  recurrence4C0_coeff_39
  recurrence4C0_coeff_4
  recurrence4C0_coeff_40
  recurrence4C0_coeff_41
  recurrence4C0_coeff_42
  recurrence4C0_coeff_43
  recurrence4C0_coeff_44
  recurrence4C0_coeff_45
  recurrence4C0_coeff_46
  recurrence4C0_coeff_47
  recurrence4C0_coeff_48
  recurrence4C0_coeff_49
  recurrence4C0_coeff_5
  recurrence4C0_coeff_50
  recurrence4C0_coeff_51
  recurrence4C0_coeff_52
  recurrence4C0_coeff_53
  recurrence4C0_coeff_54
  recurrence4C0_coeff_55
  recurrence4C0_coeff_56
  recurrence4C0_coeff_57
  recurrence4C0_coeff_58
  recurrence4C0_coeff_59
  recurrence4C0_coeff_6
  recurrence4C0_coeff_60
  recurrence4C0_coeff_61
  recurrence4C0_coeff_62
  recurrence4C0_coeff_63
  recurrence4C0_coeff_64
  recurrence4C0_coeff_65
  recurrence4C0_coeff_66
  recurrence4C0_coeff_67
  recurrence4C0_coeff_68
  recurrence4C0_coeff_69
  recurrence4C0_coeff_7
  recurrence4C0_coeff_70
  recurrence4C0_coeff_71
  recurrence4C0_coeff_72
  recurrence4C0_coeff_73
  recurrence4C0_coeff_74
  recurrence4C0_coeff_75
  recurrence4C0_coeff_76

attribute [local simp]
  recurrence4C0_coeff_77
  recurrence4C0_coeff_78
  recurrence4C0_coeff_79
  recurrence4C0_coeff_8
  recurrence4C0_coeff_80
  recurrence4C0_coeff_81
  recurrence4C0_coeff_82
  recurrence4C0_coeff_83
  recurrence4C0_coeff_84
  recurrence4C0_coeff_85
  recurrence4C0_coeff_86
  recurrence4C0_coeff_87
  recurrence4C0_coeff_88
  recurrence4C0_coeff_89
  recurrence4C0_coeff_9
  recurrence4C0_coeff_90
  recurrence4C0_coeff_91
  recurrence4C0_coeff_92
  recurrence4C0_coeff_93
  recurrence4C0_coeff_94
  recurrence4C0_coeff_95
  recurrence4C0_coeff_96
  recurrence4C0_coeff_97
  recurrence4C0_coeff_98
  recurrence4C0_coeff_99
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar0Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (316 + x) *
        remainder6Coefficient0.coeff (316 - (316 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 316 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (316 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (316 - (316 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_316 :
    recurrence4Scalar0Exceptional.coeff 316 =
      -(((((433798762159304600392 * 10 ^ 70 +
        6334117714533754095217201373668906817883667724575682837153797415677543) * 10 ^ 70 +
        7002446622518497798508101734931855614940267596741813518311435506690398) * 10 ^ 70 +
        9718016451817325384477542225643392659081150652920074988209626104346345) * 10 ^ 70 +
        8509007644537884981997898873007617006656332446420352495054741521361670) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (316 - x)) = _
  rw [show 317 = 163 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (317 + x) *
        remainder6Coefficient0.coeff (317 - (317 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 317 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (317 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (317 - (317 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_317 :
    recurrence4Scalar0Exceptional.coeff 317 =
      (((((247479365378230777082 * 10 ^ 70 +
        5716845709151042841258035236159516062492495130992717754151242892159991) * 10 ^ 70 +
        6438211546712112580424143684054558887438359208558048495546884088488342) * 10 ^ 70 +
        7160413876712967090520240728038416258806203527538410776359940540458222) * 10 ^ 70 +
        0198137535896796519211237915266055971441763397104261681263889491180313) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (317 - x)) = _
  rw [show 318 = 164 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (318 + x) *
        remainder6Coefficient0.coeff (318 - (318 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 318 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (318 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (318 - (318 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_318 :
    recurrence4Scalar0Exceptional.coeff 318 =
      -(((((138367236378942399711 * 10 ^ 70 +
        5413028764315513735809721560373393575710827961841081568785366752729044) * 10 ^ 70 +
        5859345202514130253651530841335607238662954646869397541135059186204257) * 10 ^ 70 +
        3763856318392355865599474965522966086290812679852830712871601788968524) * 10 ^ 70 +
        9904527933533992578144882611992708835346298324986479224247504997697546) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (318 - x)) = _
  rw [show 319 = 165 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (319 + x) *
        remainder6Coefficient0.coeff (319 - (319 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 319 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (319 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (319 - (319 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_319 :
    recurrence4Scalar0Exceptional.coeff 319 =
      (((((75859701209721452128 * 10 ^ 70 +
        5056875306796813346330393412254355912395538461840227776886005916612305) * 10 ^ 70 +
        6723330793614420427370955646073220811185228387188956505954822046018732) * 10 ^ 70 +
        9042060702423386081459558778149794591940057996139937620392867560631148) * 10 ^ 70 +
        8903090972697861114311406236750000235991172520319964171501247879682871) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (319 - x)) = _
  rw [show 320 = 166 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (320 + x) *
        remainder6Coefficient0.coeff (320 - (320 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 320 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (320 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (320 - (320 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_320 :
    recurrence4Scalar0Exceptional.coeff 320 =
      -(((((40795703835268182371 * 10 ^ 70 +
        9340050663842514900216869896451374220593773910460123592493248939029349) * 10 ^ 70 +
        1768757043379541189934668524887464200225177665676079550475163533305749) * 10 ^ 70 +
        2220647506071337529219889183870866423459490125878838358044408156107034) * 10 ^ 70 +
        3928419483278416694907531931892975427103502105525435480967582533995679) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (320 - x)) = _
  rw [show 321 = 167 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (321 + x) *
        remainder6Coefficient0.coeff (321 - (321 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 321 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (321 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (321 - (321 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_321 :
    recurrence4Scalar0Exceptional.coeff 321 =
      (((((21523004518034986587 * 10 ^ 70 +
        0816515951963817663971541920932631729998286720442982259520007328266620) * 10 ^ 70 +
        5278505392280527059958454148436566404448477939858847271995414380032502) * 10 ^ 70 +
        0340144836106027516896673362433851534733155923582780347258637373661468) * 10 ^ 70 +
        6168147798591171891403514275538852087830564302195826547684495197660222) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (321 - x)) = _
  rw [show 322 = 168 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (322 + x) *
        remainder6Coefficient0.coeff (322 - (322 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 322 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (322 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (322 - (322 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_322 :
    recurrence4Scalar0Exceptional.coeff 322 =
      -(((((11139423911414300696 * 10 ^ 70 +
        9621544772117557417292490905641613263491233534828515969339106524189413) * 10 ^ 70 +
        5593250976300245666683261060836850445991777537027983848418952903124631) * 10 ^ 70 +
        8742760527474138603174561124211940298718319277607258519839201367486389) * 10 ^ 70 +
        6281335290483645863829463137137097321052759537528885450678678946395340) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (322 - x)) = _
  rw [show 323 = 169 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (323 + x) *
        remainder6Coefficient0.coeff (323 - (323 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 323 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (323 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (323 - (323 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_323 :
    recurrence4Scalar0Exceptional.coeff 323 =
      (((((5654694391357435660 * 10 ^ 70 +
        8773633169352598211005214714907362302027667255344030469324045720307635) * 10 ^ 70 +
        5558076324469519285212147324384560035753352540356163513199176760183087) * 10 ^ 70 +
        4700213128262358637299984576262974166076824448966813685236734517897964) * 10 ^ 70 +
        6128145745949405818016650497423071815242134458772974522031146354263827) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (323 - x)) = _
  rw [show 324 = 170 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (324 + x) *
        remainder6Coefficient0.coeff (324 - (324 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 324 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (324 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (324 - (324 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_324 :
    recurrence4Scalar0Exceptional.coeff 324 =
      -(((((2814381640588080974 * 10 ^ 70 +
        7508424940708198204278880202529125952407112514166612896980209861218139) * 10 ^ 70 +
        8966657972470791772268776405909924283082637257223139175088147928506047) * 10 ^ 70 +
        3484509368692888280529630998748393359462888954036521378803067440249390) * 10 ^ 70 +
        3236969978747674416878651967291032468096750524208479232608030089120349) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (324 - x)) = _
  rw [show 325 = 171 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (325 + x) *
        remainder6Coefficient0.coeff (325 - (325 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 325 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (325 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (325 - (325 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_325 :
    recurrence4Scalar0Exceptional.coeff 325 =
      (((((1372590114349415669 * 10 ^ 70 +
        2274646982246345503274104232743202774454445415007391522092820321762561) * 10 ^ 70 +
        6995354449644518413449359342890640042800617012271809907204269923794032) * 10 ^ 70 +
        8508993555177914890762516620821623616402513875829731748103550672943372) * 10 ^ 70 +
        4107944407174452053997406249824204896032150456854363099636291658007394) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (325 - x)) = _
  rw [show 326 = 172 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (326 + x) *
        remainder6Coefficient0.coeff (326 - (326 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 326 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (326 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (326 - (326 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_326 :
    recurrence4Scalar0Exceptional.coeff 326 =
      -(((((655445351414752069 * 10 ^ 70 +
        5672922730148791930310467246373327015446876851422650610411630315892057) * 10 ^ 70 +
        5027851490151461902373822123104257910086575457064000618927785257514873) * 10 ^ 70 +
        1918751140323947668314218850709033033148656372080937120689348221463130) * 10 ^ 70 +
        8608040101154428592361798206211395417502734275106900786767634471680187) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (326 - x)) = _
  rw [show 327 = 173 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (327 + x) *
        remainder6Coefficient0.coeff (327 - (327 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 327 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (327 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (327 - (327 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_327 :
    recurrence4Scalar0Exceptional.coeff 327 =
      (((((306118518928448420 * 10 ^ 70 +
        7669049524745767512251514961438112495126139127043873347390523096674350) * 10 ^ 70 +
        6781833642894190998255608663110781451622168920308891930192668682955752) * 10 ^ 70 +
        8672575096537917365813262434234146772606791803038547656713982073756192) * 10 ^ 70 +
        4610753287838445793736733169212715698624586054827018578617666752594839) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (327 - x)) = _
  rw [show 328 = 174 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (328 + x) *
        remainder6Coefficient0.coeff (328 - (328 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 328 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (328 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (328 - (328 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_328 :
    recurrence4Scalar0Exceptional.coeff 328 =
      -(((((139616004840130988 * 10 ^ 70 +
        6899159918836410668321909354167421127617917124194604619769164299053548) * 10 ^ 70 +
        3375172726549048901439050749854316953463654920849484741175804337020754) * 10 ^ 70 +
        9750790826812212056891385032668641789546797941363497435644883135842734) * 10 ^ 70 +
        0265949395052726950127887764007101375939812435111586989584188961205419) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (328 - x)) = _
  rw [show 329 = 175 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (329 + x) *
        remainder6Coefficient0.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 329 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (329 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_329 :
    recurrence4Scalar0Exceptional.coeff 329 =
      (((((62049687364935925 * 10 ^ 70 +
        4776149408739934292272680188197904372384990273717947533689046647521109) * 10 ^ 70 +
        5849905514121633450536643723792326103338024131829687429827348530198857) * 10 ^ 70 +
        9015873084503795679907379127900344405358405370944997239139017456011790) * 10 ^ 70 +
        8462946991396148838747947063725318486663571945830951402958203990753372) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (329 - x)) = _
  rw [show 330 = 176 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (330 + x) *
        remainder6Coefficient0.coeff (330 - (330 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 330 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (330 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (330 - (330 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_330 :
    recurrence4Scalar0Exceptional.coeff 330 =
      -(((((26789028181771436 * 10 ^ 70 +
        6404714850550137876200570340381723502796260827360462785703115953712504) * 10 ^ 70 +
        7682884625042279324708980892013106539273482904536658321775087249946517) * 10 ^ 70 +
        9817632691897397562886029470307569922508379261450867293660195381631391) * 10 ^ 70 +
        2057935782784202286441831463375669931226333787444616156704646357735945) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (330 - x)) = _
  rw [show 331 = 177 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (331 + x) *
        remainder6Coefficient0.coeff (331 - (331 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 331 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (331 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (331 - (331 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_331 :
    recurrence4Scalar0Exceptional.coeff 331 =
      (((((11183328842133886 * 10 ^ 70 +
        0497559387675523257713612481325721247777424411175705136737057957718934) * 10 ^ 70 +
        8473732115815166353196877876240469913797444201835329780815434320281999) * 10 ^ 70 +
        1120629822829861085476020224916491285612485005983623231455866437861682) * 10 ^ 70 +
        5212545007052664719563491413565663916360243477526749276773215053884490) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (331 - x)) = _
  rw [show 332 = 178 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (332 + x) *
        remainder6Coefficient0.coeff (332 - (332 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 332 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (332 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (332 - (332 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_332 :
    recurrence4Scalar0Exceptional.coeff 332 =
      -(((((4481208055887998 * 10 ^ 70 +
        3422665763500063039710090497520494668632175253324832012873203067300752) * 10 ^ 70 +
        3641370478079110163660599982599964554619560012961270283915260376213692) * 10 ^ 70 +
        5368983233251122553073931575796686924793966320722281248167524767212191) * 10 ^ 70 +
        5826758415640317159569194669937419367449309196237157865095391413210330) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (332 - x)) = _
  rw [show 333 = 179 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (333 + x) *
        remainder6Coefficient0.coeff (333 - (333 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 333 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (333 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (333 - (333 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_333 :
    recurrence4Scalar0Exceptional.coeff 333 =
      (((((1702152577690804 * 10 ^ 70 +
        6008478144677673983813564173674915267336848005972894210237341425112841) * 10 ^ 70 +
        4424005345437590844275034777140858794758383241950963136153630448846265) * 10 ^ 70 +
        2860402851662091170104844549920483505486932406451360773514391205446603) * 10 ^ 70 +
        4252058582105882498769864585554583345873398501681514335765163660196489) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (333 - x)) = _
  rw [show 334 = 180 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (334 + x) *
        remainder6Coefficient0.coeff (334 - (334 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 334 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (334 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (334 - (334 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_334 :
    recurrence4Scalar0Exceptional.coeff 334 =
      -(((((598471945740846 * 10 ^ 70 +
        6828290377808724493052214007325316966381502286723137925282469075015843) * 10 ^ 70 +
        5944040599194870712787574458376448035568426258821369570294671382268291) * 10 ^ 70 +
        1314298665596159573422579063149759737730905512077350675486552721002548) * 10 ^ 70 +
        0962391176085916400029797832089622794767156166250123344546573429361011) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (334 - x)) = _
  rw [show 335 = 181 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (335 + x) *
        remainder6Coefficient0.coeff (335 - (335 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 335 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (335 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (335 - (335 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_335 :
    recurrence4Scalar0Exceptional.coeff 335 =
      (((((184489772772104 * 10 ^ 70 +
        4094341626857258493826212250103821641855934863689556618878855666167176) * 10 ^ 70 +
        4341514844573594573271738420327474184538010117143139988105133084179627) * 10 ^ 70 +
        3009947488311972576590752408576529459784794283218698304488352912388893) * 10 ^ 70 +
        9077625317809910743982297970318730339532315799712633638932070903937859) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (335 - x)) = _
  rw [show 336 = 182 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (336 + x) *
        remainder6Coefficient0.coeff (336 - (336 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 336 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (336 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (336 - (336 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_336 :
    recurrence4Scalar0Exceptional.coeff 336 =
      -(((((41789034947383 * 10 ^ 70 +
        9599878693586031651513224888097066562798590242424653144469799380748786) * 10 ^ 70 +
        8797460117203554603697627096393177163940713877781493668104535009634105) * 10 ^ 70 +
        0548381341593462613921166057641437781089256288774770876051746528285173) * 10 ^ 70 +
        0808133122168603469928204298196944614625462237141071729340294437198722) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (336 - x)) = _
  rw [show 337 = 183 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (337 + x) *
        remainder6Coefficient0.coeff (337 - (337 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 337 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (337 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (337 - (337 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_337 :
    recurrence4Scalar0Exceptional.coeff 337 =
      -(((((548535417451 * 10 ^ 70 +
        2897356711471464891227807940955339420138447841279210149909070729054924) * 10 ^ 70 +
        4365246232401716766167251984413452841364868122321499623709912428767316) * 10 ^ 70 +
        7205100960412726588329446054009155002187870784025551549839220501267902) * 10 ^ 70 +
        1608509018893827637724650837710310814609549326969894958299823881536092) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (337 - x)) = _
  rw [show 338 = 184 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
