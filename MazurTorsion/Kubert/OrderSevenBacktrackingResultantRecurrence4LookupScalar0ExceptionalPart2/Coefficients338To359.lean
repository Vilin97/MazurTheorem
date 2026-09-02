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

private theorem recurrence4Scalar0Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (338 + x) *
        remainder6Coefficient0.coeff (338 - (338 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 338 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (338 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (338 - (338 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_338 :
    recurrence4Scalar0Exceptional.coeff 338 =
      (((((9053068472701 * 10 ^ 70 +
        8319507474692214009623356860136884126996693589263308051378829797345690) * 10 ^ 70 +
        0017264991593441026860894816473229650302372561325210839593882159358778) * 10 ^ 70 +
        8237738287149057868169337820618776740215235930073819159342096304805812) * 10 ^ 70 +
        0851422545700015547562152994598023883504461252342838810947349359596156) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (338 - x)) = _
  rw [show 339 = 185 +
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
  rw [recurrence4Scalar0Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (339 + x) *
        remainder6Coefficient0.coeff (339 - (339 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 339 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (339 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (339 - (339 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_339 :
    recurrence4Scalar0Exceptional.coeff 339 =
      -(((((7967715866907 * 10 ^ 70 +
        7851920461900319506129487163713891295618459018274225193626783658123059) * 10 ^ 70 +
        9515908615209919768677070904741429347727698623296063306654901990465626) * 10 ^ 70 +
        2718689128206270662577022625576438063007803915710709311785129015397003) * 10 ^ 70 +
        0763159155907843631380383341204685114263980681900560130993852956679150) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (339 - x)) = _
  rw [show 340 = 186 +
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
  rw [recurrence4Scalar0Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (340 + x) *
        remainder6Coefficient0.coeff (340 - (340 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 340 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (340 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (340 - (340 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_340 :
    recurrence4Scalar0Exceptional.coeff 340 =
      (((((5260841701931 * 10 ^ 70 +
        2241333263035354143371379240057396355518189970114424396702938288357571) * 10 ^ 70 +
        1862028837512041395925648124204223616515855258879644709795829690774045) * 10 ^ 70 +
        9947315173027980652093312599958478595263386706764607105617811982501228) * 10 ^ 70 +
        5088196936874506487928315077102470596870553302988774713406477360449571) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (340 - x)) = _
  rw [show 341 = 187 +
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
  rw [recurrence4Scalar0Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (341 + x) *
        remainder6Coefficient0.coeff (341 - (341 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 341 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (341 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (341 - (341 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_341 :
    recurrence4Scalar0Exceptional.coeff 341 =
      -(((((3069002028179 * 10 ^ 70 +
        7340492704438298333607320730084978267166111743279809448020571494993212) * 10 ^ 70 +
        5109758509025577911813090406101081172078154471584623051670122726414070) * 10 ^ 70 +
        6240087712105419921970394740463322416020840160760456353915312664452049) * 10 ^ 70 +
        3949181826208063123656585292325635175327454335936401720095925237264408) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (341 - x)) = _
  rw [show 342 = 188 +
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
  rw [recurrence4Scalar0Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (342 + x) *
        remainder6Coefficient0.coeff (342 - (342 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 342 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (342 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (342 - (342 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_342 :
    recurrence4Scalar0Exceptional.coeff 342 =
      (((((1666742669598 * 10 ^ 70 +
        1227023903552245867426550027254618823066650987025079409178489555385876) * 10 ^ 70 +
        2840248726594537912151331796404093786028349941615923572822469760578967) * 10 ^ 70 +
        1455422959470792091344144193979034498938320158434513474064500544678494) * 10 ^ 70 +
        4396949455452640862824449625644471755198354176099829893963229818701106) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (342 - x)) = _
  rw [show 343 = 189 +
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
  rw [recurrence4Scalar0Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (343 + x) *
        remainder6Coefficient0.coeff (343 - (343 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 343 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (343 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (343 - (343 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_343 :
    recurrence4Scalar0Exceptional.coeff 343 =
      -(((((862806759108 * 10 ^ 70 +
        3958873564254592187581280549971376661829119354333371656456453175712292) * 10 ^ 70 +
        6867069207764265894653376947552821440870397513941946605202306466191177) * 10 ^ 70 +
        5905051546637897251560581092909843579755619348911101888164000358835396) * 10 ^ 70 +
        4996125837520483953005071298689548457797675371804257273174017066904856) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (343 - x)) = _
  rw [show 344 = 190 +
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
  rw [recurrence4Scalar0Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (344 + x) *
        remainder6Coefficient0.coeff (344 - (344 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 344 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (344 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (344 - (344 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_344 :
    recurrence4Scalar0Exceptional.coeff 344 =
      (((((431155619022 * 10 ^ 70 +
        9844242859685824393014464289685404206805018535154995535179551231113075) * 10 ^ 70 +
        1634811532743022225710692139317287430188096561782336404112311595091172) * 10 ^ 70 +
        3084187889351096004582688225025082189635296269194340506620255439894403) * 10 ^ 70 +
        2153584489784371781279093323260096005446962687096833626309775515957102) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (344 - x)) = _
  rw [show 345 = 191 +
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
  rw [recurrence4Scalar0Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (345 + x) *
        remainder6Coefficient0.coeff (345 - (345 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 345 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (345 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (345 - (345 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_345 :
    recurrence4Scalar0Exceptional.coeff 345 =
      -(((((209555422739 * 10 ^ 70 +
        9316917031207526430822437709531041931832240939632092979228651506841980) * 10 ^ 70 +
        9649002993309230482239322858186681474483976934305262074237336780137246) * 10 ^ 70 +
        4071200589689481800197116046832073280064870663315318530609658303121502) * 10 ^ 70 +
        6405570943809808061150297398824299298590137490554306428915855395372511) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (345 - x)) = _
  rw [show 346 = 192 +
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
  rw [recurrence4Scalar0Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (346 + x) *
        remainder6Coefficient0.coeff (346 - (346 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 346 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (346 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (346 - (346 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_346 :
    recurrence4Scalar0Exceptional.coeff 346 =
      (((((99531955229 * 10 ^ 70 +
        5114902121393700750931524659066643692284513753851678084752528041334037) * 10 ^ 70 +
        8930008710186067797688582537818553725828627915939250460752055486883080) * 10 ^ 70 +
        3659277963832521023388874769950462776069066085814919666031972362210863) * 10 ^ 70 +
        0219053277901020901955960639785231105067733291174944960196818530058801) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (346 - x)) = _
  rw [show 347 = 193 +
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
  rw [recurrence4Scalar0Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (347 + x) *
        remainder6Coefficient0.coeff (347 - (347 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 347 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (347 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (347 - (347 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_347 :
    recurrence4Scalar0Exceptional.coeff 347 =
      -(((((46338715682 * 10 ^ 70 +
        1853375751110162505452174975867701368143251333040243521765690353950178) * 10 ^ 70 +
        3764132739012054499027895113360006618065358449210309780378992884901571) * 10 ^ 70 +
        9736226665261813063491154047057183486106351000300518897552696177472065) * 10 ^ 70 +
        7320697689001777746283042105203794237102341594795671632400259943476035) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (347 - x)) = _
  rw [show 348 = 194 +
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
  rw [recurrence4Scalar0Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (348 + x) *
        remainder6Coefficient0.coeff (348 - (348 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 348 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (348 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (348 - (348 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_348 :
    recurrence4Scalar0Exceptional.coeff 348 =
      (((((21187431959 * 10 ^ 70 +
        8617648174026914850606747902408055676262796796823987775761634948564892) * 10 ^ 70 +
        5616781111865699253133929885128622430098162209065991085518403016091228) * 10 ^ 70 +
        6686949689354591421351097603260316338560600808535926068563264631458040) * 10 ^ 70 +
        6617924942659912876133370084740118908514542532675764303826479237512147) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (348 - x)) = _
  rw [show 349 = 195 +
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
  rw [recurrence4Scalar0Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (349 + x) *
        remainder6Coefficient0.coeff (349 - (349 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 349 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (349 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (349 - (349 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_349 :
    recurrence4Scalar0Exceptional.coeff 349 =
      -(((((9524911506 * 10 ^ 70 +
        5968986705568806164126391638428802410253357078063289026224335986544444) * 10 ^ 70 +
        1759457670407913036936300318876174558048897458379092594467754159054363) * 10 ^ 70 +
        3794729748655135660876803437903290459093967501702240421938246840162312) * 10 ^ 70 +
        2890559384974372815283530290793453525170221572801524177714176819169187) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (349 - x)) = _
  rw [show 350 = 196 +
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
  rw [recurrence4Scalar0Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (350 + x) *
        remainder6Coefficient0.coeff (350 - (350 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 350 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (350 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (350 - (350 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_350 :
    recurrence4Scalar0Exceptional.coeff 350 =
      (((((4212471451 * 10 ^ 70 +
        5659923570943679172632613864831278537152796335758511668504917437131945) * 10 ^ 70 +
        9532598207631174428241540515153819155620127790478298864863316354616873) * 10 ^ 70 +
        5744903411341940673831990945061691077694064444169805154687902173182318) * 10 ^ 70 +
        4732278398648958213410311498129037118683671803420505068446096579671112) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (350 - x)) = _
  rw [show 351 = 197 +
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
  rw [recurrence4Scalar0Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (351 + x) *
        remainder6Coefficient0.coeff (351 - (351 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 351 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (351 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (351 - (351 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_351 :
    recurrence4Scalar0Exceptional.coeff 351 =
      -(((((1832985740 * 10 ^ 70 +
        0538301511777684908407662592689885869319311007660042287642580683287267) * 10 ^ 70 +
        9783893718191507549619988542850743268866053765733808488898845481805749) * 10 ^ 70 +
        7505675178566114688000627750656722276171540830369431168030723096242977) * 10 ^ 70 +
        1375517099636958255372477441573829197372143849915444999982482367182443) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (351 - x)) = _
  rw [show 352 = 198 +
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
  rw [recurrence4Scalar0Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (352 + x) *
        remainder6Coefficient0.coeff (352 - (352 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 352 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (352 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (352 - (352 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_352 :
    recurrence4Scalar0Exceptional.coeff 352 =
      (((((784558303 * 10 ^ 70 +
        4854098743661894853131319756472334392486673754333203124381132869483590) * 10 ^ 70 +
        6217198048720663869360662120922350431256786820341926439671792299625107) * 10 ^ 70 +
        4299286124506981461987237970449732792946700382205831579474859568626796) * 10 ^ 70 +
        8903206333175683699392561207572289024686175356227635599017129698816523) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (352 - x)) = _
  rw [show 353 = 199 +
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
  rw [recurrence4Scalar0Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (353 + x) *
        remainder6Coefficient0.coeff (353 - (353 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 353 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (353 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (353 - (353 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_353 :
    recurrence4Scalar0Exceptional.coeff 353 =
      -(((((330141710 * 10 ^ 70 +
        2816688447825136213693890416395931034460347326916554421016008418907803) * 10 ^ 70 +
        1428783991367048455755779539882582103269705705519754187462111412453429) * 10 ^ 70 +
        4841169380923770545883594556665427400732563716552519932146258262995670) * 10 ^ 70 +
        4636159498641263746882558011374378021552569828631626592000546122532216) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (353 - x)) = _
  rw [show 354 = 200 +
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
  rw [recurrence4Scalar0Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (354 + x) *
        remainder6Coefficient0.coeff (354 - (354 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 354 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (354 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (354 - (354 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_354 :
    recurrence4Scalar0Exceptional.coeff 354 =
      (((((136465743 * 10 ^ 70 +
        3645308922238207117086431383256799707115911436611303878304923304457297) * 10 ^ 70 +
        2544753760365282885805089825631144450160909142798227983636656047010582) * 10 ^ 70 +
        4475039529286354641432611084426068020223786073316548610888104430420322) * 10 ^ 70 +
        9104790482874479111340820773663451615929791268044277926222053567523799) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (354 - x)) = _
  rw [show 355 = 201 +
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
  rw [recurrence4Scalar0Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (355 + x) *
        remainder6Coefficient0.coeff (355 - (355 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 355 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (355 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (355 - (355 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_355 :
    recurrence4Scalar0Exceptional.coeff 355 =
      -(((((55347480 * 10 ^ 70 +
        8922283064620067169955156813478546662604803835776561149768557925071163) * 10 ^ 70 +
        0617042337381127188575503421951879295761214584904211194959749058062786) * 10 ^ 70 +
        6493046505493161421513873453558416944846971097498951517597456916022313) * 10 ^ 70 +
        3287357432921353673791826842090784406986826938374520858638309300054743) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (355 - x)) = _
  rw [show 356 = 202 +
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
  rw [recurrence4Scalar0Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (356 + x) *
        remainder6Coefficient0.coeff (356 - (356 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 356 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (356 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (356 - (356 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_356 :
    recurrence4Scalar0Exceptional.coeff 356 =
      (((((21991594 * 10 ^ 70 +
        0117209148380667335342168343221378853637864999571529214069895881384143) * 10 ^ 70 +
        0943756875196627567613940890770165569862993947789479190540996046808002) * 10 ^ 70 +
        8729913347811572899145967553977364127975280355338388337826854195999242) * 10 ^ 70 +
        1737080916706239286572555302285483231004977625666137073481403935038786) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (356 - x)) = _
  rw [show 357 = 203 +
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
  rw [recurrence4Scalar0Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (357 + x) *
        remainder6Coefficient0.coeff (357 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 357 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (357 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (357 - (357 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_357 :
    recurrence4Scalar0Exceptional.coeff 357 =
      -(((((8542733 * 10 ^ 70 +
        2948836865592444512334228834438577825339597781176374343095154781974787) * 10 ^ 70 +
        7068146923438722446355635594678842037493901056203225998112932735139794) * 10 ^ 70 +
        0266354562344340650161583355779033580407091699520051884501230647225935) * 10 ^ 70 +
        7277224228211412024377720747340237265614054065136267990389624528476523) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (357 - x)) = _
  rw [show 358 = 204 +
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
  rw [recurrence4Scalar0Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (358 + x) *
        remainder6Coefficient0.coeff (358 - (358 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 358 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (358 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (358 - (358 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_358 :
    recurrence4Scalar0Exceptional.coeff 358 =
      (((((3234831 * 10 ^ 70 +
        7325171505310157922797280255071138339909673154884066459541520542509715) * 10 ^ 70 +
        7725080641752298967914681606012643503865732724276242504539152908454950) * 10 ^ 70 +
        5632411385951154872028371824985154143415248990847615628596462570330902) * 10 ^ 70 +
        6356756175592946155657195953553594281323962506433660219764748125550510) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (358 - x)) = _
  rw [show 359 = 205 +
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
  rw [recurrence4Scalar0Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (359 + x) *
        remainder6Coefficient0.coeff (359 - (359 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 359 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (359 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (359 - (359 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_359 :
    recurrence4Scalar0Exceptional.coeff 359 =
      -(((((1188932 * 10 ^ 70 +
        5333856294606041638438803925350240344867767776990734993024365142848435) * 10 ^ 70 +
        0438241685750105882427520105226600827346487353523876127872145803927938) * 10 ^ 70 +
        7918576163235552906387901143693001162774940732369787742000232255634316) * 10 ^ 70 +
        9457340308110162336285984510227857152873807991759001111406846213128894) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (359 - x)) = _
  rw [show 360 = 206 +
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
  rw [recurrence4Scalar0Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
