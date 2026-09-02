/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
