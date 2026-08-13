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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
