/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59

attribute [local simp]
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123

attribute [local simp]
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_170
  recurrence4B3A4_coeff_171
  recurrence4B3A4_coeff_172
  recurrence4B3A4_coeff_173
  recurrence4B3A4_coeff_174
  recurrence4B3A4_coeff_175
  recurrence4B3A4_coeff_176
  recurrence4B3A4_coeff_177
  recurrence4B3A4_coeff_178
  recurrence4B3A4_coeff_179
  recurrence4B3A4_coeff_180
  recurrence4B3A4_coeff_181
  recurrence4B3A4_coeff_182
  recurrence4B3A4_coeff_183
  recurrence4B3A4_coeff_184
  recurrence4B3A4_coeff_185
  recurrence4B3A4_coeff_186
  recurrence4B3A4_coeff_187

attribute [local simp]
  recurrence4B3A4_coeff_188
  recurrence4B3A4_coeff_189
  recurrence4B3A4_coeff_190
  recurrence4B3A4_coeff_191
  recurrence4B3A4_coeff_192
  recurrence4B3A4_coeff_193
  recurrence4B3A4_coeff_194
  recurrence4B3A4_coeff_195
  recurrence4B3A4_coeff_196
  recurrence4B3A4_coeff_197
  recurrence4B3A4_coeff_198
  recurrence4B3A4_coeff_199
  recurrence4B3A4_coeff_200
  recurrence4B3A4_coeff_201
  recurrence4B3A4_coeff_202
  recurrence4B3A4_coeff_203
  recurrence4B3A4_coeff_204
  recurrence4B3A4_coeff_205
  recurrence4B3A4_coeff_206
  recurrence4B3A4_coeff_207
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_210
  recurrence4B3A4_coeff_211
  recurrence4B3A4_coeff_212
  recurrence4B3A4_coeff_213
  recurrence4B3A4_coeff_214
  recurrence4B3A4_coeff_215
  recurrence4B3A4_coeff_216
  recurrence4B3A4_coeff_217
  recurrence4B3A4_coeff_218
  recurrence4B3A4_coeff_219
  recurrence4B3A4_coeff_220
  recurrence4B3A4_coeff_221
  recurrence4B3A4_coeff_222
  recurrence4B3A4_coeff_223
  recurrence4B3A4_coeff_224
  recurrence4B3A4_coeff_225
  recurrence4B3A4_coeff_226
  recurrence4B3A4_coeff_227
  recurrence4B3A4_coeff_228
  recurrence4B3A4_coeff_229
  recurrence4B3A4_coeff_230
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_240
  recurrence4B3A4_coeff_241
  recurrence4B3A4_coeff_242
  recurrence4B3A4_coeff_243
  recurrence4B3A4_coeff_244
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251

attribute [local simp]
  recurrence4B3A4_coeff_252
  recurrence4B3A4_coeff_253
  recurrence4B3A4_coeff_254
  recurrence4B3A4_coeff_255
  recurrence4B3A4_coeff_256
  recurrence4B3A4_coeff_257
  recurrence4B3A4_coeff_258
  recurrence4B3A4_coeff_259
  recurrence4B3A4_coeff_260
  recurrence4B3A4_coeff_261
  recurrence4B3A4_coeff_262
  recurrence4B3A4_coeff_263
  recurrence4B3A4_coeff_264
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
  recurrence4B3A4_coeff_275
  recurrence4B3A4_coeff_276
  recurrence4B3A4_coeff_277
  recurrence4B3A4_coeff_278
  recurrence4B3A4_coeff_279
  recurrence4B3A4_coeff_280
  recurrence4B3A4_coeff_281
  recurrence4B3A4_coeff_282
  recurrence4B3A4_coeff_283
  recurrence4B3A4_coeff_284
  recurrence4B3A4_coeff_285
  recurrence4B3A4_coeff_286
  recurrence4B3A4_coeff_287
  recurrence4B3A4_coeff_288
  recurrence4B3A4_coeff_289
  recurrence4B3A4_coeff_290
  recurrence4B3A4_coeff_291
  recurrence4B3A4_coeff_292
  recurrence4B3A4_coeff_293
  recurrence4B3A4_coeff_294
  recurrence4B3A4_coeff_295
  recurrence4B3A4_coeff_296
  recurrence4B3A4_coeff_297
  recurrence4B3A4_coeff_298
  recurrence4B3A4_coeff_299
  recurrence4B3A4_coeff_300
  recurrence4B3A4_coeff_301
  recurrence4B3A4_coeff_302
  recurrence4B3A4_coeff_303
  recurrence4B3A4_coeff_304
  recurrence4B3A4_coeff_305
  recurrence4B3A4_coeff_306
  recurrence4B3A4_coeff_307
  recurrence4B3A4_coeff_308
  recurrence4B3A4_coeff_309
  recurrence4B3A4_coeff_310
  recurrence4B3A4_coeff_311
  recurrence4B3A4_coeff_312
  recurrence4B3A4_coeff_313
  recurrence4B3A4_coeff_314
  recurrence4B3A4_coeff_315

attribute [local simp]
  recurrence4B3A4_coeff_316
  recurrence4B3A4_coeff_317
  recurrence4B3A4_coeff_318
  recurrence4B3A4_coeff_319
  recurrence4B3A4_coeff_320
  recurrence4B3A4_coeff_321
  recurrence4B3A4_coeff_322
  recurrence4B3A4_coeff_323
  recurrence4B3A4_coeff_324
  recurrence4B3A4_coeff_325
  recurrence4B3A4_coeff_326
  recurrence4B3A4_coeff_327
  recurrence4B3A4_coeff_328
  recurrence4B3A4_coeff_329
  recurrence4B3A4_coeff_330
  recurrence4B3A4_coeff_331
  recurrence4B3A4_coeff_332
  recurrence4B3A4_coeff_333
  recurrence4B3A4_coeff_334
  recurrence4B3A4_coeff_335
  recurrence4B3A4_coeff_336
  recurrence4B3A4_coeff_337
  recurrence4B3A4_coeff_338
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar2First_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (355 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (355 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_355 :
    recurrence4Scalar2First.coeff 355 =
      (((((16615 * 10 ^ 70 +
        9448881222827856839309751813730840024388396955754883969870810952658299) * 10 ^ 70 +
        7232027915419667344815925888953483873167063817098748214662727490786380) * 10 ^ 70 +
        1951522647152266231644290371175899774657494107856646917626481723997985) * 10 ^ 70 +
        5496682315436745703000622533078956988708783786037130925845234318384625) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (355 - x)) = _
  rw [show 356 = 13 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (356 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (356 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_356 :
    recurrence4Scalar2First.coeff 356 =
      -(((((7907 * 10 ^ 70 +
        7666635271160424572186450278174248444964403291257375369400253859751503) * 10 ^ 70 +
        2129063077689193850731862204254315873182096047082966066498665544367081) * 10 ^ 70 +
        9648349382289714247118238883958759130206828780562086300190066299037941) * 10 ^ 70 +
        7563723118944998273142883951011041353752364470207021607410832622503824) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (356 - x)) = _
  rw [show 357 = 14 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 31 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (357 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (357 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_357 :
    recurrence4Scalar2First.coeff 357 =
      (((((3580 * 10 ^ 70 +
        5129935116848842143584191247814256944789645984884771144148191213237844) * 10 ^ 70 +
        9049827350256511750369714953636750648092334001125166874737595935665823) * 10 ^ 70 +
        0938181794421500869288648710718714362210840588542740951120548547899877) * 10 ^ 70 +
        4562885420655531681997138179700200647961536050189555576749408385921709) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (357 - x)) = _
  rw [show 358 = 15 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 30 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (358 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (358 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_358 :
    recurrence4Scalar2First.coeff 358 =
      -(((((1558 * 10 ^ 70 +
        2643507630308334802489653233998508362431422760718947829929828858118771) * 10 ^ 70 +
        0663590557783177286084015897755363917582358595139830041163968764945946) * 10 ^ 70 +
        4353907664739787513702003039571740369811789710590155859020417079002255) * 10 ^ 70 +
        7834238367444264414757052736730378334894327992024857591655019629804808) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (358 - x)) = _
  rw [show 359 = 16 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 29 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (359 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (359 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_359 :
    recurrence4Scalar2First.coeff 359 =
      (((((655 * 10 ^ 70 +
        0426735417591091115490380661994423318200891108923866884387519109628487) * 10 ^ 70 +
        9279436394164877912391749689633108498208155438727268566458944915412492) * 10 ^ 70 +
        5329429299024993548697767063928205821919755236498949948851595012626053) * 10 ^ 70 +
        7652921457965690724604296597843740884853032770523592541821395265870164) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (359 - x)) = _
  rw [show 360 = 17 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 28 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (360 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (360 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_360 :
    recurrence4Scalar2First.coeff 360 =
      -(((((266 * 10 ^ 70 +
        4035468829613767150650755057360214216784009928203877220910993369265133) * 10 ^ 70 +
        8063511331056203745060982736487902247654163534884221360642713965364136) * 10 ^ 70 +
        1909704975991294799346476544575894230460515157351336736776430964798852) * 10 ^ 70 +
        7828713651726611938757962475165638327265548971344296691010498962059944) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (360 - x)) = _
  rw [show 361 = 18 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 27 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (361 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (361 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_361 :
    recurrence4Scalar2First.coeff 361 =
      (((((104 * 10 ^ 70 +
        7367886806253447649542393508517861692629943450194045165491959039664485) * 10 ^ 70 +
        9336042604052816412425671437076792625097778487556568802065997961392462) * 10 ^ 70 +
        8269917275028641666284563541160760106575075688870675835334032307473957) * 10 ^ 70 +
        7798706978193503212346185009749905934805342573446515945076961400460213) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (361 - x)) = _
  rw [show 362 = 19 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 26 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (362 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (362 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_362 :
    recurrence4Scalar2First.coeff 362 =
      -(((((39 * 10 ^ 70 +
        6814814764698048713091032937688965243619954326314654224076678531362333) * 10 ^ 70 +
        5881614081805996130934260989374656251128864554744835987702854023612022) * 10 ^ 70 +
        5858403261069192414969762795689906819470608276496170545602862133013788) * 10 ^ 70 +
        1881911142984351554415514285600031694310949254334325015995499025039859) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (362 - x)) = _
  rw [show 363 = 20 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 25 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (363 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (363 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_363 :
    recurrence4Scalar2First.coeff 363 =
      (((((14 * 10 ^ 70 +
        4017014516693052025750350416388251565360563287543506821309215334408529) * 10 ^ 70 +
        2666235075192456178208583463025659768501687137108540272912759227477608) * 10 ^ 70 +
        1552862748760004337699114648690838987461676077023985197462912727033719) * 10 ^ 70 +
        6813227640365097686293357489379422990226174980650897857588775053258297) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (363 - x)) = _
  rw [show 364 = 21 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 24 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (364 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (364 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_364 :
    recurrence4Scalar2First.coeff 364 =
      -(((((4 * 10 ^ 70 +
        9552796448004741978162894467890920256184511994165161142100983062382187) * 10 ^ 70 +
        2486850975366320735147968160202608443682656731017130772513253139261609) * 10 ^ 70 +
        5302417958306139799245688427936766204182406656596217146171931132247088) * 10 ^ 70 +
        5337812150347290443474698270541979480931826952789042597567938258945679) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (364 - x)) = _
  rw [show 365 = 22 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 23 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (365 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (365 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_365 :
    recurrence4Scalar2First.coeff 365 =
      (((((1 * 10 ^ 70 +
        5862447138927228530002325100220948301014361762957916611946391485374073) * 10 ^ 70 +
        1727333697300392438169553971580211370272816238487924708207530342234707) * 10 ^ 70 +
        0131418007106570143878011626690757622362068749286993294286532883290131) * 10 ^ 70 +
        2084965041767019186442628336422060987860656532309385367049059076529286) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (365 - x)) = _
  rw [show 366 = 23 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 22 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (366 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (366 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_366 :
    recurrence4Scalar2First.coeff 366 =
      -((((4543594034307845937095921993300058545761946488455553719582327157756807 * 10 ^ 70 +
        5281883967293960440357876459861342540411580160988983434918846913381049) * 10 ^ 70 +
        2653347653272239938482637588696975538057714276783060012218142660389304) * 10 ^ 70 +
        4610973859144085550911644924999513635483756290008494675620477087787738) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (366 - x)) = _
  rw [show 367 = 24 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 21 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (367 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (367 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_367 :
    recurrence4Scalar2First.coeff 367 =
      ((((1048753576605666811572679606039613877865937082837999037399037068666268 * 10 ^ 70 +
        7056777777190415019194323383661167624192403785696681885062132849515306) * 10 ^ 70 +
        4030132566901394076747126730310260620863698549628727480887596111444959) * 10 ^ 70 +
        6352747566316993537076990760232120095903740505691048290307528061746383) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (367 - x)) = _
  rw [show 368 = 25 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 20 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (368 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (368 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_368 :
    recurrence4Scalar2First.coeff 368 =
      -((((110576430145268469167238609588123085791880914774983608806680290780702 * 10 ^ 70 +
        5862186087906973304090547496627816065010434091035224674413454078408301) * 10 ^ 70 +
        0887056260896600491821878274726641288504989484367441520475506214296359) * 10 ^ 70 +
        8546395572947631890933045342076739543582496305535252821320701442919997) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (368 - x)) = _
  rw [show 369 = 26 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 19 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (369 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (369 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_369 :
    recurrence4Scalar2First.coeff 369 =
      -((((72536958049755527513870068928810325647460804335966727226409496414349 * 10 ^ 70 +
        1489251068628180926342945208352691891341354729157744611091691668717407) * 10 ^ 70 +
        8289011163590703266577049843221511581388083349312797568161394729047917) * 10 ^ 70 +
        7866048431401819988557950373390570865717639506066020581609783003828015) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (369 - x)) = _
  rw [show 370 = 27 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 18 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (370 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (370 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_370 :
    recurrence4Scalar2First.coeff 370 =
      ((((70221309328128595609945611946148285258419577925412837169273643913677 * 10 ^ 70 +
        9343650151894878554796196617996156730435846301944291110127173719226378) * 10 ^ 70 +
        3589344031256572588640748251880684630220469598571192053774066742842884) * 10 ^ 70 +
        9012652181328595328992767830888336266625868821455886005055206439521926) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (370 - x)) = _
  rw [show 371 = 28 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 17 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (371 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (371 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_371 :
    recurrence4Scalar2First.coeff 371 =
      -((((41438190229352366926631260918726071872638749013853075687908074958367 * 10 ^ 70 +
        1206610815624837595886440323802626109607670543645373485784306490490106) * 10 ^ 70 +
        3780061487984503748254689730729219754923691252426957538672533573151498) * 10 ^ 70 +
        3668250587776089848161065790046198087168092006051131085459059514244432) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (371 - x)) = _
  rw [show 372 = 29 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 16 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (372 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (372 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_372 :
    recurrence4Scalar2First.coeff 372 =
      ((((20397107379687218397104305656409755538771244207754938697448650932095 * 10 ^ 70 +
        1701727970051868215715852230331879853131672539172902468591110858659615) * 10 ^ 70 +
        6341007809024521879212593760564939528501335721996331292024422256365937) * 10 ^ 70 +
        0826522661205807120342761599337339451028061417001982313803911302864130) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (372 - x)) = _
  rw [show 373 = 30 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 15 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (373 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (373 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_373 :
    recurrence4Scalar2First.coeff 373 =
      -((((9027332222992998465160093876955259602225643641862949082844367258797 * 10 ^ 70 +
        7692924079007134507896574537717031183360772989533884678853185029940331) * 10 ^ 70 +
        6440462702371041706862323161716909300847858379168488244214283526501383) * 10 ^ 70 +
        8105059874237378995136386339569891097603489049746251211562823294988527) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (373 - x)) = _
  rw [show 374 = 31 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 14 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (374 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (374 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_374 :
    recurrence4Scalar2First.coeff 374 =
      ((((3695489088456919715512143261316964143871181162782846229185121482508 * 10 ^ 70 +
        3726194472380145919269158580654707156917226257009298785295167209512434) * 10 ^ 70 +
        2736616699779278422820351259428314296770127772591388805558871607395136) * 10 ^ 70 +
        0964809481809466266942197930691550656555530170150255592158577671511046) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (374 - x)) = _
  rw [show 375 = 32 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 13 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (375 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (375 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_375 :
    recurrence4Scalar2First.coeff 375 =
      -((((1415834616073323971822809241828577837010846656429121570741854825759 * 10 ^ 70 +
        9282824404851455133647644282107557392751645862838260721376753415047962) * 10 ^ 70 +
        7709205719103042492603941141979155798983415905874875846427939340597316) * 10 ^ 70 +
        3507363613998556326538972838785558132330570203223207984588321330710538) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (375 - x)) = _
  rw [show 376 = 33 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 12 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (376 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (376 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_376 :
    recurrence4Scalar2First.coeff 376 =
      ((((509288026247192895669255812565014487570221869363206697470520514175 * 10 ^ 70 +
        4650998378572053670233488441999580074915389219779155115079468729408238) * 10 ^ 70 +
        4615043851362014193054512970510673113782922681935619253794875781550158) * 10 ^ 70 +
        5762477399062820518408719010616556839560997427268357489445548921933250) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (376 - x)) = _
  rw [show 377 = 34 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 11 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (377 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (377 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_377 :
    recurrence4Scalar2First.coeff 377 =
      -((((171378877498012194157776756332609228293867200974106577845754237835 * 10 ^ 70 +
        2108988931230888692015997863366940613756320784196279474870358645601782) * 10 ^ 70 +
        1004117586887244302902969685709079667479461686649511631518238555584430) * 10 ^ 70 +
        7373633874255848702831931431866839544555294374428833395425384194843824) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (377 - x)) = _
  rw [show 378 = 35 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 10 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (378 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (378 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_378 :
    recurrence4Scalar2First.coeff 378 =
      ((((53290090409385014208321018903153222650351136490927876319512716014 * 10 ^ 70 +
        3287355530017630387648150178816585746688402876985705916214727455165446) * 10 ^ 70 +
        5425569421159316740651855423889739088952511168651264586328112090156356) * 10 ^ 70 +
        7320857212913575899602903746696164336851991980482315201198572661961556) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (378 - x)) = _
  rw [show 379 = 36 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 9 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (379 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (379 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_379 :
    recurrence4Scalar2First.coeff 379 =
      -((((14870396205980421851860769816278447304464053187303313306541894203 * 10 ^ 70 +
        3596008178540840443750767622913567072197640035412770902915606548580925) * 10 ^ 70 +
        7955861506461603707274003906504928782168702565100016190181818740771335) * 10 ^ 70 +
        6735105566731640436932542023207889077124658813961444474595233668982940) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (379 - x)) = _
  rw [show 380 = 37 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 8 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (380 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (380 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_380 :
    recurrence4Scalar2First.coeff 380 =
      ((((3446440543244035889545453204214247833255724805605579289550491284 * 10 ^ 70 +
        3870398614632200796790339278842853532136424151407780989784889823081085) * 10 ^ 70 +
        1003904211913016721424969724914922493713349331002282050771869516409961) * 10 ^ 70 +
        0194208193266655070584386409599393107766542890727311612580439880781745) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (380 - x)) = _
  rw [show 381 = 38 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 7 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (381 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (381 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_381 :
    recurrence4Scalar2First.coeff 381 =
      -((((477851474248902326731234011870993210011912974686808989949611405 * 10 ^ 70 +
        5434490845635971049214510582246645018964021901460550708106098973328751) * 10 ^ 70 +
        1105593086746032810567004335537995238694918929427590478792686337745211) * 10 ^ 70 +
        4651554345104340048124463691483419051596661573118551762153440040800393) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (381 - x)) = _
  rw [show 382 = 39 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 6 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (382 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (382 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_382 :
    recurrence4Scalar2First.coeff 382 =
      -((((109406951691816989711944340828812595762410916924578479489526936 * 10 ^ 70 +
        6837352861861235315738048264644408912574205975930094001830910647727511) * 10 ^ 70 +
        6571577334390745695157565706591702063216129502341794193962133311462537) * 10 ^ 70 +
        3775380507971414771956526112040138707666575729332716552304419516047139) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (382 - x)) = _
  rw [show 383 = 40 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 5 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
