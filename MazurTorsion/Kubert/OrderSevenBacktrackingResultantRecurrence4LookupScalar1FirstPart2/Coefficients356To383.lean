/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_1
  recurrence4B0_coeff_10
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_11
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_12
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_13
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_14
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_15
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156

attribute [local simp]
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_16
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_17
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B0_coeff_18
  recurrence4B0_coeff_19
  recurrence4B0_coeff_2
  recurrence4B0_coeff_20
  recurrence4B0_coeff_21
  recurrence4B0_coeff_22
  recurrence4B0_coeff_23
  recurrence4B0_coeff_24
  recurrence4B0_coeff_25
  recurrence4B0_coeff_26
  recurrence4B0_coeff_27
  recurrence4B0_coeff_28
  recurrence4B0_coeff_29
  recurrence4B0_coeff_3
  recurrence4B0_coeff_30
  recurrence4B0_coeff_31
  recurrence4B0_coeff_32
  recurrence4B0_coeff_33
  recurrence4B0_coeff_34
  recurrence4B0_coeff_35
  recurrence4B0_coeff_36
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_4
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_5
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55

attribute [local simp]
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_6
  recurrence4B0_coeff_60
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_7
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_8
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_9
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
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

attribute [local simp]
  recurrence4B3A4_coeff_117
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
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

attribute [local simp]
  recurrence4B3A4_coeff_181
  recurrence4B3A4_coeff_182
  recurrence4B3A4_coeff_183
  recurrence4B3A4_coeff_184
  recurrence4B3A4_coeff_185
  recurrence4B3A4_coeff_186
  recurrence4B3A4_coeff_187
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

attribute [local simp]
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251
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

attribute [local simp]
  recurrence4B3A4_coeff_309
  recurrence4B3A4_coeff_310
  recurrence4B3A4_coeff_311
  recurrence4B3A4_coeff_312
  recurrence4B3A4_coeff_313
  recurrence4B3A4_coeff_314
  recurrence4B3A4_coeff_315
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

private theorem recurrence4Scalar1First_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (356 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (356 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_356 :
    recurrence4Scalar1First.coeff 356 =
      (((((851976 * 10 ^ 70 +
        6861202570475270929301487694070044769256255556762495152777222809186805) * 10 ^ 70 +
        7372330885671799130478519743361364407590157396781036639041754958953582) * 10 ^ 70 +
        5375185899581397264428337942911416180166869682925717662307980332724714) * 10 ^ 70 +
        8555560008115196139618232605780337015354266360353090223263309498665620) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (356 - x)) = _
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
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 3 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (357 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (357 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_357 :
    recurrence4Scalar1First.coeff 357 =
      -(((((253877 * 10 ^ 70 +
        2380206000907907542852170233132148602911920376869916127166321623721342) * 10 ^ 70 +
        3555636715498769439013741607453454222264754414651112950425043899134167) * 10 ^ 70 +
        8989933343910039967982490565405329663863523854384444934353535556493983) * 10 ^ 70 +
        4516632607776814420989732863860360527085281409716684289716346977511551) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (357 - x)) = _
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
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 2 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (358 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (358 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_358 :
    recurrence4Scalar1First.coeff 358 =
      (((((64570 * 10 ^ 70 +
        1650782620677428846549174400712116548354602966287725226094010354282707) * 10 ^ 70 +
        5432447845671288268465809176087649078011765655243666660159574687688978) * 10 ^ 70 +
        1108621436132708048246076635647907381037287355484377600827905328276361) * 10 ^ 70 +
        3062477158565434299438125887920799124220749130770902489676949301621547) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (358 - x)) = _
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
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 1 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (359 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (359 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_359 :
    recurrence4Scalar1First.coeff 359 =
      -(((((10533 * 10 ^ 70 +
        2683822216095572984240704250894292143820519958778544502210610323818280) * 10 ^ 70 +
        8261963524628190828225973292368918719161854035589149679185367348465199) * 10 ^ 70 +
        2627772648969519811881083292933535672310803409666786993769969300234606) * 10 ^ 70 +
        5236516608108304234384953613382899023261995027660938845564202014265995) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (359 - x)) = _
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
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (360 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (360 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_360 :
    recurrence4Scalar1First.coeff 360 =
      -(((((1951 * 10 ^ 70 +
        3463596655791753038205049041824954578565680802510916982832577910260654) * 10 ^ 70 +
        9609911657349784805521311884467250321605137205823263925758663246530768) * 10 ^ 70 +
        9265134920463351495106422619780046156346351906587654920726703345309727) * 10 ^ 70 +
        5870220332558105876179557555140406172034415432848478796343280133247812) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (360 - x)) = _
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
    rw [show 215 = 31 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (361 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (361 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_361 :
    recurrence4Scalar1First.coeff 361 =
      (((((3203 * 10 ^ 70 +
        9588909337502732589303194746008109281846778703190891236239921734722369) * 10 ^ 70 +
        8623467061352502916850628408989545867553891166549459748263156310573269) * 10 ^ 70 +
        5187792484261685540296128547929426346425645809423327198081718505737134) * 10 ^ 70 +
        8088795575288669636115981398536957192461719810361308035075898720483282) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (361 - x)) = _
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
    rw [show 215 = 30 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (362 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (362 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_362 :
    recurrence4Scalar1First.coeff 362 =
      -(((((2209 * 10 ^ 70 +
        8637711924919552387726588785402920052138677876803079880163420976577135) * 10 ^ 70 +
        9701947638789294440972892472572420222653004709222223540674488461394503) * 10 ^ 70 +
        2913771667491281965026645146940111393990679478250348511857170708646545) * 10 ^ 70 +
        7430898273274215654570980016336947790619902410075855644331644627901032) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (362 - x)) = _
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
    rw [show 215 = 29 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (363 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (363 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_363 :
    recurrence4Scalar1First.coeff 363 =
      (((((1229 * 10 ^ 70 +
        3167494671085977751265218512517282559630595644979351996423747414432720) * 10 ^ 70 +
        4989542920165338798194476688810870210836810618405503093715476177619481) * 10 ^ 70 +
        2306242769979338026024345596135064617031156173256168331023656185774779) * 10 ^ 70 +
        1098057067117486863361155650288178730852445662444003011063237038450819) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (363 - x)) = _
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
    rw [show 215 = 28 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (364 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (364 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_364 :
    recurrence4Scalar1First.coeff 364 =
      -(((((615 * 10 ^ 70 +
        7640152282891802952440751936727121698270705872670437317964155370532330) * 10 ^ 70 +
        6700986196553479603460519095348381286074209567688459646033012168393516) * 10 ^ 70 +
        1004970289879501722692046343851029833304494327809241054365067257350794) * 10 ^ 70 +
        3703712386089266642912692602688122055338525784622983133799323449160762) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (364 - x)) = _
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
    rw [show 215 = 27 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (365 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (365 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_365 :
    recurrence4Scalar1First.coeff 365 =
      (((((288 * 10 ^ 70 +
        8298090657641169610887255330187001979329023652109404500519388574289124) * 10 ^ 70 +
        7760078818161197040168180763398723601221391793043291246784714472651570) * 10 ^ 70 +
        2069324091274291051474823971753815237164111143892800743295049752886367) * 10 ^ 70 +
        2918532800565160008202109163631585431435967213231761300355416630492300) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (365 - x)) = _
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
    rw [show 215 = 26 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (366 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (366 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_366 :
    recurrence4Scalar1First.coeff 366 =
      -(((((129 * 10 ^ 70 +
        1640674902051111219349488827489918620950056300187823854139157049645524) * 10 ^ 70 +
        2471047077594320451224105405179810915817814301516277168866295165259921) * 10 ^ 70 +
        4437526199749040229873364988407695637039397370430993265311808870658941) * 10 ^ 70 +
        5042953232423897496063470166834957832980089037484993698507067773616950) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (366 - x)) = _
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
    rw [show 215 = 25 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (367 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (367 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_367 :
    recurrence4Scalar1First.coeff 367 =
      (((((55 * 10 ^ 70 +
        5776405518916715165325543772487091395850186681832099320599518777218125) * 10 ^ 70 +
        5303526519399962414023965542557988727637821455149935024368492302926550) * 10 ^ 70 +
        8253661923044992872110413059732975287211450887765702426974121804497230) * 10 ^ 70 +
        1736303901264414509573185662732396516311673190680248894961083328590194) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (367 - x)) = _
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
    rw [show 215 = 24 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (368 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (368 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_368 :
    recurrence4Scalar1First.coeff 368 =
      -(((((23 * 10 ^ 70 +
        1205299671398424456572950729854510167893567760643310528842798773146217) * 10 ^ 70 +
        4125214216820201978582283896824414241722350676748676649348073540346042) * 10 ^ 70 +
        0106327765534324124186890367506033100889848660578441639357252039960737) * 10 ^ 70 +
        6863871587931589700163992918996445042236531876126126316161293071970473) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (368 - x)) = _
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
    rw [show 215 = 23 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (369 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (369 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_369 :
    recurrence4Scalar1First.coeff 369 =
      (((((9 * 10 ^ 70 +
        3198928727333220273929122430180730951900932714455752609277058240690264) * 10 ^ 70 +
        2898500518042472865756911914361228630125884600277582074005125183888280) * 10 ^ 70 +
        8715202128605285930405290830521751203796819839293933793093186018795518) * 10 ^ 70 +
        7493386347259548048643945813836794469424575515115540029425406154102566) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (369 - x)) = _
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
    rw [show 215 = 22 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (370 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (370 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_370 :
    recurrence4Scalar1First.coeff 370 =
      -(((((3 * 10 ^ 70 +
        6423407190110081278707077584379028278282588388192409133117120517486882) * 10 ^ 70 +
        1135350636488128198497422395165165983044889432866723959015087560209795) * 10 ^ 70 +
        5078096015786427543296557939894418367046221180974539756637414906153002) * 10 ^ 70 +
        5241154319986574098844836948738757087539702116980593849591163073249327) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (370 - x)) = _
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
    rw [show 215 = 21 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (371 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (371 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_371 :
    recurrence4Scalar1First.coeff 371 =
      (((((1 * 10 ^ 70 +
        3790305773813558327331520067089145731055501305810073876411785236466934) * 10 ^ 70 +
        1580093025033539078802116658929137233235696381707054439420642400631902) * 10 ^ 70 +
        5997454132325943384764172135369842985124105247784250916973705691614737) * 10 ^ 70 +
        0319391072642246526952224708568987385158371849290341245479136589012513) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (371 - x)) = _
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
    rw [show 215 = 20 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (372 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (372 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_372 :
    recurrence4Scalar1First.coeff 372 =
      -((((5047951864859391420025819146589335263571411929779782322989002423592059 * 10 ^ 70 +
        7010010021377975901822815689335923593563163977664297795538336393324785) * 10 ^ 70 +
        1112668442040728157330351251000921228747536798160843342144948015297710) * 10 ^ 70 +
        7427321194077763984336055604355993164810544932175040033595993111937455) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (372 - x)) = _
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
    rw [show 215 = 19 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (373 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (373 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_373 :
    recurrence4Scalar1First.coeff 373 =
      ((((1780318896070156601135532587483620680177540224396097650374124686419224 * 10 ^ 70 +
        1481843244820731374052405711669579058111906062716250820235317038155580) * 10 ^ 70 +
        2743984355333734901327522700089512016498992959424468799105244293687153) * 10 ^ 70 +
        7877078751749458754485134150219633343632697905335961943436445873460589) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (373 - x)) = _
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
    rw [show 215 = 18 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (374 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (374 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_374 :
    recurrence4Scalar1First.coeff 374 =
      -((((601631991357835456485675376232599272730795488542800571001539799401986 * 10 ^ 70 +
        8255464429632497627311848871051479871214905853141921885386760911863120) * 10 ^ 70 +
        3122473271786409416674902585774930740826310969518769131579757593416579) * 10 ^ 70 +
        0118904597430722156228790947083303665588041159651236838614540975548702) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (374 - x)) = _
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
    rw [show 215 = 17 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (375 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (375 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_375 :
    recurrence4Scalar1First.coeff 375 =
      ((((193097130732843364126719796248789832813946564601916143762389572962547 * 10 ^ 70 +
        4491196740798444138685301094187784910619726233934569567185746396930423) * 10 ^ 70 +
        6568980228525511801018295533225119214283363503559868360182070568922305) * 10 ^ 70 +
        6938352280432784840192300705017142850343343074050737538478373180572555) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (375 - x)) = _
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
    rw [show 215 = 16 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (376 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (376 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_376 :
    recurrence4Scalar1First.coeff 376 =
      -((((57976934469364187698044410298575823572005342777990557312952575715899 * 10 ^ 70 +
        9866287851906828752655079065469016940040630118323355411812301902333358) * 10 ^ 70 +
        1323696122225092723911706059891671844176510292686888641711530947235514) * 10 ^ 70 +
        3752593567502528688961421685513674623199935604847478181649363388961721) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (376 - x)) = _
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
    rw [show 215 = 15 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (377 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (377 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_377 :
    recurrence4Scalar1First.coeff 377 =
      ((((15815165317160723710207850131241144582738665260685914897591983707339 * 10 ^ 70 +
        3701709126578915170879601701856687683120903495770349896696156683477942) * 10 ^ 70 +
        3230959977690617102924050171736606480529176183544228934850420108823729) * 10 ^ 70 +
        5631583165281588072054138439934080083284455903176457504440299087360103) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (377 - x)) = _
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
    rw [show 215 = 14 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (378 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (378 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_378 :
    recurrence4Scalar1First.coeff 378 =
      -((((3656221844231908386513134469410256610482869261326742860317941413280 * 10 ^ 70 +
        9604326501536007641118514597661082846176309686494462670849019352106408) * 10 ^ 70 +
        8200059942692213606800446706795723342014695090053589604050168265011148) * 10 ^ 70 +
        3247595671280359189303039026279196183011240432185540827596982521246711) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (378 - x)) = _
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
    rw [show 215 = 13 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (379 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (379 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_379 :
    recurrence4Scalar1First.coeff 379 =
      ((((552779547190033443550116257221212198159756876720724921041489154441 * 10 ^ 70 +
        4279085597894204709052923740124520960036308862436269741341960758261956) * 10 ^ 70 +
        6056200655575935949942807320352467520029473583100537960844668811746262) * 10 ^ 70 +
        7072370310219942713390480262322064288952881642548821214648516533478558) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (379 - x)) = _
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
    rw [show 215 = 12 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (380 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (380 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_380 :
    recurrence4Scalar1First.coeff 380 =
      ((((67733002895135294915147147958686678160430963762690931772465247754 * 10 ^ 70 +
        5809009584659994969667837101321032024116303978684519525042260639121264) * 10 ^ 70 +
        4719251770635413101003814171261464025941428793866344429487018207114070) * 10 ^ 70 +
        0097696664767797938707582107677341790972193667559939858248005126544702) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (380 - x)) = _
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
    rw [show 215 = 11 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (381 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (381 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_381 :
    recurrence4Scalar1First.coeff 381 =
      -((((110786896572173366102496578284293791119201536233770122864341183835 * 10 ^ 70 +
        8074660260407849838986310688374695120236716376975599633557934964542112) * 10 ^ 70 +
        9744526251695890396769847571594633209270035602579439590046838236071078) * 10 ^ 70 +
        3469509430222651343575750311427563193000221224055719224903928358356897) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (381 - x)) = _
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
    rw [show 215 = 10 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (382 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (382 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_382 :
    recurrence4Scalar1First.coeff 382 =
      ((((65416050483493921045371673870005464385898982428340785235777135348 * 10 ^ 70 +
        5087008849296683577834889087751596319967659436728193551325037634848062) * 10 ^ 70 +
        9430585987761779497148960732103937955170655631813066591756823618229422) * 10 ^ 70 +
        3457611224615131280800429370148935646610478559441722633890883957259983) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (382 - x)) = _
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
    rw [show 215 = 9 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (383 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (383 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_383 :
    recurrence4Scalar1First.coeff 383 =
      -((((30169167216653489824769675501638440290429374953786324888243292611 * 10 ^ 70 +
        8396375040253065289625794832748375757901190253692200726535963111627798) * 10 ^ 70 +
        8036791618934710606353484733995457086313805758565107267777471806108287) * 10 ^ 70 +
        7809028912870126231621433342594575219049910769436779258931879797550705) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (383 - x)) = _
  rw [show 384 = 41 +
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
  rw [recurrence4Scalar1First_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_383_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
