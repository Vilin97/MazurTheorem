/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115
  recurrence4QuotientConstant_coeff_116
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122
  recurrence4QuotientConstant_coeff_123

attribute [local simp]
  recurrence4QuotientConstant_coeff_124
  recurrence4QuotientConstant_coeff_125
  recurrence4QuotientConstant_coeff_126
  recurrence4QuotientConstant_coeff_127
  recurrence4QuotientConstant_coeff_128
  recurrence4QuotientConstant_coeff_129
  recurrence4QuotientConstant_coeff_130
  recurrence4QuotientConstant_coeff_131
  recurrence4QuotientConstant_coeff_132
  recurrence4QuotientConstant_coeff_133
  recurrence4QuotientConstant_coeff_134
  recurrence4QuotientConstant_coeff_135
  recurrence4QuotientConstant_coeff_136
  recurrence4QuotientConstant_coeff_137
  recurrence4QuotientConstant_coeff_138
  recurrence4QuotientConstant_coeff_139
  recurrence4QuotientConstant_coeff_140
  recurrence4QuotientConstant_coeff_141
  recurrence4QuotientConstant_coeff_142
  recurrence4QuotientConstant_coeff_143
  recurrence4QuotientConstant_coeff_144
  recurrence4QuotientConstant_coeff_145
  recurrence4QuotientConstant_coeff_146
  recurrence4QuotientConstant_coeff_147
  recurrence4QuotientConstant_coeff_148
  recurrence4QuotientConstant_coeff_149
  recurrence4QuotientConstant_coeff_150
  recurrence4QuotientConstant_coeff_151
  recurrence4QuotientConstant_coeff_152
  recurrence4QuotientConstant_coeff_153
  recurrence4QuotientConstant_coeff_154
  recurrence4QuotientConstant_coeff_155
  recurrence4QuotientConstant_coeff_156
  recurrence4QuotientConstant_coeff_157
  recurrence4QuotientConstant_coeff_158
  recurrence4QuotientConstant_coeff_159
  recurrence4QuotientConstant_coeff_160
  recurrence4QuotientConstant_coeff_161
  recurrence4QuotientConstant_coeff_162
  recurrence4QuotientConstant_coeff_163
  recurrence4QuotientConstant_coeff_164
  recurrence4QuotientConstant_coeff_165
  recurrence4QuotientConstant_coeff_166
  recurrence4QuotientConstant_coeff_167
  recurrence4QuotientConstant_coeff_168
  recurrence4QuotientConstant_coeff_169
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_180
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187

attribute [local simp]
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
  recurrence4QuotientConstant_coeff_209
  recurrence4QuotientConstant_coeff_210
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_217
  recurrence4QuotientConstant_coeff_218
  recurrence4QuotientConstant_coeff_219
  recurrence4QuotientConstant_coeff_220
  recurrence4QuotientConstant_coeff_221
  recurrence4QuotientConstant_coeff_222
  recurrence4QuotientConstant_coeff_223
  recurrence4QuotientConstant_coeff_224
  recurrence4QuotientConstant_coeff_225
  recurrence4QuotientConstant_coeff_226
  recurrence4QuotientConstant_coeff_227
  recurrence4QuotientConstant_coeff_228
  recurrence4QuotientConstant_coeff_229
  recurrence4QuotientConstant_coeff_230
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_240
  recurrence4QuotientConstant_coeff_241
  recurrence4QuotientConstant_coeff_242
  recurrence4QuotientConstant_coeff_243
  recurrence4QuotientConstant_coeff_244
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_250
  recurrence4QuotientConstant_coeff_251

attribute [local simp]
  recurrence4QuotientConstant_coeff_252
  recurrence4QuotientConstant_coeff_253
  recurrence4QuotientConstant_coeff_254
  recurrence4QuotientConstant_coeff_255
  recurrence4QuotientConstant_coeff_256
  recurrence4QuotientConstant_coeff_257
  recurrence4QuotientConstant_coeff_258
  recurrence4QuotientConstant_coeff_259
  recurrence4QuotientConstant_coeff_260
  recurrence4QuotientConstant_coeff_261
  recurrence4QuotientConstant_coeff_262
  recurrence4QuotientConstant_coeff_263
  recurrence4QuotientConstant_coeff_264
  recurrence4QuotientConstant_coeff_265
  recurrence4QuotientConstant_coeff_266
  recurrence4QuotientConstant_coeff_267
  recurrence4QuotientConstant_coeff_268
  recurrence4QuotientConstant_coeff_269
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_275
  recurrence4QuotientConstant_coeff_276
  recurrence4QuotientConstant_coeff_277
  recurrence4QuotientConstant_coeff_278
  recurrence4QuotientConstant_coeff_279
  recurrence4QuotientConstant_coeff_280
  recurrence4QuotientConstant_coeff_281
  recurrence4QuotientConstant_coeff_282
  recurrence4QuotientConstant_coeff_283
  recurrence4QuotientConstant_coeff_284
  recurrence4QuotientConstant_coeff_285
  recurrence4QuotientConstant_coeff_286
  recurrence4QuotientConstant_coeff_287
  recurrence4QuotientConstant_coeff_288
  recurrence4QuotientConstant_coeff_289
  recurrence4QuotientConstant_coeff_290
  recurrence4QuotientConstant_coeff_291
  recurrence4QuotientConstant_coeff_292
  recurrence4QuotientConstant_coeff_293
  recurrence4QuotientConstant_coeff_294
  recurrence4QuotientConstant_coeff_295
  recurrence4QuotientConstant_coeff_296
  recurrence4QuotientConstant_coeff_297
  recurrence4QuotientConstant_coeff_298
  recurrence4QuotientConstant_coeff_299
  recurrence4QuotientConstant_coeff_300
  recurrence4QuotientConstant_coeff_301
  recurrence4QuotientConstant_coeff_302
  recurrence4QuotientConstant_coeff_303
  recurrence4QuotientConstant_coeff_304
  recurrence4QuotientConstant_coeff_305
  recurrence4QuotientConstant_coeff_306
  recurrence4QuotientConstant_coeff_307
  recurrence4QuotientConstant_coeff_308
  recurrence4QuotientConstant_coeff_309
  recurrence4QuotientConstant_coeff_310
  recurrence4QuotientConstant_coeff_311
  recurrence4QuotientConstant_coeff_312
  recurrence4QuotientConstant_coeff_313
  recurrence4QuotientConstant_coeff_314
  recurrence4QuotientConstant_coeff_315

attribute [local simp]
  recurrence4QuotientConstant_coeff_316
  recurrence4QuotientConstant_coeff_317
  recurrence4QuotientConstant_coeff_318
  recurrence4QuotientConstant_coeff_319
  recurrence4QuotientConstant_coeff_320
  recurrence4QuotientConstant_coeff_321
  recurrence4QuotientConstant_coeff_322
  recurrence4QuotientConstant_coeff_323
  recurrence4QuotientConstant_coeff_324
  recurrence4QuotientConstant_coeff_325
  recurrence4QuotientConstant_coeff_326
  recurrence4QuotientConstant_coeff_327
  recurrence4QuotientConstant_coeff_328
  recurrence4QuotientConstant_coeff_329
  recurrence4QuotientConstant_coeff_330
  recurrence4QuotientConstant_coeff_331
  recurrence4QuotientConstant_coeff_332
  recurrence4QuotientConstant_coeff_333
  recurrence4QuotientConstant_coeff_334
  recurrence4QuotientConstant_coeff_335
  recurrence4QuotientConstant_coeff_336
  recurrence4QuotientConstant_coeff_337
  recurrence4QuotientConstant_coeff_338
  recurrence4QuotientConstant_coeff_339
  recurrence4QuotientConstant_coeff_340
  recurrence4QuotientConstant_coeff_341
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346

private theorem recurrence4Scalar1Second_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (276 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (276 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_276 :
    recurrence4Scalar1Second.coeff 276 =
      -(((((414696313120003193615051761 * 10 ^ 70 +
        1734840517400781688884909974362780170371906720057324092597744669445755) * 10 ^ 70 +
        7793691397724073391850643925371377338301478762902196325321112110594252) * 10 ^ 70 +
        1247162659420384611423799633160551274881525899442169867788157524050856) * 10 ^ 70 +
        8791342322544231624973341324085853718766544748495348350047495116113708) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (276 - x)) = _
  rw [show 277 = 1 +
    276 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 12 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (277 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (277 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_277 :
    recurrence4Scalar1Second.coeff 277 =
      (((((216146235793403465683286961 * 10 ^ 70 +
        2657294957202647441195837873717624220057920454141921034472007145111469) * 10 ^ 70 +
        4536807299961671173862380687601724935270937640721690869814545775807378) * 10 ^ 70 +
        4866799926466922299852764721716687874007579188267017247001060324272847) * 10 ^ 70 +
        7663120910619920231698780876305581779694539411401206149490371561384171) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (277 - x)) = _
  rw [show 278 = 1 +
    277 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 277 = 32 +
      245 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 12 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (278 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (278 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_278 :
    recurrence4Scalar1Second.coeff 278 =
      -(((((83011408796196965796738000 * 10 ^ 70 +
        0840563134968410317867416007602871706416323708714523232856894013684974) * 10 ^ 70 +
        6380597116998680203002962716956339415064256623878519256488471533697363) * 10 ^ 70 +
        4721294385054723992359714707126844253906979002730191397187500330434713) * 10 ^ 70 +
        3194520438488104528096025802481778377388954798028803782977089911990008) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (278 - x)) = _
  rw [show 279 = 1 +
    278 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 12 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (279 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (279 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_279 :
    recurrence4Scalar1Second.coeff 279 =
      -(((((498317851002589993217326 * 10 ^ 70 +
        0255596160461103922040142749167944803789290690103059470661656954086054) * 10 ^ 70 +
        1789634482264714879576972253085667441852797360615144441739571133153477) * 10 ^ 70 +
        7430200434640175165953718957734861519094392627869987466803028454228573) * 10 ^ 70 +
        4505422024494281546273730485950417973951168196882230203238500650136290) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (279 - x)) = _
  rw [show 280 = 1 +
    279 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 12 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (280 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (280 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_280 :
    recurrence4Scalar1Second.coeff 280 =
      (((((47916922210536294833133641 * 10 ^ 70 +
        8778752106918456806136578399070728374708792298864563336328506993274756) * 10 ^ 70 +
        0242178759713763517717769030781893097661177219498814443815813885637387) * 10 ^ 70 +
        4295813211785208441221512837744883877425810989287449285326975115712069) * 10 ^ 70 +
        6270813336560092614805723453111141645544755498273026026087876580433427) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (280 - x)) = _
  rw [show 281 = 1 +
    280 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 280 = 32 +
      248 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 12 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (281 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (281 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_281 :
    recurrence4Scalar1Second.coeff 281 =
      -(((((70334591351116129498150440 * 10 ^ 70 +
        0292462674505449031217732686572526290873623782645937215618202354274942) * 10 ^ 70 +
        5996602550332514687482738525068436884010686216958279071183282239790826) * 10 ^ 70 +
        4859021221659525775085138175923224342794377241331849342404216710248783) * 10 ^ 70 +
        0670149951707988755079860001705790942604397585969485435389090868743897) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (281 - x)) = _
  rw [show 282 = 1 +
    281 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 281 = 32 +
      249 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 12 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (282 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (282 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_282 :
    recurrence4Scalar1Second.coeff 282 =
      (((((76447030877914888018518610 * 10 ^ 70 +
        6034807979989055629667550977552290623664789362514514302049846700384283) * 10 ^ 70 +
        9058691593260411162902715180932756591553333611367646190916257390293396) * 10 ^ 70 +
        1413907576094866526388189075863940762982462571187881997519799218050137) * 10 ^ 70 +
        9165644045956984951504731594900025700519349151819148659115517900633236) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (282 - x)) = _
  rw [show 283 = 1 +
    282 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 12 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (283 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (283 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_283 :
    recurrence4Scalar1Second.coeff 283 =
      -(((((72769224147727054773738202 * 10 ^ 70 +
        6850278585763376158405376310359347531933654937239014629017942378433127) * 10 ^ 70 +
        5767022044696932737356686609268492352548760792639017564396100745907958) * 10 ^ 70 +
        0750192403750083516619114238989337101700593998884975295874418564791425) * 10 ^ 70 +
        1009416339831159817303050003105519478246603756741439403407742216587965) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (283 - x)) = _
  rw [show 284 = 1 +
    283 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 12 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (284 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (284 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_284 :
    recurrence4Scalar1Second.coeff 284 =
      (((((63945926871146795293536506 * 10 ^ 70 +
        3516650004772443529701655532132334297156834719164545958123927172349279) * 10 ^ 70 +
        3274918297238267514452424747307228438100649810644123678068835735889790) * 10 ^ 70 +
        2801585526909819822299774919137309498318459174126952532822702892786897) * 10 ^ 70 +
        4944758614880196148375811253270404874453942019258964119150271084411143) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (284 - x)) = _
  rw [show 285 = 1 +
    284 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 284 = 32 +
      252 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 252 = 32 +
      220 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 12 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (285 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (285 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_285 :
    recurrence4Scalar1Second.coeff 285 =
      -(((((53101965312145742262946590 * 10 ^ 70 +
        2175752257306003455047716629550525863594919132803898695254802907549466) * 10 ^ 70 +
        2446879139894284672237631153855645275505597125335306871453529015725157) * 10 ^ 70 +
        8400638058943688756768810825524628565482017719816805143391884762286936) * 10 ^ 70 +
        5674003540920214008448956728511391437252375045479113823723705472144857) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (285 - x)) = _
  rw [show 286 = 1 +
    285 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 285 = 32 +
      253 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 253 = 32 +
      221 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 12 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (286 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (286 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_286 :
    recurrence4Scalar1Second.coeff 286 =
      (((((42189161471901010190373474 * 10 ^ 70 +
        8445173405615473207852871503176773532488888658771618125283567314621898) * 10 ^ 70 +
        0681799714552706822244727388222734336290786395402889566651175537129926) * 10 ^ 70 +
        3360085217455980907161694377868406472729362589868352148717817933491665) * 10 ^ 70 +
        6922256940686057943811900777883385413830491190938030418279166608181240) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (286 - x)) = _
  rw [show 287 = 1 +
    286 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 286 = 32 +
      254 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 254 = 32 +
      222 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 12 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (287 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (287 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_287 :
    recurrence4Scalar1Second.coeff 287 =
      -(((((32300892342281587076125890 * 10 ^ 70 +
        6408768072331458872066274514723943256946060949978653100792408113034380) * 10 ^ 70 +
        1185849662649221080772517577269516465839959765216757374807410234056851) * 10 ^ 70 +
        0812322533616797119074718159937646114466827430618336449689805068362342) * 10 ^ 70 +
        3861634578422653122337956732826790629822296432410754732935582515424650) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (287 - x)) = _
  rw [show 288 = 1 +
    287 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 287 = 32 +
      255 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 255 = 32 +
      223 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 12 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (288 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (288 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_288 :
    recurrence4Scalar1Second.coeff 288 =
      (((((23938072605499024198731853 * 10 ^ 70 +
        3116478561362226048621608936524919096771654639496053504038188500764690) * 10 ^ 70 +
        3110857591733540304659390103028254803074320681724409889769156434023078) * 10 ^ 70 +
        8810722306540227692968524318505199611108879300059081241790872027970127) * 10 ^ 70 +
        2643614574949040489705740920849016580583944539875524206937209303927687) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (288 - x)) = _
  rw [show 289 = 1 +
    288 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 288 = 32 +
      256 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 256 = 32 +
      224 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 12 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (289 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (289 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_289 :
    recurrence4Scalar1Second.coeff 289 =
      -(((((17220656245677441423424161 * 10 ^ 70 +
        2857030299994700340808304281570231219674135066680775971203693439257917) * 10 ^ 70 +
        5118699683733792294521831463994480405654045487091951535507479119971424) * 10 ^ 70 +
        7569324054243081320335208948845013913646899499706815287232160338730170) * 10 ^ 70 +
        3252097527573166927582805343363334834579811210963860382848025715172126) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (289 - x)) = _
  rw [show 290 = 1 +
    289 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 289 = 32 +
      257 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 257 = 32 +
      225 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 12 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (290 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (290 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_290 :
    recurrence4Scalar1Second.coeff 290 =
      (((((12046176453276914208343302 * 10 ^ 70 +
        0283454298477727244803543080755929330682368142452760093574123476377277) * 10 ^ 70 +
        9660495529500886323439774482368115849376346704404891917953336592679556) * 10 ^ 70 +
        2211300667109293408961356023959284136222504907040988131760947060869395) * 10 ^ 70 +
        5530239582913246990042122637865713031980346317511672328413479702509718) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (290 - x)) = _
  rw [show 291 = 1 +
    290 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 290 = 32 +
      258 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 258 = 32 +
      226 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 12 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (291 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (291 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_291 :
    recurrence4Scalar1Second.coeff 291 =
      -(((((8201487655351281685620699 * 10 ^ 70 +
        1664116212183905558048444199453354223936581552660315340116845841296478) * 10 ^ 70 +
        9677968313162969983721233856884593195300494853389615937329157574559148) * 10 ^ 70 +
        4269370312056018822240881693647832017890869802949727373740715834850700) * 10 ^ 70 +
        4297625336171240903558174059381272867062762302399368089321229198759249) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (291 - x)) = _
  rw [show 292 = 1 +
    291 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 291 = 32 +
      259 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 259 = 32 +
      227 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 12 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (292 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (292 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_292 :
    recurrence4Scalar1Second.coeff 292 =
      (((((5436165378255907178321965 * 10 ^ 70 +
        6806875757730722233601368132968079737843538802907177537707165443461158) * 10 ^ 70 +
        0185415631776818808793635207288539991293429646091729975924239527322254) * 10 ^ 70 +
        8376941686803589563510984304731946821315058026522125890037521559544306) * 10 ^ 70 +
        9570635247419495541145298452288224275975486486699484623284560475231824) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (292 - x)) = _
  rw [show 293 = 1 +
    292 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 292 = 32 +
      260 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 260 = 32 +
      228 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 12 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (293 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (293 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_293 :
    recurrence4Scalar1Second.coeff 293 =
      -(((((3506538844549637686014138 * 10 ^ 70 +
        8974308439608682126356937804675213739778963034441835545008300651523287) * 10 ^ 70 +
        2903841376916050370473398569245975131510613739968217079368614700623147) * 10 ^ 70 +
        1973206825579395349639288243099526380404988318196379084791895973824351) * 10 ^ 70 +
        5987074702783749242443207579867948485867087834920066345941284412398110) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (293 - x)) = _
  rw [show 294 = 1 +
    293 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 293 = 32 +
      261 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 261 = 32 +
      229 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 12 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (294 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (294 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_294 :
    recurrence4Scalar1Second.coeff 294 =
      (((((2198675766275309073472588 * 10 ^ 70 +
        1909298167745954332755604233765473637067389429952627165143524531563872) * 10 ^ 70 +
        6116880450373876587595004820553229060086570856723792184975928830552096) * 10 ^ 70 +
        8864197501851200024217558773042965554547652052515182690851972946589771) * 10 ^ 70 +
        1944806760481218046605363665232546541487615595148184690093822214018179) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (294 - x)) = _
  rw [show 295 = 1 +
    294 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 294 = 32 +
      262 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 262 = 32 +
      230 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (295 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (295 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_295 :
    recurrence4Scalar1Second.coeff 295 =
      -(((((1337335261390774441255456 * 10 ^ 70 +
        4436176987849074157471310868210602489786013185295380730615363594323432) * 10 ^ 70 +
        7232774890850661946741876899141342558153502427266009737637851778918153) * 10 ^ 70 +
        5514837084354269062632895449489259338087322156515273497212524120282877) * 10 ^ 70 +
        8486326106492958110884441834148014369700934409059393349094536437505615) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (295 - x)) = _
  rw [show 296 = 1 +
    295 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 295 = 32 +
      263 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 263 = 32 +
      231 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 12 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (296 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (296 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_296 :
    recurrence4Scalar1Second.coeff 296 =
      (((((786361923335936257859523 * 10 ^ 70 +
        6602565443797512536243086268975857432643619070636949060645151988115154) * 10 ^ 70 +
        8158332646471527698883540670719235477751709603970216132530154527993094) * 10 ^ 70 +
        8951860216603816001200791487765862929956144795655392230436195392303527) * 10 ^ 70 +
        7649225891817234045253723916050788496670372201372432063092451213445468) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (296 - x)) = _
  rw [show 297 = 1 +
    296 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 296 = 32 +
      264 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 264 = 32 +
      232 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 12 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (297 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (297 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_297 :
    recurrence4Scalar1Second.coeff 297 =
      -(((((444491260249716554177412 * 10 ^ 70 +
        9168800103515254271268696599518284091869162028822646411405802186947350) * 10 ^ 70 +
        8678197936789985249036557695150718343360735153955684814748638765750435) * 10 ^ 70 +
        3081435446867021224066195799925246277385391526426805150446870640981428) * 10 ^ 70 +
        3194478667379330133151859545331392073743701972023431959962352667116302) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (297 - x)) = _
  rw [show 298 = 1 +
    297 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 297 = 32 +
      265 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 265 = 32 +
      233 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 12 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (298 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (298 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_298 :
    recurrence4Scalar1Second.coeff 298 =
      (((((239236212095690157590510 * 10 ^ 70 +
        4063435190157922895839310170290918231415600134345153160992539224136646) * 10 ^ 70 +
        4680543549001688540971969716528087455956945062262183092669659758899211) * 10 ^ 70 +
        8709199975860916386278773672816852057661837782689007502970969090755938) * 10 ^ 70 +
        6621725539143562660291441277601467493558191250117208489966462352839074) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (298 - x)) = _
  rw [show 299 = 1 +
    298 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 298 = 32 +
      266 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 266 = 32 +
      234 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 12 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (299 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (299 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_299 :
    recurrence4Scalar1Second.coeff 299 =
      -(((((120495900899051578051142 * 10 ^ 70 +
        7474595864032216586512740385207742370151820571163844427352175856807882) * 10 ^ 70 +
        3784712394766547732819095788282676527315925368319678726977470377762865) * 10 ^ 70 +
        1468227557813873006760254330795370099927319946167067152001261423472394) * 10 ^ 70 +
        6134891631450420894734422655369777187334782854880008734202375037963103) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (299 - x)) = _
  rw [show 300 = 1 +
    299 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 299 = 32 +
      267 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 267 = 32 +
      235 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 12 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (300 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (300 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_300 :
    recurrence4Scalar1Second.coeff 300 =
      (((((54776647058971683462586 * 10 ^ 70 +
        8840902127560143274250487126000994286967656814220089562410995315770419) * 10 ^ 70 +
        0459528334243066579563259419538421944971581158063380473718104606906047) * 10 ^ 70 +
        8302506971074347538528370127047783562803469048077529128747473146563415) * 10 ^ 70 +
        7828225666563745275354517157462141160954302958781619490563062357390463) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (300 - x)) = _
  rw [show 301 = 1 +
    300 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 300 = 32 +
      268 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 268 = 32 +
      236 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 12 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (301 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (301 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_301 :
    recurrence4Scalar1Second.coeff 301 =
      -(((((20409070514343596798539 * 10 ^ 70 +
        7940959988936659697575496549884107449517982733195344996790586121978938) * 10 ^ 70 +
        9029308708540850951717982605373439751833912843025896391219551335633468) * 10 ^ 70 +
        2347165501697713577086629565227056755434508027840865779874314061605577) * 10 ^ 70 +
        3289721286343914447917998849961924330686053784984726173614503764248692) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (301 - x)) = _
  rw [show 302 = 1 +
    301 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 301 = 32 +
      269 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 269 = 32 +
      237 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 12 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (302 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (302 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_302 :
    recurrence4Scalar1Second.coeff 302 =
      (((((3834037411607361091259 * 10 ^ 70 +
        3483347502048911596897545389391165745106066620708956628108901761326215) * 10 ^ 70 +
        2736009000978119246531569110163676001208840270854743293920879285247678) * 10 ^ 70 +
        3834399851674532642888653065796323207997013529381514407905598317429625) * 10 ^ 70 +
        1093524819759090280637842384336181954020899220185627495064779542738981) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (302 - x)) = _
  rw [show 303 = 1 +
    302 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 302 = 32 +
      270 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 12 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (303 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (303 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_303 :
    recurrence4Scalar1Second.coeff 303 =
      (((((3138279589319785921388 * 10 ^ 70 +
        0455307676187021995396528383388515203829319748820027324029915247872836) * 10 ^ 70 +
        3974601734272882234636784054485433479018139682731213472916267155016791) * 10 ^ 70 +
        3566242496770598577001237608585498491289378784029838002244147355943151) * 10 ^ 70 +
        5552185259365551714350248660001571287809474387075280943306711057617749) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (303 - x)) = _
  rw [show 304 = 1 +
    303 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 303 = 32 +
      271 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 12 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (304 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (304 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_304 :
    recurrence4Scalar1Second.coeff 304 =
      -(((((5264807904993948205421 * 10 ^ 70 +
        7271422325869752236914092190760014749128273175423279022405343503019451) * 10 ^ 70 +
        1212767991081717566948377102496052370536001030902890076404561899650933) * 10 ^ 70 +
        8356677446007604645781195875387697447287142918416907450603834271026868) * 10 ^ 70 +
        4554743410838747612131030475375570264926438971469593839583835445267425) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (304 - x)) = _
  rw [show 305 = 1 +
    304 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 304 = 32 +
      272 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 12 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (305 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (305 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_305 :
    recurrence4Scalar1Second.coeff 305 =
      (((((5184609788177044872231 * 10 ^ 70 +
        8515269466706654492780709085519167243278465629556335267124007116570447) * 10 ^ 70 +
        4936554740503091020476521951740745223432501240005833425787821000117789) * 10 ^ 70 +
        2756887486442287622417661561595849124100829560103531961039395934226794) * 10 ^ 70 +
        3578740685243145178717332070724380615535833841757304450787901610805983) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (305 - x)) = _
  rw [show 306 = 1 +
    305 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 305 = 32 +
      273 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 12 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (306 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (306 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_306 :
    recurrence4Scalar1Second.coeff 306 =
      -(((((4279135761154146919908 * 10 ^ 70 +
        1073674942477209526077606925332915259407341704061712588720685186363156) * 10 ^ 70 +
        3762323291655234075002110225658607861780736437693786361063159262564590) * 10 ^ 70 +
        3640209537526864581416712191695232478892088277660603125814694373844098) * 10 ^ 70 +
        7553407835710058711467163705503263368811514021667215701123974561418064) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (306 - x)) = _
  rw [show 307 = 1 +
    306 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 306 = 32 +
      274 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 12 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (307 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (307 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_307 :
    recurrence4Scalar1Second.coeff 307 =
      (((((3214541556981382236743 * 10 ^ 70 +
        5258153026853410625137083280663778992630741912565296357341910895114121) * 10 ^ 70 +
        6611880493997961669318681884289229748564962791173991675074064019324085) * 10 ^ 70 +
        5695279627197141270119195113870118224195030136420991285322384888945751) * 10 ^ 70 +
        2096334217739349808027938845678209620630413648535249705262259907745182) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (307 - x)) = _
  rw [show 308 = 1 +
    307 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 307 = 32 +
      275 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (308 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (308 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_308 :
    recurrence4Scalar1Second.coeff 308 =
      -(((((2270758219878421571440 * 10 ^ 70 +
        2288753780267012178205826765843577994827247419824638037426538067120108) * 10 ^ 70 +
        2451868124688815719029260693952367317212058302518037908154742142580524) * 10 ^ 70 +
        0607317997052655950437123660579281131312107064571815448090947875640573) * 10 ^ 70 +
        4978355122316906112032164711167179650178807670636740806045800381324942) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (308 - x)) = _
  rw [show 309 = 1 +
    308 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 308 = 32 +
      276 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 12 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (309 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (309 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_309 :
    recurrence4Scalar1Second.coeff 309 =
      (((((1533050901045379179631 * 10 ^ 70 +
        0899481158284711606005910273537271474777822191680510280486984098402253) * 10 ^ 70 +
        5481579919061576662510001145934146614001401622822667507362893550147878) * 10 ^ 70 +
        3752463868858335134094317034156297487359201697138515851403830452432574) * 10 ^ 70 +
        1291796633000815803024380300204707353565259742431341153020253782214659) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (309 - x)) = _
  rw [show 310 = 1 +
    309 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 309 = 32 +
      277 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 277 = 32 +
      245 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 12 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (310 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (310 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_310 :
    recurrence4Scalar1Second.coeff 310 =
      -(((((998308970396484890582 * 10 ^ 70 +
        2865799468707814301753879503088967004765082689485572368757873754602923) * 10 ^ 70 +
        3292608785542249217636911459076230380791625506352289567640777099482158) * 10 ^ 70 +
        9672190834791528301181922989742387102956765191043589140569561238269703) * 10 ^ 70 +
        0735608498102295187571806351297206314382471573982906875872189353026096) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (310 - x)) = _
  rw [show 311 = 1 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 12 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (311 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (311 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_311 :
    recurrence4Scalar1Second.coeff 311 =
      (((((630584383189671915658 * 10 ^ 70 +
        9162439526689545537921900041562238944151383333180343556315727661385648) * 10 ^ 70 +
        0928646571084137327184866158025116020823432229724734908108434916516154) * 10 ^ 70 +
        0771293687735790943901037463795649367427855643632724895710582508380103) * 10 ^ 70 +
        0356398726188656898031454963092641549310126325712061683645872623327178) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (311 - x)) = _
  rw [show 312 = 1 +
    311 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 12 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (312 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (312 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_312 :
    recurrence4Scalar1Second.coeff 312 =
      -(((((387764030062144711012 * 10 ^ 70 +
        3765300961213316132428881018363695220361680247655754753856082232605610) * 10 ^ 70 +
        4528360925527743166437765802720677435122638464638693935739018157498347) * 10 ^ 70 +
        3963599575185433581632282632065178468877351182863830565433797951331318) * 10 ^ 70 +
        4127648769916319348828620464100331484213352573804191792609040226676089) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (312 - x)) = _
  rw [show 313 = 1 +
    312 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 312 = 32 +
      280 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 280 = 32 +
      248 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 12 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (313 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (313 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_313 :
    recurrence4Scalar1Second.coeff 313 =
      (((((232689790114992099143 * 10 ^ 70 +
        1621870040727369362880505367647411018323894215343479679443054282259486) * 10 ^ 70 +
        3770763426611973010656413078091601772965902123704520301359136682010417) * 10 ^ 70 +
        4504485758083579506504389746966464712281004972543506709170436272938532) * 10 ^ 70 +
        1982684902583463245333650940372772599939921404082085888774568884787654) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (313 - x)) = _
  rw [show 314 = 1 +
    313 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 313 = 32 +
      281 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 281 = 32 +
      249 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 12 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (314 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (314 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_314 :
    recurrence4Scalar1Second.coeff 314 =
      -(((((136475838324482626889 * 10 ^ 70 +
        6659934573418886476435945707483684818493702177152086758627991056759199) * 10 ^ 70 +
        8798833627859750210541059863665392652342022357459769247549289622275760) * 10 ^ 70 +
        2444337930136996896765004879385208492324309454947249968624550878054815) * 10 ^ 70 +
        7983953768622538815144584941402479358025360345327464678622044971283159) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (314 - x)) = _
  rw [show 315 = 1 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 12 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (315 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (315 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_315 :
    recurrence4Scalar1Second.coeff 315 =
      (((((78312773955928452454 * 10 ^ 70 +
        9583783364279780059782113332810551126770576779141033124097999428183933) * 10 ^ 70 +
        1948763130247773804746746684146709379149820553301202078776252647424140) * 10 ^ 70 +
        6142531133529514449026623573703942454133859889293877241095171986683847) * 10 ^ 70 +
        8785538243308343802637474818937980022413149312432242118164487411315865) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (315 - x)) = _
  rw [show 316 = 1 +
    315 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 12 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (316 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (316 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_316 :
    recurrence4Scalar1Second.coeff 316 =
      -(((((43989009181657161266 * 10 ^ 70 +
        7160111622579197959855306833805319214786916489627594370628487108441912) * 10 ^ 70 +
        2439274485126958771592096801876141250007786248565741885044685922753625) * 10 ^ 70 +
        0878317119491393232097227812149875218757172024411400561959902849917125) * 10 ^ 70 +
        4740859971587852327985367817822144238225625638571361198236285724511428) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (316 - x)) = _
  rw [show 317 = 1 +
    316 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 316 = 32 +
      284 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 284 = 32 +
      252 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 252 = 32 +
      220 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 12 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (317 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (317 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_317 :
    recurrence4Scalar1Second.coeff 317 =
      (((((24191746077035536327 * 10 ^ 70 +
        4096298773579762199137998469893034973273924757679749842097183773586452) * 10 ^ 70 +
        4407355074725207260784382966570220044589091308742966814124049619523268) * 10 ^ 70 +
        8575002662050107614996105636849043981352814692231388454574687342103601) * 10 ^ 70 +
        3417763504683424237966398736080156893151740295262700430528086456209461) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (317 - x)) = _
  rw [show 318 = 1 +
    317 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 317 = 32 +
      285 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 285 = 32 +
      253 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 253 = 32 +
      221 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 12 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (318 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (318 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_318 :
    recurrence4Scalar1Second.coeff 318 =
      -(((((13023707548663505336 * 10 ^ 70 +
        2588891074865954057849178571574352769645220634248500410839604116819032) * 10 ^ 70 +
        1012957968562993321773361987303975150959041865920207318887630168630513) * 10 ^ 70 +
        2910937249049299033722562375860403264976325052341925433784431582214976) * 10 ^ 70 +
        6947602836605387184511601792001317991866750647591832893042605763261005) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (318 - x)) = _
  rw [show 319 = 1 +
    318 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 318 = 32 +
      286 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 286 = 32 +
      254 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 254 = 32 +
      222 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 12 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (319 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (319 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_319 :
    recurrence4Scalar1Second.coeff 319 =
      (((((6860199310039750944 * 10 ^ 70 +
        9595855611620893113109764992633792019994788021969487076079504248451091) * 10 ^ 70 +
        4488681022144613254762103525707409417780069579225942980281705117115737) * 10 ^ 70 +
        3521636851186120058374137351704269799209987188435594317560356174883667) * 10 ^ 70 +
        5886224726577122451417815992056254265725894984834950142148681445687169) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (319 - x)) = _
  rw [show 320 = 1 +
    319 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 319 = 32 +
      287 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 287 = 32 +
      255 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 255 = 32 +
      223 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 12 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (320 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (320 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_320 :
    recurrence4Scalar1Second.coeff 320 =
      -(((((3532707886784291354 * 10 ^ 70 +
        6964746523916850833068209499673139259148341840774601526996499172921035) * 10 ^ 70 +
        1983453882609471331886541912818700715988515913369159519711103756202537) * 10 ^ 70 +
        1947638159396404553005981026353712716160930453619510309186156979767219) * 10 ^ 70 +
        6933438090815703341099211477098436224321424466777858520102577875012099) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (320 - x)) = _
  rw [show 321 = 1 +
    320 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 320 = 32 +
      288 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 288 = 32 +
      256 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 256 = 32 +
      224 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 12 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (321 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (321 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_321 :
    recurrence4Scalar1Second.coeff 321 =
      (((((1776210168241853911 * 10 ^ 70 +
        4129367915385302176946289719489747020001518785612239786779530488463502) * 10 ^ 70 +
        7137845035250581598025562050589149544036950544868529437987301839931281) * 10 ^ 70 +
        5975817605372878980103282239300615220689637713884975588790383008747033) * 10 ^ 70 +
        7675457301750829477585878936194446180647489166400184025753944911797375) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (321 - x)) = _
  rw [show 322 = 1 +
    321 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 321 = 32 +
      289 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 289 = 32 +
      257 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 257 = 32 +
      225 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 12 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (322 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (322 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_322 :
    recurrence4Scalar1Second.coeff 322 =
      -(((((870358974638998068 * 10 ^ 70 +
        2418193211716434892953742458412383860043352843891017500237224069873725) * 10 ^ 70 +
        7205236846638786245841997043923928883322940117427339703087814876371703) * 10 ^ 70 +
        5611668791507559542490608772500606504170613058436999751478565549419685) * 10 ^ 70 +
        8550958379540096172648481901764460461324420410870840969321331853006435) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (322 - x)) = _
  rw [show 323 = 1 +
    322 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 322 = 32 +
      290 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 290 = 32 +
      258 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 258 = 32 +
      226 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 12 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (323 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (323 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_323 :
    recurrence4Scalar1Second.coeff 323 =
      (((((414549861077786904 * 10 ^ 70 +
        8641168617075850781825592610653892701901775867636470834105501221261479) * 10 ^ 70 +
        6024344650680363773848254935944954495650032413685621770671168935655329) * 10 ^ 70 +
        4022982486020332131962967992702737796837122725647251617266373458808433) * 10 ^ 70 +
        2288738617778695784172315861580015047561259230723277017290351658790811) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (323 - x)) = _
  rw [show 324 = 1 +
    323 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 323 = 32 +
      291 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 291 = 32 +
      259 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 259 = 32 +
      227 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 12 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (324 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (324 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_324 :
    recurrence4Scalar1Second.coeff 324 =
      -(((((191189816485422398 * 10 ^ 70 +
        1718008314104956123800538493917005908315445898436579393078092621711306) * 10 ^ 70 +
        8661581490658727035305937668066461303152516235548217991143816346608818) * 10 ^ 70 +
        2710323830127546345006481894745943247236582314941999332664780725790600) * 10 ^ 70 +
        7248223366954840034984260391074760151029492190965790022081904361612726) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (324 - x)) = _
  rw [show 325 = 1 +
    324 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 324 = 32 +
      292 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 292 = 32 +
      260 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 260 = 32 +
      228 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 12 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (325 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (325 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_325 :
    recurrence4Scalar1Second.coeff 325 =
      (((((84888451501799104 * 10 ^ 70 +
        8648780486574059518950333945104627994653861344452870649803491677189118) * 10 ^ 70 +
        8116070860625897994313424368558881529819564910641045896107428038920532) * 10 ^ 70 +
        9527981551933038572152482409760597296902970635296358700743323778420912) * 10 ^ 70 +
        0113985777275805680013226534269762744405601818128314087596195152341643) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (325 - x)) = _
  rw [show 326 = 1 +
    325 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 325 = 32 +
      293 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 293 = 32 +
      261 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 261 = 32 +
      229 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 12 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (326 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (326 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_326 :
    recurrence4Scalar1Second.coeff 326 =
      -(((((35950791369016447 * 10 ^ 70 +
        8137101259747827141404626161308693796257586757813562846088423910961929) * 10 ^ 70 +
        0184858063974856454239447110869672910122384235580429388962174374410040) * 10 ^ 70 +
        1757384057710486250917968792311747364258474360913016355394991637997501) * 10 ^ 70 +
        8421779152247678238487600066686512496048930073339321511081524586276800) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (326 - x)) = _
  rw [show 327 = 1 +
    326 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 326 = 32 +
      294 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 294 = 32 +
      262 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 262 = 32 +
      230 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (327 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (327 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_327 :
    recurrence4Scalar1Second.coeff 327 =
      (((((14290256198521147 * 10 ^ 70 +
        9735963265294864743356669767542109464399749252096320219444862871266091) * 10 ^ 70 +
        7262437246790801115271620723871142454468780816286098022253098124966807) * 10 ^ 70 +
        7958802379419712649026980594432277236846859916618025836623370759698548) * 10 ^ 70 +
        4986496774077347887508229821439400736794996046429148839942023383714335) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (327 - x)) = _
  rw [show 328 = 1 +
    327 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 327 = 32 +
      295 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 295 = 32 +
      263 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 263 = 32 +
      231 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 12 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (328 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (328 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_328 :
    recurrence4Scalar1Second.coeff 328 =
      -(((((5163088577551240 * 10 ^ 70 +
        5681162853197878874627298211083938557784325440639363761768444112352193) * 10 ^ 70 +
        2937832282357803756160003213587559726764644465443761033983735841979958) * 10 ^ 70 +
        0246765845110892441765199617480305701041746362367688539546103354881945) * 10 ^ 70 +
        1520748463010102283822773962628792410785618646236194356789461412145214) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (328 - x)) = _
  rw [show 329 = 1 +
    328 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 328 = 32 +
      296 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 296 = 32 +
      264 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 264 = 32 +
      232 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 12 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (329 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (329 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_329 :
    recurrence4Scalar1Second.coeff 329 =
      (((((1564948852488946 * 10 ^ 70 +
        5002284416799171889326670652693554830635590668414042253546631750757042) * 10 ^ 70 +
        4929955032225618770305671271169460752491280172048703408377601261092780) * 10 ^ 70 +
        7967214195604257592775016640143154641871942029017213637278812431154430) * 10 ^ 70 +
        0679219101078906535356640684667498332104539683559143429977680659293015) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (329 - x)) = _
  rw [show 330 = 1 +
    329 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 329 = 32 +
      297 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 297 = 32 +
      265 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 265 = 32 +
      233 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 12 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (330 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (330 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_330 :
    recurrence4Scalar1Second.coeff 330 =
      -(((((284068805941796 * 10 ^ 70 +
        5264892449291446989172676329973938740822210208469070259180880968683296) * 10 ^ 70 +
        3223790562027551388433424041604945852112490821978342789480749048434540) * 10 ^ 70 +
        3388246223839525152374786901326012053669748622252412334623636603962307) * 10 ^ 70 +
        5547168344594555341385629612501415512629613656392991181432224337752416) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (330 - x)) = _
  rw [show 331 = 1 +
    330 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 330 = 32 +
      298 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 298 = 32 +
      266 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 266 = 32 +
      234 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (331 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (331 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_331 :
    recurrence4Scalar1Second.coeff 331 =
      -(((((91388241949117 * 10 ^ 70 +
        1554450940794323706727639428659157305204806950936929272851125812504173) * 10 ^ 70 +
        4862896977283963510185170256357825374787037123769366912281883161330487) * 10 ^ 70 +
        0625965027391067559461608574579976542273283980080852980293000773705036) * 10 ^ 70 +
        2689547730648856894973362819140434907188494675781797064851380446493607) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (331 - x)) = _
  rw [show 332 = 1 +
    331 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 331 = 32 +
      299 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 299 = 32 +
      267 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 267 = 32 +
      235 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 12 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (332 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (332 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_332 :
    recurrence4Scalar1Second.coeff 332 =
      (((((149732367351428 * 10 ^ 70 +
        2168421658703280369210554731067995932435179601461437300551057861307918) * 10 ^ 70 +
        7171034710791322574325701494661381026879674144923662281554834711545112) * 10 ^ 70 +
        5293047365929670664909288310505508953206803478970954163282418953483757) * 10 ^ 70 +
        0074681153205448371053757214856029640160486870422953287504632068338550) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (332 - x)) = _
  rw [show 333 = 1 +
    332 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 332 = 32 +
      300 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 300 = 32 +
      268 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 268 = 32 +
      236 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 12 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (333 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (333 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_333 :
    recurrence4Scalar1Second.coeff 333 =
      -(((((118635511584991 * 10 ^ 70 +
        7143010144914365499900245153323778978547803346418695089108603930149673) * 10 ^ 70 +
        8229767145572184102777866356995989829964337753977779862669393346141814) * 10 ^ 70 +
        5381115853106473066586746850564346791916982945814163108495567947997927) * 10 ^ 70 +
        0907146541216938367505894333704296531735880659252922803501546187619863) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (333 - x)) = _
  rw [show 334 = 1 +
    333 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 333 = 32 +
      301 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 301 = 32 +
      269 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 269 = 32 +
      237 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 12 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (334 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (334 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_334 :
    recurrence4Scalar1Second.coeff 334 =
      (((((76418359381077 * 10 ^ 70 +
        2282771969627363840133985009884878474476887224410394020506571416362641) * 10 ^ 70 +
        0291873935874210028149615602663831832053166375299113070414059056317527) * 10 ^ 70 +
        3839887939828364442590321836617876728145130041214347182647442980143497) * 10 ^ 70 +
        2063319446440599405444952832625827556950817484609868181834362190553812) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (334 - x)) = _
  rw [show 335 = 1 +
    334 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 334 = 32 +
      302 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 302 = 32 +
      270 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 12 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (335 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (335 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_335 :
    recurrence4Scalar1Second.coeff 335 =
      -(((((44202133655079 * 10 ^ 70 +
        9648680232423649243850517703340018513786235627750020102733009427038929) * 10 ^ 70 +
        4864225327235392352503077942507974150369202429503396786371127343499641) * 10 ^ 70 +
        4861540444216792939981748375819848153233087719624160331888199881292293) * 10 ^ 70 +
        3703661387291229858366103315478622793100937148257487174835786107283366) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (335 - x)) = _
  rw [show 336 = 1 +
    335 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 335 = 32 +
      303 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 303 = 32 +
      271 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 12 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (336 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (336 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_336 :
    recurrence4Scalar1Second.coeff 336 =
      (((((23818808112348 * 10 ^ 70 +
        8585577665061556522541652633966761623619903240265354471986863390345173) * 10 ^ 70 +
        9796649201550444054213708151277141499948603143898098966373171995650769) * 10 ^ 70 +
        2876305057943377828449649656261432823317103806788440380621036942430399) * 10 ^ 70 +
        7886213732983233764028363066911601813724757381000347602849611228917118) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (336 - x)) = _
  rw [show 337 = 1 +
    336 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 336 = 32 +
      304 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 304 = 32 +
      272 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 12 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (337 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (337 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_337 :
    recurrence4Scalar1Second.coeff 337 =
      -(((((12166923266844 * 10 ^ 70 +
        2544804605165292462975354668601558273808465672646603850418795398289463) * 10 ^ 70 +
        6211541271948088220166951700592921280690365337060279805325916795322763) * 10 ^ 70 +
        7869237625160612983162549206807266275561576903860356852460408150517709) * 10 ^ 70 +
        0229297291386389358826426263449146274203575267761502628072482902414907) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (337 - x)) = _
  rw [show 338 = 1 +
    337 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 337 = 32 +
      305 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 305 = 32 +
      273 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 12 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (338 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (338 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_338 :
    recurrence4Scalar1Second.coeff 338 =
      (((((5946477239518 * 10 ^ 70 +
        2911699997068631514394767841056197395254464270615242368527331242916170) * 10 ^ 70 +
        3397965647259513161861102410067512335609055125511501889875697875740309) * 10 ^ 70 +
        2152753065736358235821389355148862261611547353253110863770450728846069) * 10 ^ 70 +
        4877641758063788288918101971963400355780826691940464522125919603278011) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (338 - x)) = _
  rw [show 339 = 1 +
    338 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 338 = 32 +
      306 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 306 = 32 +
      274 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 12 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (339 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (339 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_339 :
    recurrence4Scalar1Second.coeff 339 =
      -(((((2795219396364 * 10 ^ 70 +
        0881278632624474403704246151554384227696406869253103324131707460018754) * 10 ^ 70 +
        3395845613556906334465691439834480501401634635183649907979738791360381) * 10 ^ 70 +
        7451836783419799060243521888963129829416665844791895614122676046234070) * 10 ^ 70 +
        4654440512102835813675645662599037613787707700639157295618644536437433) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (339 - x)) = _
  rw [show 340 = 1 +
    339 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 339 = 32 +
      307 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 307 = 32 +
      275 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (340 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (340 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_340 :
    recurrence4Scalar1Second.coeff 340 =
      (((((1267264266607 * 10 ^ 70 +
        9478991304638747974534497562825725419986135833466057495808976217872886) * 10 ^ 70 +
        4417275313480466014976938987827229052766457626790574302098903693422247) * 10 ^ 70 +
        3151976808293958210998338367818987922950178863900341089302182089874890) * 10 ^ 70 +
        6278199877545200053074968714517544983043636407975560528714125434514912) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (340 - x)) = _
  rw [show 341 = 1 +
    340 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 340 = 32 +
      308 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 308 = 32 +
      276 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 12 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (341 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (341 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_341 :
    recurrence4Scalar1Second.coeff 341 =
      -(((((554783167830 * 10 ^ 70 +
        2090554907070674988204784863980498029547475228944248309966005458860261) * 10 ^ 70 +
        4931312398374771892486233194852841186697421079293046500153594031931141) * 10 ^ 70 +
        3026662175464122749331668900186410067524711465303214065560670576307711) * 10 ^ 70 +
        8888546009952782254964282115016506251593386268525778242709402934934771) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (341 - x)) = _
  rw [show 342 = 1 +
    341 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 341 = 32 +
      309 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 309 = 32 +
      277 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 277 = 32 +
      245 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 12 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (342 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (342 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_342 :
    recurrence4Scalar1Second.coeff 342 =
      (((((234489189767 * 10 ^ 70 +
        3568477183806866642659625589729870284423400283812997118692709139394204) * 10 ^ 70 +
        7509244081877590975208574286943831908127465695727082597888223089525443) * 10 ^ 70 +
        7820236651279140133754060929620216209683567436321000990855759218949628) * 10 ^ 70 +
        0788097248935923727642847800525241374070581440685693405659664796665852) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (342 - x)) = _
  rw [show 343 = 1 +
    342 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 342 = 32 +
      310 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 12 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (343 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (343 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_343 :
    recurrence4Scalar1Second.coeff 343 =
      -(((((95553772268 * 10 ^ 70 +
        5263849980298275536506988762816260760061322775648605076555191008836153) * 10 ^ 70 +
        6491109183393198895236431843168725765315324027126896764548552934217175) * 10 ^ 70 +
        5790363556435226806310010194525090607672764285093205476605499719573578) * 10 ^ 70 +
        7138110435121276370515908974583335572895054722283003812673364295409233) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (343 - x)) = _
  rw [show 344 = 1 +
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
    rw [show 183 = 12 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (344 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (344 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_344 :
    recurrence4Scalar1Second.coeff 344 =
      (((((37430392709 * 10 ^ 70 +
        2274880251187195290919574908926633354274191816284732199442480411442158) * 10 ^ 70 +
        8457003292626280360465826401353039557194952033916779279025539408666855) * 10 ^ 70 +
        1485888478893403426992500185423533642069640898420728986536026554620795) * 10 ^ 70 +
        9040936578825493032621110998486428814207856084117613024709426305286508) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (344 - x)) = _
  rw [show 345 = 1 +
    344 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 344 = 32 +
      312 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 312 = 32 +
      280 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 280 = 32 +
      248 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 12 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (345 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (345 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_345 :
    recurrence4Scalar1Second.coeff 345 =
      -(((((14023791235 * 10 ^ 70 +
        4565468965022275676633410937556441709073706765841502340401041602135504) * 10 ^ 70 +
        6967283154012481475374882933763281374698887446528239307939810822956949) * 10 ^ 70 +
        5431950015836006566380832050840751785309028549728684140135858546962000) * 10 ^ 70 +
        2188190665064307752623451033500774344500716408589544134360602146028137) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (345 - x)) = _
  rw [show 346 = 1 +
    345 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 345 = 32 +
      313 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 313 = 32 +
      281 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 281 = 32 +
      249 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 12 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (346 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (346 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_346 :
    recurrence4Scalar1Second.coeff 346 =
      (((((4983303542 * 10 ^ 70 +
        3697350076132061901097435397729013616198744071316082560387651466473525) * 10 ^ 70 +
        3748924767067185967391631390848913191001568708525978780331128441448708) * 10 ^ 70 +
        7026785074227459100430813666395266119753991744045127000255373397053261) * 10 ^ 70 +
        4687883873665776966778576962547977749705452439795674118993807072404070) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (346 - x)) = _
  rw [show 347 = 1 +
    346 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 346 = 32 +
      314 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 12 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (347 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (347 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_347 :
    recurrence4Scalar1Second.coeff 347 =
      -(((((1655091068 * 10 ^ 70 +
        9856990734010452171795339540954628931716011290713724887256837873706627) * 10 ^ 70 +
        9314851066276395230476531499407034844062536005909063821792789207992264) * 10 ^ 70 +
        4034396907566737093988036521536066968736789504669329350105272096669518) * 10 ^ 70 +
        4320381102672448524350899259853941027429730650624244001990961353814207) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (347 - x)) = _
  rw [show 348 = 1 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 12 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (348 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (348 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_348 :
    recurrence4Scalar1Second.coeff 348 =
      (((((499513176 * 10 ^ 70 +
        2012053249728911176476588436935987093894155844192126555029306183058560) * 10 ^ 70 +
        2988263044682779874727081396864011027799626193339033836316005313283786) * 10 ^ 70 +
        6461974610004071636454062798325892156976104172396401590795464236329433) * 10 ^ 70 +
        6585876352924479854519049620866142494132218621599762683015261247728491) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (348 - x)) = _
  rw [show 349 = 2 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 11 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (349 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (349 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_349 :
    recurrence4Scalar1Second.coeff 349 =
      -(((((128299472 * 10 ^ 70 +
        2700587375529324322248026993449919968273772122054976075226680388148525) * 10 ^ 70 +
        4434958396946960596083321020849497489336902645542172334385709001779783) * 10 ^ 70 +
        2685129443437834213955371390285585132841195502539858444576451374772846) * 10 ^ 70 +
        9505230102923452327804292633384776885318157391036302383898591448315762) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (349 - x)) = _
  rw [show 350 = 3 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 10 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (350 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (350 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_350 :
    recurrence4Scalar1Second.coeff 350 =
      (((((22265248 * 10 ^ 70 +
        6509560275657764650187438565274459792087406552224759338383614072181406) * 10 ^ 70 +
        7215669302051831154297684216788534629621529056655130048944413922370453) * 10 ^ 70 +
        9793215818983655665853392143430441123383993117919444446819571218900668) * 10 ^ 70 +
        6443278337489699153451276808050919293916624922909197654443089435703880) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (350 - x)) = _
  rw [show 351 = 4 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 9 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (351 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (351 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_351 :
    recurrence4Scalar1Second.coeff 351 =
      (((((1947680 * 10 ^ 70 +
        6844471034796808775993083411324599079771458363160516584711378400477860) * 10 ^ 70 +
        3091667224223912786028375860204082853636799872715135532300774586046771) * 10 ^ 70 +
        6965744813661161035345261308569812967244502988154377844076071871154724) * 10 ^ 70 +
        7841256995403067391721051773782433512269257421765657814435926795610872) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (351 - x)) = _
  rw [show 352 = 5 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 8 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (352 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (352 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_352 :
    recurrence4Scalar1Second.coeff 352 =
      -(((((4429647 * 10 ^ 70 +
        5995810997740324804685867986760306712771405357998200845658600227420134) * 10 ^ 70 +
        8073051016227687061970725515388163868705679558389023524598079191691469) * 10 ^ 70 +
        5762076652170489464387577896272632839998125579339361751899731947026859) * 10 ^ 70 +
        8849088582958839191595866897069143503908701196702320660747278929533858) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (352 - x)) = _
  rw [show 353 = 6 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 7 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (353 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (353 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_353 :
    recurrence4Scalar1Second.coeff 353 =
      (((((2814664 * 10 ^ 70 +
        9351169493818072339389760232301118164783988498590482328205101103283407) * 10 ^ 70 +
        9581862274113247872404466259320900457608420283964129104505872756340062) * 10 ^ 70 +
        5026600931171189700045787673289931800218481697745925312455009898286750) * 10 ^ 70 +
        1660521555572832830625397159946509606436591852790496782877817317306318) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (353 - x)) = _
  rw [show 354 = 7 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 6 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (354 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (354 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_354 :
    recurrence4Scalar1Second.coeff 354 =
      -(((((1330199 * 10 ^ 70 +
        0125073169391910126565367055095551849819376614754319164410442957320281) * 10 ^ 70 +
        1120015074651738933624778340546228750209323323813544636480936721218505) * 10 ^ 70 +
        3802312274103764514391487654145015863040634449691806492350583662911362) * 10 ^ 70 +
        9607361002619707384313721313644889522752968568778721957073912090283265) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (354 - x)) = _
  rw [show 355 = 8 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (355 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (355 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_355 :
    recurrence4Scalar1Second.coeff 355 =
      (((((516624 * 10 ^ 70 +
        9155533746037275718399554893075158133579039442336310021235568087161434) * 10 ^ 70 +
        4452671729956879610410437625941548583391441933052323725101608778936450) * 10 ^ 70 +
        3133324295909999664669335274521757636630347243913750116147991947491421) * 10 ^ 70 +
        4685540026032915995056517350741324515600887037447072767663323415471727) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (355 - x)) = _
  rw [show 356 = 9 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 4 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (356 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (356 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_356 :
    recurrence4Scalar1Second.coeff 356 =
      -(((((159891 * 10 ^ 70 +
        4989757642575665820462590664351205422497760627926398067763253175829203) * 10 ^ 70 +
        7764284959187570149990515052816695603009568681250680146716403337565200) * 10 ^ 70 +
        9924353175982807539990865185018480732962906744002642651355695855642760) * 10 ^ 70 +
        3654123309266562592418229019610156424171333125942627167611845513909955) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (356 - x)) = _
  rw [show 357 = 10 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 3 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (357 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (357 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_357 :
    recurrence4Scalar1Second.coeff 357 =
      (((((29740 * 10 ^ 70 +
        6464312404568459510017671015328373336919726901769504371411678750448739) * 10 ^ 70 +
        0640640952270998559296183728836788254155989543352447150251504897583653) * 10 ^ 70 +
        5364701752759133608668207478287469397548746117616892834351289290246430) * 10 ^ 70 +
        6668018460921442885070179022923165156026725893408753050180219480402916) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (357 - x)) = _
  rw [show 358 = 11 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 2 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (358 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (358 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_358 :
    recurrence4Scalar1Second.coeff 358 =
      (((((7139 * 10 ^ 70 +
        1271717050645764515211493995896017904340071920041515055176082529163379) * 10 ^ 70 +
        3903898402662103648633942228905852029485725612270448445178118602033685) * 10 ^ 70 +
        9683429632128117285633499822682957919586088521224856920592229839298321) * 10 ^ 70 +
        6478580791674359422632544569809766824396761900743503038644388205814413) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (358 - x)) = _
  rw [show 359 = 12 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 1 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (359 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (359 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_359 :
    recurrence4Scalar1Second.coeff 359 =
      -(((((12057 * 10 ^ 70 +
        4525084507176267044867584806187306636927523769107791400708082591490820) * 10 ^ 70 +
        7053917972954662747716529161442949858772422505855351041159578028579615) * 10 ^ 70 +
        3527519570674090431338447066792061088314752574048407918134934729191322) * 10 ^ 70 +
        0206524963913474234568744194291698915824265475677638492004945827583658) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (359 - x)) = _
  rw [show 360 = 13 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (360 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (360 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_360 :
    recurrence4Scalar1Second.coeff 360 =
      (((((8849 * 10 ^ 70 +
        9613691643608132588501886726356881639823169692938133081413832247315683) * 10 ^ 70 +
        4845749221462237696505174427125688170263838039461348870065747065067563) * 10 ^ 70 +
        4630151523106239085992840636100576232715031339535056224329715460843426) * 10 ^ 70 +
        9232952870097982372172238869007582139933186326510303894790537228435296) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (360 - x)) = _
  rw [show 361 = 14 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 31 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (361 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (361 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_361 :
    recurrence4Scalar1Second.coeff 361 =
      -(((((5155 * 10 ^ 70 +
        9436699903447168423987863187671277976355708324171756452793647432390621) * 10 ^ 70 +
        8274954470379568089237317494426490444777834800535652266385700467310831) * 10 ^ 70 +
        7720226407379515727294533637311017371755551344500112387080449531242465) * 10 ^ 70 +
        5715455079206152461947163132275396737170469653898029330112132174912686) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (361 - x)) = _
  rw [show 362 = 15 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 30 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (362 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (362 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_362 :
    recurrence4Scalar1Second.coeff 362 =
      (((((2655 * 10 ^ 70 +
        0594249025792162452622344031252007511640318942869403742435686676400881) * 10 ^ 70 +
        8490768023162478078293499119339200379833755182602129388096681211918075) * 10 ^ 70 +
        2467100454809195671673149467244049838670504147817104136741281917273503) * 10 ^ 70 +
        9677476549855533402436962459509863268787043997944722234287734239099246) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (362 - x)) = _
  rw [show 363 = 16 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 29 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (363 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (363 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_363 :
    recurrence4Scalar1Second.coeff 363 =
      -(((((1256 * 10 ^ 70 +
        4194186958647408789426341907657607973627718782798274943373598121378557) * 10 ^ 70 +
        1812348308812499559402543712657600109650206100858632980654667695489106) * 10 ^ 70 +
        7574718272170073634431260491564369983553315022026167888435349049123136) * 10 ^ 70 +
        9694629680915400228599523112088938047300731145568491499786055438097541) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (363 - x)) = _
  rw [show 364 = 17 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 28 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (364 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (364 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_364 :
    recurrence4Scalar1Second.coeff 364 =
      (((((556 * 10 ^ 70 +
        0543644527874415269170322063093725164740231050004246697620968561095600) * 10 ^ 70 +
        1888396274153950565669913973290433184215904414742117737353705862004937) * 10 ^ 70 +
        9138773063448824980906894564873229345259672517567587889978388965838808) * 10 ^ 70 +
        4361993538900823249275213131179637837456894477093054458700467467078950) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (364 - x)) = _
  rw [show 365 = 18 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 27 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (365 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (365 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_365 :
    recurrence4Scalar1Second.coeff 365 =
      -(((((232 * 10 ^ 70 +
        0349737851736920570137680972736201659515707141371943245260860216301952) * 10 ^ 70 +
        2230243799326685802127261179359771952079947081713993300172717626351230) * 10 ^ 70 +
        6328794591236587540081580127476437830686231043536538024966600728046769) * 10 ^ 70 +
        2091532147940099194103747118009062597197185568409573852898700332445480) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (365 - x)) = _
  rw [show 366 = 19 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 26 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (366 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (366 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_366 :
    recurrence4Scalar1Second.coeff 366 =
      (((((91 * 10 ^ 70 +
        5300659312116488335686017565730898141473410230385744586022712182145754) * 10 ^ 70 +
        6209598653423026808916848474044099036449836614121635130611556170921553) * 10 ^ 70 +
        2829240269832150809523049661360861805265738019647496034138820414463323) * 10 ^ 70 +
        9398367000669067995979181001554542873794341603870512838124350062925384) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (366 - x)) = _
  rw [show 367 = 20 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 25 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (367 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (367 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_367 :
    recurrence4Scalar1Second.coeff 367 =
      -(((((34 * 10 ^ 70 +
        0643297018456123372011695133445926974469179003328222107252891223268262) * 10 ^ 70 +
        9101937168848926659503926923043194021367277038812951699329375053068827) * 10 ^ 70 +
        9611441288970658160282701076958935970300688847136201374771970742410676) * 10 ^ 70 +
        0646210964528337134116881963515865756483414593891451976175692529242261) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (367 - x)) = _
  rw [show 368 = 21 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 24 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (368 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (368 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_368 :
    recurrence4Scalar1Second.coeff 368 =
      (((((11 * 10 ^ 70 +
        8735410801029890450084147373367270127267743735186475534422931675456294) * 10 ^ 70 +
        6368262208535443028041841181992388276479794064452049526927381125805661) * 10 ^ 70 +
        8350889789757631813889933459307929824110257448956675012497717670055386) * 10 ^ 70 +
        3090020666449654347537705070228341279388036409738019354321167620572229) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (368 - x)) = _
  rw [show 369 = 22 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 23 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (369 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (369 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_369 :
    recurrence4Scalar1Second.coeff 369 =
      -(((((3 * 10 ^ 70 +
        8135791832568568251882013930792865164559344901839652313493373922050634) * 10 ^ 70 +
        8921347901410939507891191447763511686637827954845999453168886942648078) * 10 ^ 70 +
        5383744522024492017803446925464768870678037784118588984108035816232693) * 10 ^ 70 +
        6412639027633982445977512592179662517249678137769746179562742285460268) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (369 - x)) = _
  rw [show 370 = 23 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 22 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (370 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (370 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_370 :
    recurrence4Scalar1Second.coeff 370 =
      (((((1 * 10 ^ 70 +
        0883378619583598393144176037189326743310443590431326211035419606506077) * 10 ^ 70 +
        5349299100886933847021881661935794157020598159063056242745154041968972) * 10 ^ 70 +
        7120740404820021219025227812506413091630713766311256214854249189018375) * 10 ^ 70 +
        9158205370105492305869532404565204277269768161087213029503426817589397) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (370 - x)) = _
  rw [show 371 = 24 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 21 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (371 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (371 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_371 :
    recurrence4Scalar1Second.coeff 371 =
      -((((2496898247036375192303984922275487301821368831778476618377730658502274 * 10 ^ 70 +
        1997762733767119303800593248072946011957001061873177846048464660317215) * 10 ^ 70 +
        7510922432008750212789315810085286470157262034430095389596154000686182) * 10 ^ 70 +
        0041709869953764184446398841447935929217444683090750770602891809252016) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (371 - x)) = _
  rw [show 372 = 25 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 20 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (372 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (372 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_372 :
    recurrence4Scalar1Second.coeff 372 =
      ((((271195554955399855903143585930520871896629991117224788419080405769387 * 10 ^ 70 +
        2258819514470835007083940849936662544678481664397561014952326936858889) * 10 ^ 70 +
        5843704732153114897873910456569046847413180371486772917361135607895646) * 10 ^ 70 +
        4375325843873028145567781967576994477035283920943744635771071774681100) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (372 - x)) = _
  rw [show 373 = 26 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 19 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (373 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (373 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_373 :
    recurrence4Scalar1Second.coeff 373 =
      ((((155243376242138007743502402813369603809405302637422835888749923721696 * 10 ^ 70 +
        4535130659415761706625157667014370651950298147645272485734488810501933) * 10 ^ 70 +
        3967039106040970718712083183372126759327611399282954304929847544216228) * 10 ^ 70 +
        5470786349308036517900640771030442397642289589864003403993229827754464) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (373 - x)) = _
  rw [show 374 = 27 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 18 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (374 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (374 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_374 :
    recurrence4Scalar1Second.coeff 374 =
      -((((149778672661499806735611808176348574172392360210217473456936714215004 * 10 ^ 70 +
        1671174358680316558555050822138993708453056562166457216800931345646652) * 10 ^ 70 +
        1459735746510717987376177512028302177085550658734847400935214082934136) * 10 ^ 70 +
        0414651827985511303075910334330437443085229067098465005483636871044601) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (374 - x)) = _
  rw [show 375 = 28 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 17 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (375 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (375 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_375 :
    recurrence4Scalar1Second.coeff 375 =
      ((((85995902457846716077693475686658398271956549645776148204526859921098 * 10 ^ 70 +
        6515896994335735193301364953524167252745382633041760215464414216874148) * 10 ^ 70 +
        8532368076821147065512532109807331648752485287550717342608868863679061) * 10 ^ 70 +
        9813229515716151963763759457654133989074414141862626246312058618910447) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (375 - x)) = _
  rw [show 376 = 29 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 16 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (376 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (376 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_376 :
    recurrence4Scalar1Second.coeff 376 =
      -((((40892128419825681008509688176414286340308327615339623688961650751046 * 10 ^ 70 +
        2327216217004501881360760763408603922339045993035291390959503665388168) * 10 ^ 70 +
        0650023848396163098819316616329396551212964392838165525344271025069054) * 10 ^ 70 +
        2215462150289389864470658923491873022590671720139267726866515926582641) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (376 - x)) = _
  rw [show 377 = 30 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 15 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (377 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (377 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_377 :
    recurrence4Scalar1Second.coeff 377 =
      ((((17398859442015155497107044273474371914039783798455435003236597334893 * 10 ^ 70 +
        9319791734215406317117673660306527662603898191235010388769036421942847) * 10 ^ 70 +
        9540706512396171291579145564771951194186050266870853633418688659899518) * 10 ^ 70 +
        5778110906673061894379824565878996159908997942680231525998169399997595) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (377 - x)) = _
  rw [show 378 = 31 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 14 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (378 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (378 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_378 :
    recurrence4Scalar1Second.coeff 378 =
      -((((6817594412262318650560289996018346846896753360225698591587574886549 * 10 ^ 70 +
        0340768301060780499352491464045630338564651138365086833639676779583033) * 10 ^ 70 +
        7507102959517449209081934800815968741177955883388879748977194813753096) * 10 ^ 70 +
        8261111309919377220473783689696486055280661747168432739607256299985266) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (378 - x)) = _
  rw [show 379 = 32 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 13 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (379 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (379 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_379 :
    recurrence4Scalar1Second.coeff 379 =
      ((((2488812741878293392346288290552315878963525546586970934274470681452 * 10 ^ 70 +
        6047688947140206997629274198938512466021001936218651976624192727113935) * 10 ^ 70 +
        8371470499848274901515717105152732225078039307106520857308932956735801) * 10 ^ 70 +
        2113187596149538142528848228896182125305093132095187834060378296580649) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (379 - x)) = _
  rw [show 380 = 33 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 12 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (380 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (380 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_380 :
    recurrence4Scalar1Second.coeff 380 =
      -((((848495656953926538025589810562134411157799312299593748391041974907 * 10 ^ 70 +
        0081971276417629994404212082707628531819646204685900313241178066100208) * 10 ^ 70 +
        4531111520725130401296508526008209502309308397780857199870815453661473) * 10 ^ 70 +
        0178726231274816389621864011881770603794008318262650568132598676446688) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (380 - x)) = _
  rw [show 381 = 34 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 11 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (381 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (381 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_381 :
    recurrence4Scalar1Second.coeff 381 =
      ((((268736159083725851040039925299793505077279180231752802230014933742 * 10 ^ 70 +
        3319383351854366574099600979567273303689140924622925411794310026905510) * 10 ^ 70 +
        2569994727389349999496309918313094765549726021377915946322649638016214) * 10 ^ 70 +
        4145264322499070436580640414316164653424454438660233327153868563468071) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (381 - x)) = _
  rw [show 382 = 35 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 10 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (382 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (382 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_382 :
    recurrence4Scalar1Second.coeff 382 =
      -((((77834989043484279630500503874620088847621235238428890266047464055 * 10 ^ 70 +
        7747194725252433054601980415109704056901395911248689133335087068716338) * 10 ^ 70 +
        0247984145566361680069701230139532933329018826842048438512634730238802) * 10 ^ 70 +
        1676177300902521457710665406856624555744297816151390562289137564765272) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (382 - x)) = _
  rw [show 383 = 36 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 9 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
