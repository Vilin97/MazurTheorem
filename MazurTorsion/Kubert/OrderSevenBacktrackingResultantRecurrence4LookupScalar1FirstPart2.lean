/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar1First_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (277 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (277 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_277 :
    recurrence4Scalar1First.coeff 277 =
      (((((494895085461110436772500413 * 10 ^ 70 +
        6981681160833280586321571978515318318337576712290015460303162715135884) * 10 ^ 70 +
        2668741191398412016162865030375266360620459911427975175304612994264522) * 10 ^ 70 +
        3237520329943979440755127430900833206707321465413604089456066340067109) * 10 ^ 70 +
        9890933335912556445522594594865050065492963918937945190061552661397905) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (277 - x)) = _
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
    rw [show 117 = 16 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (278 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (278 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_278 :
    recurrence4Scalar1First.coeff 278 =
      -(((((402892609375738616822307784 * 10 ^ 70 +
        6584670831949709320228168724588380842222201702403217284716268741690204) * 10 ^ 70 +
        7796180487296444065294158546206537395997774353443682547729524240063108) * 10 ^ 70 +
        8819796704583720547317167614083389774739899585278903224460804932978145) * 10 ^ 70 +
        8368859036085661916010762477077070997969883917166815245083187248736969) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (278 - x)) = _
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
    rw [show 118 = 16 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (279 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (279 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_279 :
    recurrence4Scalar1First.coeff 279 =
      (((((321577631412161747554452692 * 10 ^ 70 +
        6165400475697720569891972886294193174888943068008514545963885314910132) * 10 ^ 70 +
        1081631619956240915066061403140360319810841252374968619139379466913534) * 10 ^ 70 +
        0443276606391641206757893056812899829304860929527880952643629812922721) * 10 ^ 70 +
        2639471474207874723205915287995859582990615243367780570507468446284363) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (279 - x)) = _
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
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (280 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (280 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_280 :
    recurrence4Scalar1First.coeff 280 =
      -(((((251829082274363794362845829 * 10 ^ 70 +
        3180916357121323683049692340877789048423794911254929860437138143819948) * 10 ^ 70 +
        9647197719966779971993036126491247034260896383502065977897779966041717) * 10 ^ 70 +
        4360726907491449909138572189790784382851466643062081175979382812215373) * 10 ^ 70 +
        2255369677980507394982652806198184600317644908073330677939025473751259) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (280 - x)) = _
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
    rw [show 120 = 16 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (281 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (281 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_281 :
    recurrence4Scalar1First.coeff 281 =
      (((((193587157651102352017062433 * 10 ^ 70 +
        7810595351762292874610357790641851348609738511228341669064420711225410) * 10 ^ 70 +
        2385801069925137164581969928292694518723227576301980562336099506797197) * 10 ^ 70 +
        5111295520007198153562032272309860910348870876046326458701030845676449) * 10 ^ 70 +
        9626687448471081256161718260049790452838049813233366925510909600085148) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (281 - x)) = _
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
    rw [show 121 = 16 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (282 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (282 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_282 :
    recurrence4Scalar1First.coeff 282 =
      -(((((146138538944486735259304646 * 10 ^ 70 +
        8220241877362468977708191625452472230437636823027031737158289452204250) * 10 ^ 70 +
        8417991115281258424150890916334255572011376348103576199885453134810325) * 10 ^ 70 +
        3804869760472881081115469465158417786216898425623949556450550195205664) * 10 ^ 70 +
        3964639010010031949320502424686240213195749539873371702782232693448537) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (282 - x)) = _
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
    rw [show 122 = 16 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (283 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (283 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_283 :
    recurrence4Scalar1First.coeff 283 =
      (((((108364800727942824709768024 * 10 ^ 70 +
        1241265299595549236457780178437951365009346178245731373094831149348546) * 10 ^ 70 +
        3885016625222763024962032029608484358976137651607240338878553743666688) * 10 ^ 70 +
        3943632524604715956175022966099007020126893175021346023790097589023045) * 10 ^ 70 +
        8620517310633965265210589103970941182556891213647725304414331826642795) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (283 - x)) = _
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
    rw [show 123 = 16 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (284 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (284 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_284 :
    recurrence4Scalar1First.coeff 284 =
      -(((((78944671044567547080854016 * 10 ^ 70 +
        4039914145850422374294014194083914815801435592029549012907105586612146) * 10 ^ 70 +
        0462603196909674926470101783790053733179050156765591421705494417183460) * 10 ^ 70 +
        9136480999704244538562601050708168270556551237319154504564513424670062) * 10 ^ 70 +
        8982840347166596594893556121955112308341506976003215472935045796692792) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (284 - x)) = _
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
    rw [show 124 = 16 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (285 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (285 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_285 :
    recurrence4Scalar1First.coeff 285 =
      (((((56507661662498909384691820 * 10 ^ 70 +
        1113348862706831554648405634470706549142130160636757093621604579524979) * 10 ^ 70 +
        0952111780238516805422420561174032941800069256303786019038651073537511) * 10 ^ 70 +
        0759162657889888554420230370230514661891367495656839731135790779157822) * 10 ^ 70 +
        7300899997862684537729536595448900564434740504429289828854448758793157) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (285 - x)) = _
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
    rw [show 125 = 16 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (286 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (286 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_286 :
    recurrence4Scalar1First.coeff 286 =
      -(((((39741698373589595411004315 * 10 ^ 70 +
        6773292399012771264624655216908283013646912514789424342449703908947024) * 10 ^ 70 +
        4651377233520670170509079951673727728258175673299294501410377284846367) * 10 ^ 70 +
        4740574616455707328074021833345028846663444634346073199019527717153720) * 10 ^ 70 +
        6103954311411598013264361113983753941657711227350920586435016269678753) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (286 - x)) = _
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
    rw [show 126 = 16 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (287 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (287 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_287 :
    recurrence4Scalar1First.coeff 287 =
      (((((27460704564745356942929200 * 10 ^ 70 +
        3782025934735008140382031009857887020253714274845815826960413950377452) * 10 ^ 70 +
        2877712014789091375716532082271454525243569091623667573956200716042969) * 10 ^ 70 +
        1888505758807129847126650041937206057422883506494152824535882153812425) * 10 ^ 70 +
        7931840547311423879891487758171653231987804929061648727371364819265908) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (287 - x)) = _
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
    rw [show 127 = 16 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (288 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (288 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_288 :
    recurrence4Scalar1First.coeff 288 =
      -(((((18639800349729924913472983 * 10 ^ 70 +
        1488019585633064714863755252222884298910809271898008931111395046018810) * 10 ^ 70 +
        8444616731163645891151136024848999042378727450202026812373925516202678) * 10 ^ 70 +
        8900903056509611233082901911868419830776307608991502248795591349952304) * 10 ^ 70 +
        4339954648808277214445206416490671727250850422030873740777197506156014) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (288 - x)) = _
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
    rw [show 128 = 16 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (289 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (289 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_289 :
    recurrence4Scalar1First.coeff 289 =
      (((((12426188010183527642590478 * 10 ^ 70 +
        0039903990764093521935736732510397532757968920581370921790432011474485) * 10 ^ 70 +
        9372326903466517973771386119231251360765510633565194854214381288509802) * 10 ^ 70 +
        7638925752843869749390508470349522874019776042500530161382795813443114) * 10 ^ 70 +
        8380490978964987483122530781056861508564378199915673654630164671631817) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (289 - x)) = _
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
    rw [show 129 = 16 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (290 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (290 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_290 :
    recurrence4Scalar1First.coeff 290 =
      -(((((8133271692311188444688827 * 10 ^ 70 +
        2729833751813076299161265472179885046078144522995155103079317906813492) * 10 ^ 70 +
        9626494643232917480472375137617180498885588925435086409415281208456954) * 10 ^ 70 +
        5913581393832190011413259280242913995222206055151764775383269816814387) * 10 ^ 70 +
        3697543648922756449707166511748418506471560253446720912942010973509801) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (290 - x)) = _
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
    rw [show 130 = 16 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (291 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (291 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_291 :
    recurrence4Scalar1First.coeff 291 =
      (((((5224466017160060352961439 * 10 ^ 70 +
        2319271775727791504888334267941875898320751867369180609729952210317328) * 10 ^ 70 +
        3848817417047728614488889815918495696071813230975437204892192098260976) * 10 ^ 70 +
        7614902200150632526568360229573214738081422060685737151410018695793652) * 10 ^ 70 +
        6327265587049759593144520218804900378924780758323405086046567672983423) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (291 - x)) = _
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
    rw [show 131 = 16 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (292 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (292 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_292 :
    recurrence4Scalar1First.coeff 292 =
      -(((((3291793765441587661290302 * 10 ^ 70 +
        8313066624932919707981069483950074236699068084410875748868575066675203) * 10 ^ 70 +
        5628491665110680769552023472946134947545305387090996769577465886503030) * 10 ^ 70 +
        4535777727457016365522863778117992274110677237143857063532331323276761) * 10 ^ 70 +
        7648757164984744902435060080688568745360049257445566443425378766910291) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (292 - x)) = _
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
    rw [show 132 = 16 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (293 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (293 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_293 :
    recurrence4Scalar1First.coeff 293 =
      (((((2032992805351442166858686 * 10 ^ 70 +
        1868084893697887630026537016609071551201071426256133020623587793324782) * 10 ^ 70 +
        8517275079251543914928058618677143565654041723294762773035044487711137) * 10 ^ 70 +
        3510350414734121988358322136077278674982562878597534662485202649150498) * 10 ^ 70 +
        5048158490847532403739682540821547134278370438946207183172308610464176) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (293 - x)) = _
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
    rw [show 133 = 16 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (294 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (294 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_294 :
    recurrence4Scalar1First.coeff 294 =
      -(((((1229604291363470668698055 * 10 ^ 70 +
        9552805197682235682741853993266528622623950493183618579558126168464368) * 10 ^ 70 +
        8723104000643993847935681283291668195055854355897541960853564200494310) * 10 ^ 70 +
        4817500882423378742001749826660807379598501128890593794352519134775318) * 10 ^ 70 +
        0876803551644322553271379247178898464456042002140572344591160607564885) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (294 - x)) = _
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
    rw [show 134 = 16 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (295 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (295 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_295 :
    recurrence4Scalar1First.coeff 295 =
      (((((727484248721387282641918 * 10 ^ 70 +
        1670183343607696748838326048104669449430487366166391464813416175628014) * 10 ^ 70 +
        8218180256946265570068085386942988626821401429633929971209913977643286) * 10 ^ 70 +
        4231940573331485555771873996312796720292451771677213343185857203557533) * 10 ^ 70 +
        5686119656162041227291387133235022754596163623132961150775228081903518) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (295 - x)) = _
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
    rw [show 135 = 16 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (296 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (296 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_296 :
    recurrence4Scalar1First.coeff 296 =
      -(((((420398732061647471668414 * 10 ^ 70 +
        4349326778161946057150911248933505889721833774641485380039400390905199) * 10 ^ 70 +
        9391843232517610994627297642915437945513176781035475376803366255977139) * 10 ^ 70 +
        8883920303439646915540953431492919415940556434229576999721438091679015) * 10 ^ 70 +
        5571525838493471011614463616106290045671898707615925779513712110531401) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (296 - x)) = _
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
    rw [show 136 = 16 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (297 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (297 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_297 :
    recurrence4Scalar1First.coeff 297 =
      (((((236818781874342583739950 * 10 ^ 70 +
        3873949814107541913204771040420568976602820734723476219122567837458765) * 10 ^ 70 +
        4128143480637004499152151619730532020008217269815743592020809278568944) * 10 ^ 70 +
        8813253874686036274938550076585283779086703943804850310396577856415102) * 10 ^ 70 +
        6892177820698014902602764722026742603858052564598916053899374921176675) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (297 - x)) = _
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
    rw [show 137 = 16 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (298 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (298 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_298 :
    recurrence4Scalar1First.coeff 298 =
      -(((((129691606445164724574510 * 10 ^ 70 +
        4733324259104657827195262091521354064631944575902867372911104364966235) * 10 ^ 70 +
        5944396454830366484424660790928656213298132034907876988501499898123695) * 10 ^ 70 +
        1152748170452099280134229054102926658062746427635442341429974518351104) * 10 ^ 70 +
        0702790378554098503024831472968770469854016852202769116573549079890133) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (298 - x)) = _
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
    rw [show 138 = 16 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (299 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (299 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_299 :
    recurrence4Scalar1First.coeff 299 =
      (((((68784452382539713840562 * 10 ^ 70 +
        4855062449233500509449394045857396017031480120678745688232061331376024) * 10 ^ 70 +
        9723585932293729095194818332011957446781855278117991087872778913207550) * 10 ^ 70 +
        8823705036047839314208039184221856927725560585672231742825679226604400) * 10 ^ 70 +
        8753015675753772462584510757941639896572393153710757178953053304955078) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (299 - x)) = _
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
    rw [show 139 = 16 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (300 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (300 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_300 :
    recurrence4Scalar1First.coeff 300 =
      -(((((35132208926544517734297 * 10 ^ 70 +
        2604801951329116138067157300532858178035678738105621223542782672382733) * 10 ^ 70 +
        2544147439658607354339116475867784186685573494976685214270578255609884) * 10 ^ 70 +
        3921084710466837261224640886125229750672667574683108665552502419045846) * 10 ^ 70 +
        5260961602694617180446443543687799223078729047328637771085021764021596) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (300 - x)) = _
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
    rw [show 140 = 16 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (301 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (301 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_301 :
    recurrence4Scalar1First.coeff 301 =
      (((((17128682204192677849599 * 10 ^ 70 +
        1717146935087341646379322643399297476371603267075616449139456319789567) * 10 ^ 70 +
        2572770846683266053880937106172185989392902879987894712138646980161937) * 10 ^ 70 +
        9885289449466457665638508770071896865560403777563156707154273088127268) * 10 ^ 70 +
        6788063735720891502725641740519660860560464986216072539398106707937933) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (301 - x)) = _
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
    rw [show 141 = 16 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (302 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (302 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_302 :
    recurrence4Scalar1First.coeff 302 =
      -(((((7852433903617639693260 * 10 ^ 70 +
        2531306555571487512083079523417873359652782140068891749963799373791199) * 10 ^ 70 +
        6087791775255957289746106678754983119917141340587543300331826818703859) * 10 ^ 70 +
        6508260448549362892890791044728807693275152574942661545420882030852035) * 10 ^ 70 +
        8295762199663625210059385971147470598092347296300982010810825682304989) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (302 - x)) = _
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
    rw [show 142 = 16 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (303 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (303 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_303 :
    recurrence4Scalar1First.coeff 303 =
      (((((3287556933890254324688 * 10 ^ 70 +
        5250939638619517153735666621266006874593603507668844943512844075976294) * 10 ^ 70 +
        7940941700657649298884133445430322664317284781366386289695177556324112) * 10 ^ 70 +
        9103170912577416973189096220253091857624908335695689858962146353317184) * 10 ^ 70 +
        9783853748113754960644747121838343669773626781274233655447291553202723) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (303 - x)) = _
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
    rw [show 143 = 16 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (304 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (304 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_304 :
    recurrence4Scalar1First.coeff 304 =
      -(((((1172165550852049235096 * 10 ^ 70 +
        8949244291272275235028349104650349095020982219802747062695685145447150) * 10 ^ 70 +
        1213938524336740415768348404599322345761471948736193951627858474012310) * 10 ^ 70 +
        3028934242274470448381304815086448793908641679979047738255626678197474) * 10 ^ 70 +
        6928061024581747442243145932529363880347334409796142680448428292739289) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (304 - x)) = _
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
    rw [show 144 = 16 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (305 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (305 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_305 :
    recurrence4Scalar1First.coeff 305 =
      (((((273591906598088972181 * 10 ^ 70 +
        8127258499081050822750294823892963300777685639407092138825632695584702) * 10 ^ 70 +
        9988328928483022500686112853480661624122917572987967427935367307159492) * 10 ^ 70 +
        1828171192992657722946596888514395670051891027331391898194504116103375) * 10 ^ 70 +
        0126493908048420227994570209993654132914742182663341799863567378842211) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (305 - x)) = _
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
    rw [show 145 = 16 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (306 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (306 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_306 :
    recurrence4Scalar1First.coeff 306 =
      (((((55035990281368035692 * 10 ^ 70 +
        4637054711165084644653878254712762226868836914339235087604329833005497) * 10 ^ 70 +
        9750217662835379047888444280581987461525313895024457542480105699655700) * 10 ^ 70 +
        1689641843986715875854665432522444901578864482350307543408091690862330) * 10 ^ 70 +
        8888121724766241141908505947803414307935455278884844927613409695624505) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (306 - x)) = _
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
    rw [show 146 = 16 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (307 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (307 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_307 :
    recurrence4Scalar1First.coeff 307 =
      -(((((138160341174344004536 * 10 ^ 70 +
        8821030082643410701604637367776756892389338156450361177093297430541521) * 10 ^ 70 +
        7286272679208839664682819207876481026480246915545962801654261716249127) * 10 ^ 70 +
        3132447326290021119774535766811646741555850982283970677776552732086142) * 10 ^ 70 +
        0454895567674346664688664451861377412347238174680726382716189957126872) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (307 - x)) = _
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
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (308 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (308 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_308 :
    recurrence4Scalar1First.coeff 308 =
      (((((129377770981141100202 * 10 ^ 70 +
        3249597912290970866762716637922162918787459297074070250314035809030309) * 10 ^ 70 +
        0258809098008756321107432189489668276465270897986617835178697282103224) * 10 ^ 70 +
        6329187084129428049986331370188939057424199863225097759330278987164404) * 10 ^ 70 +
        2514770368037974393179147243622191719951443803777850766806892629929698) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (308 - x)) = _
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
    rw [show 148 = 16 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (309 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (309 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_309 :
    recurrence4Scalar1First.coeff 309 =
      -(((((95751552986380773744 * 10 ^ 70 +
        3297523895073557694031839041893942040208186176374546480170101535791709) * 10 ^ 70 +
        6449106846656924473719190271571811419794437643926667087587305047527111) * 10 ^ 70 +
        1896901939421548264645742328046621160669918597431834722726357344502312) * 10 ^ 70 +
        6051027545192160774286334876233855328681127281284982031161686649617802) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (309 - x)) = _
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
    rw [show 149 = 16 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (310 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (310 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_310 :
    recurrence4Scalar1First.coeff 310 =
      (((((62937714735933197935 * 10 ^ 70 +
        2065178565637559040103806988138531994756313787809280156530683704712678) * 10 ^ 70 +
        8917141545863821102877395531283931455012339127432627622999456370964452) * 10 ^ 70 +
        5962545347803549034559462166844127561197131582696526914254128645489405) * 10 ^ 70 +
        4924473817454140975008551628104859875744879000839122651398825276458069) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (310 - x)) = _
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
    rw [show 150 = 16 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (311 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (311 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_311 :
    recurrence4Scalar1First.coeff 311 =
      -(((((38272624743212245872 * 10 ^ 70 +
        2091475687352429297952655809354053908165201000564513654508519064619029) * 10 ^ 70 +
        3360885834768837178310970669297297556388968105291931201504443110023111) * 10 ^ 70 +
        6140975995575629484158903854435079268100122525551467437542756217369977) * 10 ^ 70 +
        5283882119029724025844089701160501209427885668444962246323185674374831) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (311 - x)) = _
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
    rw [show 151 = 16 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (312 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (312 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_312 :
    recurrence4Scalar1First.coeff 312 =
      (((((21940382852405620964 * 10 ^ 70 +
        8992969914421434450994053618169167576585938341814701137441579482161601) * 10 ^ 70 +
        3232102015914282572519445356452297627806767032384494540779831377458877) * 10 ^ 70 +
        2983412729903812316411977040359635773152946765979243418901624357543587) * 10 ^ 70 +
        5544668387542895535730691811429251760274968929029836848091996449489166) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (312 - x)) = _
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
    rw [show 152 = 16 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (313 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (313 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_313 :
    recurrence4Scalar1First.coeff 313 =
      -(((((11978055072600289459 * 10 ^ 70 +
        4974772712731196339482842964655167611737499332924920321306115909622517) * 10 ^ 70 +
        1268309360068932069659481705720827711028307499748146235210863014833197) * 10 ^ 70 +
        3247476662205525465584837093646640170150186201070749057053920240321273) * 10 ^ 70 +
        9623053147196889516905070966413020312783735757397510956082412216033435) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (313 - x)) = _
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
    rw [show 153 = 16 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (314 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (314 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_314 :
    recurrence4Scalar1First.coeff 314 =
      (((((6267654556832976635 * 10 ^ 70 +
        8201888335667003142622314710900670694062091294243090974356809413669011) * 10 ^ 70 +
        0873841441462778638311969875138056588303895336062609237968956700300210) * 10 ^ 70 +
        1658316973368707460572903406144920421107090986819078559770221118274886) * 10 ^ 70 +
        0640214556863796961939468618638892996238236919243668331074199524509314) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (314 - x)) = _
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
    rw [show 154 = 16 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (315 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (315 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_315 :
    recurrence4Scalar1First.coeff 315 =
      -(((((3160196217767053916 * 10 ^ 70 +
        6455891062289878164339461825489808235700663276730511972934594536298292) * 10 ^ 70 +
        8687319360557346351942291595515299570526581672493365185881566017628805) * 10 ^ 70 +
        2891467491052061945842575411917913296239493938362052124462029383057026) * 10 ^ 70 +
        0483872944550505874868128012199760898656122889029680507455224805579469) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (315 - x)) = _
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
    rw [show 155 = 16 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (316 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (316 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_316 :
    recurrence4Scalar1First.coeff 316 =
      (((((1545312600121191278 * 10 ^ 70 +
        1596604219874479313903592610998976350892073738823225427295983274695310) * 10 ^ 70 +
        8274926670136270536933776562944724516575993315653432761011617233762619) * 10 ^ 70 +
        2263663713519044362862504125533741662064359503787284233832301613029233) * 10 ^ 70 +
        3771414751312944303677075538803229837267092150685110329969866600148360) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (316 - x)) = _
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
    rw [show 156 = 16 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (317 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (317 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_317 :
    recurrence4Scalar1First.coeff 317 =
      -(((((740437024226832945 * 10 ^ 70 +
        8173576923543610307128082759007465913312449779682127061444723348603844) * 10 ^ 70 +
        7242172306384846359398083187813584080144476714142433379784972620763703) * 10 ^ 70 +
        8054255433140286314722114195197226590673803981558907582385916514081840) * 10 ^ 70 +
        5285966526894454273378429783404554600608410988416769805726373034566075) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (317 - x)) = _
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
    rw [show 157 = 16 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (318 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (318 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_318 :
    recurrence4Scalar1First.coeff 318 =
      (((((353816976106011423 * 10 ^ 70 +
        9230861069979201271724363448365703278261564636056798864846206114852881) * 10 ^ 70 +
        6801907404162641838932178623783906530643284802863717469441329583796632) * 10 ^ 70 +
        4098220930838645473425822107877609129553775178918494972674950125854938) * 10 ^ 70 +
        1700004711555105454564180457928840182351629625681311424322299559052381) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (318 - x)) = _
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
    rw [show 158 = 16 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (319 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (319 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_319 :
    recurrence4Scalar1First.coeff 319 =
      -(((((173312727003863567 * 10 ^ 70 +
        7334691278998450648714493369338874443895967919121929280835567292557976) * 10 ^ 70 +
        3457108511200264417588127173701345668308300975543651407216981383520930) * 10 ^ 70 +
        5825197836903010110420157327169984992514234118885748696369914214680291) * 10 ^ 70 +
        8880750896687225286676862297137256278090692016075789951216971329765932) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (319 - x)) = _
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
    rw [show 159 = 16 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (320 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (320 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_320 :
    recurrence4Scalar1First.coeff 320 =
      (((((90022070901905791 * 10 ^ 70 +
        2037375791995011849414752168607126626689701409341721386583743754959367) * 10 ^ 70 +
        9433933559635214883010596217421665339491238349635628568489517954122006) * 10 ^ 70 +
        6381992803394570560131270283712040128511478937250322354857962603181018) * 10 ^ 70 +
        6792980250875089458562328207420890215479531141484085624619123109323241) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (320 - x)) = _
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
    rw [show 160 = 16 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (321 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (321 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_321 :
    recurrence4Scalar1First.coeff 321 =
      -(((((50859743203692440 * 10 ^ 70 +
        1142627186739829513194541690011434240414078616942002522313564234080169) * 10 ^ 70 +
        3411470767757455822026423288955904261622836038667500902873909462970580) * 10 ^ 70 +
        7504576970366346381463753729505393581741131961742605606937953981042538) * 10 ^ 70 +
        7822116475818099924437962048402932203380124935169544963922365057680268) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (321 - x)) = _
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
    rw [show 161 = 16 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (322 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (322 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_322 :
    recurrence4Scalar1First.coeff 322 =
      (((((31245996391177335 * 10 ^ 70 +
        0296148730981567041252441179064998864443280768025541431631563499445874) * 10 ^ 70 +
        5366384233969262930379106177275309530698230428483117747660049548211942) * 10 ^ 70 +
        2861766363524793322120843349011189721603124142735522017815687339306183) * 10 ^ 70 +
        6023169941169715254030785449491448117638245600373524900396124370048264) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (322 - x)) = _
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
    rw [show 162 = 16 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (323 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (323 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_323 :
    recurrence4Scalar1First.coeff 323 =
      -(((((20354122154047834 * 10 ^ 70 +
        3923525500052694774892914782109437154646191636847670289776518999764735) * 10 ^ 70 +
        1209769503233076214938620786173346394107716138159694949313987947546162) * 10 ^ 70 +
        2121477759904964693357261991274082922347293968478524655326967620935966) * 10 ^ 70 +
        4651712037767666735131712533403414390874658512350377948224015526626823) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (323 - x)) = _
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
    rw [show 163 = 16 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (324 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (324 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_324 :
    recurrence4Scalar1First.coeff 324 =
      (((((13609886948228534 * 10 ^ 70 +
        1563462045175939403233585740046583278361777377295864785105744418130911) * 10 ^ 70 +
        0423727574021612154838758265666975552815694064331091319777442200877388) * 10 ^ 70 +
        2964167260075037793695003461366149864502273228930570842385653411612212) * 10 ^ 70 +
        1629513695746965465277232955513419833291720782972874133592121875603352) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (324 - x)) = _
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
    rw [show 164 = 16 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (325 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (325 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_325 :
    recurrence4Scalar1First.coeff 325 =
      -(((((9106995603037200 * 10 ^ 70 +
        7802961080874161357565714926244393643072069991828264938324935110305041) * 10 ^ 70 +
        3027831323509296027516727678991049067001400560677294840596861720816895) * 10 ^ 70 +
        7109982872263968719108604882403597848605693429927584630288866696850922) * 10 ^ 70 +
        6002155852447514966957164862178202540243562619633016845287821033268997) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (325 - x)) = _
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
    rw [show 165 = 16 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (326 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (326 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_326 :
    recurrence4Scalar1First.coeff 326 =
      (((((6006280566716482 * 10 ^ 70 +
        2109383769216357242898271688628929061841909023467796140803216219689993) * 10 ^ 70 +
        6921715767284852235246684998562151972969737737566180159743388334466293) * 10 ^ 70 +
        2628429893194787196383047853452536070829456091500502571067614831696050) * 10 ^ 70 +
        2075794131173158789000966798772770334388528957573170610961057378722826) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (326 - x)) = _
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
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (327 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (327 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_327 :
    recurrence4Scalar1First.coeff 327 =
      -(((((3874805717830128 * 10 ^ 70 +
        7696680732115857681489414247362258509093415030997018421016340016292689) * 10 ^ 70 +
        9336357252595708985538097718292090696537571797094970970634921724764557) * 10 ^ 70 +
        9857616248486405268905097120704846017971910025961689986138880434453268) * 10 ^ 70 +
        8755747727853126718060803251112443525703076344776508410432249906705908) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (327 - x)) = _
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
    rw [show 167 = 16 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (328 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (328 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_328 :
    recurrence4Scalar1First.coeff 328 =
      (((((2437632100588591 * 10 ^ 70 +
        0617144594759577411108317146182642814373768920760881600034293440261890) * 10 ^ 70 +
        2698967371817749905923651330863493633998633186258113406431776571512539) * 10 ^ 70 +
        0184457913637913400772149207241045121792218392665846324024761157265969) * 10 ^ 70 +
        1665740363693318613254073871151549442479683925074515394888364029917520) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (328 - x)) = _
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
    rw [show 168 = 16 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (329 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (329 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_329 :
    recurrence4Scalar1First.coeff 329 =
      -(((((1494309320149141 * 10 ^ 70 +
        6100087456165563725207678426239976046745088553128839511480238875390284) * 10 ^ 70 +
        6258949234407736694947142638164734646979506940565981002127930720582601) * 10 ^ 70 +
        4246396278422904757052726368887748041231444120680817746883515068689375) * 10 ^ 70 +
        4583032000897072306287868999431133892992216429502136962150498846417829) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (329 - x)) = _
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
    rw [show 169 = 16 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (330 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (330 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_330 :
    recurrence4Scalar1First.coeff 330 =
      (((((892959632503004 * 10 ^ 70 +
        9909211703986790806167155495563839833685435337031286128668607487975064) * 10 ^ 70 +
        7030394691955019857357817856527304228990221853089078587320268577155564) * 10 ^ 70 +
        5685582590779067280518987905918295544159564755770661262420515994955039) * 10 ^ 70 +
        4147424677865491426679184791229696642769321545874652979306727898699368) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (330 - x)) = _
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
    rw [show 170 = 16 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (331 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (331 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_331 :
    recurrence4Scalar1First.coeff 331 =
      -(((((520607061361205 * 10 ^ 70 +
        0720031965399956741908307535046814462650323511291830696338021932000897) * 10 ^ 70 +
        2473266656851413026643504428317283699731503246811128896368540832292247) * 10 ^ 70 +
        1539394712879539010394490961674152380115484597543081452636870674910724) * 10 ^ 70 +
        8068710672685218667311233994027349475363597848632793488621259734909832) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (331 - x)) = _
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
    rw [show 171 = 16 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (332 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (332 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_332 :
    recurrence4Scalar1First.coeff 332 =
      (((((296418398346675 * 10 ^ 70 +
        8685580342182895797292725773614760579711394646166832419767164856127831) * 10 ^ 70 +
        0889151378912136826035704699662589222328333998129147404796572544411472) * 10 ^ 70 +
        4092142569860651021875494491616908456424018192036214250138225023642907) * 10 ^ 70 +
        8630278620060895085725221937441297233148500855247887559102972876201210) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (332 - x)) = _
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
    rw [show 172 = 16 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (333 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (333 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_333 :
    recurrence4Scalar1First.coeff 333 =
      -(((((164983923058507 * 10 ^ 70 +
        2602963453857639592565362929050682630622294428567234851717095147410308) * 10 ^ 70 +
        0723015249497384958390373248191027885750580846504764926710536579199928) * 10 ^ 70 +
        5946077058551886162445777929118015616216684450420960587681380449405172) * 10 ^ 70 +
        4606107876571410692878834580543630489231508076557691176000168441387412) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (333 - x)) = _
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
    rw [show 173 = 16 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (334 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (334 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_334 :
    recurrence4Scalar1First.coeff 334 =
      (((((89847991528526 * 10 ^ 70 +
        5802494215843710171505189759532468852986068702886766399696514214954990) * 10 ^ 70 +
        8781860962603329644744072603503344019180792541718473916877032392355540) * 10 ^ 70 +
        9344611179226387080573049635499591362443409586136332321575865722885867) * 10 ^ 70 +
        2642674814007841591003295921932914068429681807873452562688948430626424) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (334 - x)) = _
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
    rw [show 174 = 16 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (335 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (335 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_335 :
    recurrence4Scalar1First.coeff 335 =
      -(((((47912322805909 * 10 ^ 70 +
        9959868657346774083961508521260080944513795265550603671609570338162103) * 10 ^ 70 +
        5783621853647267080051034286962991310722983357798868267962030847622103) * 10 ^ 70 +
        9630453268588707671403457686495778544662084118328733870230960721024583) * 10 ^ 70 +
        9983033906134651967982748714702042895887432538906246049194740529378603) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (335 - x)) = _
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
    rw [show 175 = 16 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (336 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (336 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_336 :
    recurrence4Scalar1First.coeff 336 =
      (((((25035163180287 * 10 ^ 70 +
        7134125201219897880768058656314873300547846748286102023735100422015105) * 10 ^ 70 +
        7072175119973423347647031751348178813373695611699184753431614296090044) * 10 ^ 70 +
        4388035159134906258991314838416716750682615548628199668613850425801423) * 10 ^ 70 +
        4217864951581813890580486440031596322934294189971977915150661546894042) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (336 - x)) = _
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
    rw [show 176 = 16 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (337 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (337 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_337 :
    recurrence4Scalar1First.coeff 337 =
      -(((((12825142567348 * 10 ^ 70 +
        3771431913589638908105713403275840339049856693342783889243603778301434) * 10 ^ 70 +
        8038722195847517365434256349082435325740030548656733942918175556756473) * 10 ^ 70 +
        8136416603841086084699739073914389360032746457102841778894682066933590) * 10 ^ 70 +
        1458631584859403800635544175460911973658621541477342903738804351615424) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (337 - x)) = _
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
    rw [show 177 = 16 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (338 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (338 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_338 :
    recurrence4Scalar1First.coeff 338 =
      (((((6444391532605 * 10 ^ 70 +
        2685941389994674316553041214482318895012539500713989930132209634099236) * 10 ^ 70 +
        8929485671310532998272618734291023056996816657025346637062868735129547) * 10 ^ 70 +
        7167729966579085297730387106717367493917706416417736406592527151817209) * 10 ^ 70 +
        7396554754590024370590590862810918758688836078560130630016515232742432) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (338 - x)) = _
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
    rw [show 178 = 16 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (339 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (339 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_339 :
    recurrence4Scalar1First.coeff 339 =
      -(((((3177368264022 * 10 ^ 70 +
        6364466180882550629119027198307774348661582427616228248267415049942228) * 10 ^ 70 +
        9911237525333681257324686251207174921011159663011409089203752606067978) * 10 ^ 70 +
        5733659645764503885707055305201103644999482925417743110719183514633779) * 10 ^ 70 +
        8220155210499187169140475310896434987489649619199181347584714160290581) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (339 - x)) = _
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
    rw [show 179 = 16 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (340 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (340 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_340 :
    recurrence4Scalar1First.coeff 340 =
      (((((1537583902812 * 10 ^ 70 +
        1507187282857434718217518397347067444919000409452210647190830940138367) * 10 ^ 70 +
        0352538969641034010674799741465284303494503023715971054714821755274415) * 10 ^ 70 +
        3908259915903411739498293403194095222987391546278033210409052659827004) * 10 ^ 70 +
        9413352377788033952063853586601690827445048795638856526754659412637083) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (340 - x)) = _
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
    rw [show 180 = 16 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (341 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (341 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_341 :
    recurrence4Scalar1First.coeff 341 =
      -(((((730431708582 * 10 ^ 70 +
        9956130790311222137386264847594932596593221633056423238924446745801009) * 10 ^ 70 +
        2826472329254836412607174454818095034198248407610803182518771300439792) * 10 ^ 70 +
        0667703545132801186348461740602071064779288630465814326163994057619181) * 10 ^ 70 +
        5616838497162570030977371546330493610404550912280243388884095271124705) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (341 - x)) = _
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
    rw [show 181 = 16 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (342 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (342 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_342 :
    recurrence4Scalar1First.coeff 342 =
      (((((340674386809 * 10 ^ 70 +
        8821805697756992961610500276292818259955766989816958161428723384084832) * 10 ^ 70 +
        4062994278381195584503902396247843348622571637387545518187639043093635) * 10 ^ 70 +
        7823708020125228280939421103843055729696091261921936934619498648431222) * 10 ^ 70 +
        9487748382986348556617867949030074512374944755704001350481277346359964) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (342 - x)) = _
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
    rw [show 182 = 16 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (343 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (343 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_343 :
    recurrence4Scalar1First.coeff 343 =
      -(((((156003348475 * 10 ^ 70 +
        0196736352184092452283644987984964636568390438809720541786187452885091) * 10 ^ 70 +
        7066213932622104191814276554391003655564503047731307695536293224121593) * 10 ^ 70 +
        9552289391424450951404780949963687449689622822721093075342419534916286) * 10 ^ 70 +
        3995401865097628192535255852847698275552157198523625001515400530681495) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (343 - x)) = _
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
    rw [show 183 = 16 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (344 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (344 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_344 :
    recurrence4Scalar1First.coeff 344 =
      (((((70136353208 * 10 ^ 70 +
        4013312222524135978056709718389278990515950172112621404011503542226458) * 10 ^ 70 +
        4993787560345476509157921694442076281040490089871418925924415078168402) * 10 ^ 70 +
        8395126202379110561707311379329939240751564141458526282881903261601563) * 10 ^ 70 +
        1907382269033018607401718682598409498061722037451680523563929899331987) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (344 - x)) = _
  rw [show 345 = 2 +
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
    rw [show 183 = 15 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (345 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (345 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_345 :
    recurrence4Scalar1First.coeff 345 =
      -(((((30953451309 * 10 ^ 70 +
        7113729956522345468477819410709466278383257450474076514656341951020625) * 10 ^ 70 +
        3207427231771461318687885233896529266014029593839933831216680922316770) * 10 ^ 70 +
        4856455672288439279847858035275305408278868843541852208632140852546808) * 10 ^ 70 +
        1654563986693770700675760834354642046264481445640474487855503357318084) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (345 - x)) = _
  rw [show 346 = 3 +
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
    rw [show 183 = 14 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (346 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (346 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_346 :
    recurrence4Scalar1First.coeff 346 =
      (((((13406922525 * 10 ^ 70 +
        1539062937107066068913298212590562013566565899643516622548876416918670) * 10 ^ 70 +
        5951619005388620364613876699309507951926666938892092397736800785628722) * 10 ^ 70 +
        1052038519379592379787710229432281188602567441597023787832092351851911) * 10 ^ 70 +
        9291044129008407232988791922342623446405879853307987082632693870037969) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (346 - x)) = _
  rw [show 347 = 4 +
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
    rw [show 183 = 13 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (347 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (347 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_347 :
    recurrence4Scalar1First.coeff 347 =
      -(((((5697005138 * 10 ^ 70 +
        7302841675957798479026378251429984375836554496412020554394361121141582) * 10 ^ 70 +
        0624180103297904106736753513736763485642377347547838288311434792434515) * 10 ^ 70 +
        1845111835307473310334221808696695032513486438011728537786342469629892) * 10 ^ 70 +
        4471109339148950018186531142608558548916515222872183867081823705752251) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (347 - x)) = _
  rw [show 348 = 5 +
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
  rw [recurrence4Scalar1First_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (348 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (348 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_348 :
    recurrence4Scalar1First.coeff 348 =
      (((((2373752054 * 10 ^ 70 +
        0931494082818702327465068879428613929580844858340522425987838047333260) * 10 ^ 70 +
        2195343345613815435239386880239383231646814024353187788346445107785953) * 10 ^ 70 +
        3712813791328561444333753316322145187667721309391529912672656643002703) * 10 ^ 70 +
        6918730710991833482243577390527175338446700585360713698506258234884007) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (348 - x)) = _
  rw [show 349 = 6 +
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
    rw [show 183 = 11 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (349 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (349 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_349 :
    recurrence4Scalar1First.coeff 349 =
      -(((((969114555 * 10 ^ 70 +
        2978621852622749767559541054206757362344594782814233213615772685087179) * 10 ^ 70 +
        7102157576060580075026459365283773353842174246161513291282622804535144) * 10 ^ 70 +
        1693703606792783783633548937412066492363611098034920912242752082852693) * 10 ^ 70 +
        7184962747175547008181257597652082256549943443638012632011852081019566) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (349 - x)) = _
  rw [show 350 = 7 +
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
    rw [show 183 = 10 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (350 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (350 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_350 :
    recurrence4Scalar1First.coeff 350 =
      (((((387269661 * 10 ^ 70 +
        4074146280988252347831070408300322383730000169659750834846605048384195) * 10 ^ 70 +
        0214734832917397232864748119150054932739748485908567700406789175321635) * 10 ^ 70 +
        2246933020686581372915389643836419483536658471375249488599812008776975) * 10 ^ 70 +
        6510116175348067493096669033978228903252618750570866848982122956875986) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (350 - x)) = _
  rw [show 351 = 8 +
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
    rw [show 183 = 9 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (351 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (351 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_351 :
    recurrence4Scalar1First.coeff 351 =
      -(((((151253192 * 10 ^ 70 +
        5875604385660843250944419611218714354330205763385988316468452654457655) * 10 ^ 70 +
        8453482303145117780453636673324738867824441802756734311543008872010119) * 10 ^ 70 +
        6919466158195752897245636548233779612908230768965222713322776680880413) * 10 ^ 70 +
        6992787308392587030121526781378992656029377550133731469561141164824481) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (351 - x)) = _
  rw [show 352 = 9 +
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
    rw [show 183 = 8 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (352 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (352 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_352 :
    recurrence4Scalar1First.coeff 352 =
      (((((57611355 * 10 ^ 70 +
        3061536085009074624662389507335225874473063489797436345613822194263537) * 10 ^ 70 +
        0847160646361089362517656553744623826219106940108330254764268315785740) * 10 ^ 70 +
        5434448572884262195460872139896541865257277856430787711544230491294677) * 10 ^ 70 +
        5879593821810343494827778829903283531957856274254259589290495569773516) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (352 - x)) = _
  rw [show 353 = 10 +
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
    rw [show 183 = 7 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (353 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (353 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_353 :
    recurrence4Scalar1First.coeff 353 =
      -(((((21331238 * 10 ^ 70 +
        5330515621612540574745347566457418843330014629644569902001201609971105) * 10 ^ 70 +
        5640765221715441906746945828703955884922032127309323130267333788963907) * 10 ^ 70 +
        1941956937679268515338908468832769298235760675105826158550827333084468) * 10 ^ 70 +
        0376255698242027116012371801074909618271489166998780499247604608817752) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (353 - x)) = _
  rw [show 354 = 11 +
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
    rw [show 183 = 6 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (354 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (354 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_354 :
    recurrence4Scalar1First.coeff 354 =
      (((((7639003 * 10 ^ 70 +
        1355175555826894661477224774911999366701909379969959470017286421313637) * 10 ^ 70 +
        9182831539305916292173041581978795716749742389713062011572385383436919) * 10 ^ 70 +
        2795728837885502286951591927486837483684793202805488109224030340989672) * 10 ^ 70 +
        0336756494072717649177116525700549125396738861716495239185865938361117) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (354 - x)) = _
  rw [show 355 = 12 +
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
    rw [show 183 = 5 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (355 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (355 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_355 :
    recurrence4Scalar1First.coeff 355 =
      -(((((2624038 * 10 ^ 70 +
        1694708556623681335925585946356433937429102661472106041308469375921181) * 10 ^ 70 +
        0620947290903900721642718071918272526504143189733177476082753559420039) * 10 ^ 70 +
        9394110108638011648987510453939958824882333670400514652918836695284567) * 10 ^ 70 +
        1275343783973577658823230416668564124612398040686828880942952572056876) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (355 - x)) = _
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
    rhs
    rw [show 183 = 4 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
