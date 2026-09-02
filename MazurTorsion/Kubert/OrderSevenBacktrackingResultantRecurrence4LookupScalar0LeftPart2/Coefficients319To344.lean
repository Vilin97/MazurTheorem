/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_1
  recurrence4A0_coeff_10
  recurrence4A0_coeff_100
  recurrence4A0_coeff_101
  recurrence4A0_coeff_102
  recurrence4A0_coeff_103
  recurrence4A0_coeff_104
  recurrence4A0_coeff_105
  recurrence4A0_coeff_106
  recurrence4A0_coeff_107
  recurrence4A0_coeff_108
  recurrence4A0_coeff_109
  recurrence4A0_coeff_11
  recurrence4A0_coeff_110
  recurrence4A0_coeff_111
  recurrence4A0_coeff_112
  recurrence4A0_coeff_113
  recurrence4A0_coeff_114
  recurrence4A0_coeff_115
  recurrence4A0_coeff_116
  recurrence4A0_coeff_117
  recurrence4A0_coeff_118
  recurrence4A0_coeff_119
  recurrence4A0_coeff_12
  recurrence4A0_coeff_120
  recurrence4A0_coeff_121
  recurrence4A0_coeff_122
  recurrence4A0_coeff_123
  recurrence4A0_coeff_124
  recurrence4A0_coeff_125
  recurrence4A0_coeff_126
  recurrence4A0_coeff_127
  recurrence4A0_coeff_128
  recurrence4A0_coeff_129
  recurrence4A0_coeff_13
  recurrence4A0_coeff_130
  recurrence4A0_coeff_131
  recurrence4A0_coeff_132
  recurrence4A0_coeff_133
  recurrence4A0_coeff_134
  recurrence4A0_coeff_135
  recurrence4A0_coeff_136
  recurrence4A0_coeff_137
  recurrence4A0_coeff_138
  recurrence4A0_coeff_139
  recurrence4A0_coeff_14
  recurrence4A0_coeff_140
  recurrence4A0_coeff_141
  recurrence4A0_coeff_142
  recurrence4A0_coeff_143
  recurrence4A0_coeff_144
  recurrence4A0_coeff_145
  recurrence4A0_coeff_146
  recurrence4A0_coeff_147
  recurrence4A0_coeff_148
  recurrence4A0_coeff_149
  recurrence4A0_coeff_15
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156

attribute [local simp]
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_16
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_163
  recurrence4A0_coeff_164
  recurrence4A0_coeff_165
  recurrence4A0_coeff_166
  recurrence4A0_coeff_167
  recurrence4A0_coeff_168
  recurrence4A0_coeff_169
  recurrence4A0_coeff_17
  recurrence4A0_coeff_170
  recurrence4A0_coeff_171
  recurrence4A0_coeff_172
  recurrence4A0_coeff_173
  recurrence4A0_coeff_174
  recurrence4A0_coeff_175
  recurrence4A0_coeff_176
  recurrence4A0_coeff_177
  recurrence4A0_coeff_178
  recurrence4A0_coeff_179
  recurrence4A0_coeff_18
  recurrence4A0_coeff_180
  recurrence4A0_coeff_181
  recurrence4A0_coeff_182
  recurrence4A0_coeff_183
  recurrence4A0_coeff_184
  recurrence4A0_coeff_185
  recurrence4A0_coeff_186
  recurrence4A0_coeff_187
  recurrence4A0_coeff_188
  recurrence4A0_coeff_189
  recurrence4A0_coeff_19
  recurrence4A0_coeff_190
  recurrence4A0_coeff_191
  recurrence4A0_coeff_192
  recurrence4A0_coeff_193
  recurrence4A0_coeff_194
  recurrence4A0_coeff_2
  recurrence4A0_coeff_20
  recurrence4A0_coeff_21
  recurrence4A0_coeff_22
  recurrence4A0_coeff_23
  recurrence4A0_coeff_24
  recurrence4A0_coeff_25
  recurrence4A0_coeff_26
  recurrence4A0_coeff_27
  recurrence4A0_coeff_28
  recurrence4A0_coeff_29
  recurrence4A0_coeff_3
  recurrence4A0_coeff_30
  recurrence4A0_coeff_31
  recurrence4A0_coeff_32
  recurrence4A0_coeff_33
  recurrence4A0_coeff_34
  recurrence4A0_coeff_35
  recurrence4A0_coeff_36
  recurrence4A0_coeff_37
  recurrence4A0_coeff_38
  recurrence4A0_coeff_39

attribute [local simp]
  recurrence4A0_coeff_4
  recurrence4A0_coeff_40
  recurrence4A0_coeff_41
  recurrence4A0_coeff_42
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
  recurrence4A0_coeff_5
  recurrence4A0_coeff_50
  recurrence4A0_coeff_51
  recurrence4A0_coeff_52
  recurrence4A0_coeff_53
  recurrence4A0_coeff_54
  recurrence4A0_coeff_55
  recurrence4A0_coeff_56
  recurrence4A0_coeff_57
  recurrence4A0_coeff_58
  recurrence4A0_coeff_59
  recurrence4A0_coeff_6
  recurrence4A0_coeff_60
  recurrence4A0_coeff_61
  recurrence4A0_coeff_62
  recurrence4A0_coeff_63
  recurrence4A0_coeff_64
  recurrence4A0_coeff_65
  recurrence4A0_coeff_66
  recurrence4A0_coeff_67
  recurrence4A0_coeff_68
  recurrence4A0_coeff_69
  recurrence4A0_coeff_7
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
  recurrence4A0_coeff_8
  recurrence4A0_coeff_80
  recurrence4A0_coeff_81
  recurrence4A0_coeff_82
  recurrence4A0_coeff_83
  recurrence4A0_coeff_84
  recurrence4A0_coeff_85
  recurrence4A0_coeff_86
  recurrence4A0_coeff_87
  recurrence4A0_coeff_88
  recurrence4A0_coeff_89
  recurrence4A0_coeff_9
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97

attribute [local simp]
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_110
  recurrence4LeadingSquare_coeff_111
  recurrence4LeadingSquare_coeff_112
  recurrence4LeadingSquare_coeff_113
  recurrence4LeadingSquare_coeff_114
  recurrence4LeadingSquare_coeff_115
  recurrence4LeadingSquare_coeff_116
  recurrence4LeadingSquare_coeff_117
  recurrence4LeadingSquare_coeff_118
  recurrence4LeadingSquare_coeff_119
  recurrence4LeadingSquare_coeff_120
  recurrence4LeadingSquare_coeff_121
  recurrence4LeadingSquare_coeff_122
  recurrence4LeadingSquare_coeff_123
  recurrence4LeadingSquare_coeff_124
  recurrence4LeadingSquare_coeff_125
  recurrence4LeadingSquare_coeff_126
  recurrence4LeadingSquare_coeff_127
  recurrence4LeadingSquare_coeff_128
  recurrence4LeadingSquare_coeff_129
  recurrence4LeadingSquare_coeff_130
  recurrence4LeadingSquare_coeff_131
  recurrence4LeadingSquare_coeff_132
  recurrence4LeadingSquare_coeff_133
  recurrence4LeadingSquare_coeff_134
  recurrence4LeadingSquare_coeff_135
  recurrence4LeadingSquare_coeff_136
  recurrence4LeadingSquare_coeff_137
  recurrence4LeadingSquare_coeff_138
  recurrence4LeadingSquare_coeff_139
  recurrence4LeadingSquare_coeff_140
  recurrence4LeadingSquare_coeff_141
  recurrence4LeadingSquare_coeff_142
  recurrence4LeadingSquare_coeff_143
  recurrence4LeadingSquare_coeff_144
  recurrence4LeadingSquare_coeff_145
  recurrence4LeadingSquare_coeff_146
  recurrence4LeadingSquare_coeff_147
  recurrence4LeadingSquare_coeff_148
  recurrence4LeadingSquare_coeff_149
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161

attribute [local simp]
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168
  recurrence4LeadingSquare_coeff_169
  recurrence4LeadingSquare_coeff_170
  recurrence4LeadingSquare_coeff_171
  recurrence4LeadingSquare_coeff_172
  recurrence4LeadingSquare_coeff_173
  recurrence4LeadingSquare_coeff_174
  recurrence4LeadingSquare_coeff_175
  recurrence4LeadingSquare_coeff_176
  recurrence4LeadingSquare_coeff_177
  recurrence4LeadingSquare_coeff_178
  recurrence4LeadingSquare_coeff_179
  recurrence4LeadingSquare_coeff_180
  recurrence4LeadingSquare_coeff_181
  recurrence4LeadingSquare_coeff_182
  recurrence4LeadingSquare_coeff_183
  recurrence4LeadingSquare_coeff_184
  recurrence4LeadingSquare_coeff_185
  recurrence4LeadingSquare_coeff_186
  recurrence4LeadingSquare_coeff_187
  recurrence4LeadingSquare_coeff_188
  recurrence4LeadingSquare_coeff_189
  recurrence4LeadingSquare_coeff_190
  recurrence4LeadingSquare_coeff_191
  recurrence4LeadingSquare_coeff_192
  recurrence4LeadingSquare_coeff_193
  recurrence4LeadingSquare_coeff_194
  recurrence4LeadingSquare_coeff_195
  recurrence4LeadingSquare_coeff_196
  recurrence4LeadingSquare_coeff_197
  recurrence4LeadingSquare_coeff_198
  recurrence4LeadingSquare_coeff_199
  recurrence4LeadingSquare_coeff_200
  recurrence4LeadingSquare_coeff_201
  recurrence4LeadingSquare_coeff_202
  recurrence4LeadingSquare_coeff_203
  recurrence4LeadingSquare_coeff_204
  recurrence4LeadingSquare_coeff_205
  recurrence4LeadingSquare_coeff_206
  recurrence4LeadingSquare_coeff_207
  recurrence4LeadingSquare_coeff_208
  recurrence4LeadingSquare_coeff_209
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_220
  recurrence4LeadingSquare_coeff_221
  recurrence4LeadingSquare_coeff_222
  recurrence4LeadingSquare_coeff_223
  recurrence4LeadingSquare_coeff_224
  recurrence4LeadingSquare_coeff_225

attribute [local simp]
  recurrence4LeadingSquare_coeff_226
  recurrence4LeadingSquare_coeff_227
  recurrence4LeadingSquare_coeff_228
  recurrence4LeadingSquare_coeff_229
  recurrence4LeadingSquare_coeff_230
  recurrence4LeadingSquare_coeff_231
  recurrence4LeadingSquare_coeff_232
  recurrence4LeadingSquare_coeff_233
  recurrence4LeadingSquare_coeff_234
  recurrence4LeadingSquare_coeff_235
  recurrence4LeadingSquare_coeff_236
  recurrence4LeadingSquare_coeff_237
  recurrence4LeadingSquare_coeff_238
  recurrence4LeadingSquare_coeff_239
  recurrence4LeadingSquare_coeff_240
  recurrence4LeadingSquare_coeff_241
  recurrence4LeadingSquare_coeff_242
  recurrence4LeadingSquare_coeff_243
  recurrence4LeadingSquare_coeff_244
  recurrence4LeadingSquare_coeff_245
  recurrence4LeadingSquare_coeff_246
  recurrence4LeadingSquare_coeff_247
  recurrence4LeadingSquare_coeff_248
  recurrence4LeadingSquare_coeff_249
  recurrence4LeadingSquare_coeff_250
  recurrence4LeadingSquare_coeff_251
  recurrence4LeadingSquare_coeff_252
  recurrence4LeadingSquare_coeff_253
  recurrence4LeadingSquare_coeff_254
  recurrence4LeadingSquare_coeff_255
  recurrence4LeadingSquare_coeff_256
  recurrence4LeadingSquare_coeff_257
  recurrence4LeadingSquare_coeff_258
  recurrence4LeadingSquare_coeff_259
  recurrence4LeadingSquare_coeff_260
  recurrence4LeadingSquare_coeff_261
  recurrence4LeadingSquare_coeff_262
  recurrence4LeadingSquare_coeff_263
  recurrence4LeadingSquare_coeff_264
  recurrence4LeadingSquare_coeff_265
  recurrence4LeadingSquare_coeff_266
  recurrence4LeadingSquare_coeff_267
  recurrence4LeadingSquare_coeff_268
  recurrence4LeadingSquare_coeff_269
  recurrence4LeadingSquare_coeff_270
  recurrence4LeadingSquare_coeff_271
  recurrence4LeadingSquare_coeff_272
  recurrence4LeadingSquare_coeff_273
  recurrence4LeadingSquare_coeff_274
  recurrence4LeadingSquare_coeff_275
  recurrence4LeadingSquare_coeff_276
  recurrence4LeadingSquare_coeff_277
  recurrence4LeadingSquare_coeff_278
  recurrence4LeadingSquare_coeff_279
  recurrence4LeadingSquare_coeff_280
  recurrence4LeadingSquare_coeff_281
  recurrence4LeadingSquare_coeff_282
  recurrence4LeadingSquare_coeff_283
  recurrence4LeadingSquare_coeff_284
  recurrence4LeadingSquare_coeff_285
  recurrence4LeadingSquare_coeff_286
  recurrence4LeadingSquare_coeff_287
  recurrence4LeadingSquare_coeff_288
  recurrence4LeadingSquare_coeff_289

attribute [local simp]
  recurrence4LeadingSquare_coeff_290
  recurrence4LeadingSquare_coeff_291
  recurrence4LeadingSquare_coeff_292
  recurrence4LeadingSquare_coeff_293
  recurrence4LeadingSquare_coeff_294
  recurrence4LeadingSquare_coeff_295
  recurrence4LeadingSquare_coeff_296
  recurrence4LeadingSquare_coeff_297
  recurrence4LeadingSquare_coeff_298
  recurrence4LeadingSquare_coeff_299
  recurrence4LeadingSquare_coeff_300
  recurrence4LeadingSquare_coeff_301
  recurrence4LeadingSquare_coeff_302
  recurrence4LeadingSquare_coeff_303
  recurrence4LeadingSquare_coeff_304
  recurrence4LeadingSquare_coeff_305
  recurrence4LeadingSquare_coeff_306
  recurrence4LeadingSquare_coeff_307
  recurrence4LeadingSquare_coeff_308
  recurrence4LeadingSquare_coeff_309
  recurrence4LeadingSquare_coeff_310
  recurrence4LeadingSquare_coeff_311
  recurrence4LeadingSquare_coeff_312
  recurrence4LeadingSquare_coeff_313
  recurrence4LeadingSquare_coeff_314
  recurrence4LeadingSquare_coeff_315
  recurrence4LeadingSquare_coeff_316
  recurrence4LeadingSquare_coeff_317
  recurrence4LeadingSquare_coeff_318
  recurrence4LeadingSquare_coeff_319
  recurrence4LeadingSquare_coeff_320
  recurrence4LeadingSquare_coeff_321
  recurrence4LeadingSquare_coeff_322
  recurrence4LeadingSquare_coeff_323
  recurrence4LeadingSquare_coeff_324
  recurrence4LeadingSquare_coeff_325
  recurrence4LeadingSquare_coeff_326
  recurrence4LeadingSquare_coeff_327
  recurrence4LeadingSquare_coeff_328
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_90
  recurrence4LeadingSquare_coeff_91
  recurrence4LeadingSquare_coeff_92
  recurrence4LeadingSquare_coeff_93
  recurrence4LeadingSquare_coeff_94
  recurrence4LeadingSquare_coeff_95
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

private theorem recurrence4Scalar0Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (319 + x) *
        remainder4Coefficient0.coeff (319 - (319 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 319 + x
  · rw [recurrence4LeadingSquare_coeff_high (319 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (319 - (319 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_319 :
    recurrence4Scalar0Left.coeff 319 =
      (((((44901604054193222049 * 10 ^ 70 +
        7198499961702983857020114316562483983751339912941861932416397943403199) * 10 ^ 70 +
        9809122012744941271169154886183553957517743752379284881334176880414566) * 10 ^ 70 +
        3093715988816277902313614201988172404021445289034119263779908140440909) * 10 ^ 70 +
        5252504683495969722690520630123349948761303699322213212509035298063557) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (319 - x)) = _
  rw [show 320 = 125 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (320 + x) *
        remainder4Coefficient0.coeff (320 - (320 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 320 + x
  · rw [recurrence4LeadingSquare_coeff_high (320 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (320 - (320 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_320 :
    recurrence4Scalar0Left.coeff 320 =
      -(((((24170949961983710526 * 10 ^ 70 +
        5011020768287742449432931485191693374355945738358782369307597668109809) * 10 ^ 70 +
        3127170073249260198757445235788587377946731569153393043225048774401476) * 10 ^ 70 +
        1477102173183319338550459897526473931327996831839355788045862362950900) * 10 ^ 70 +
        8106492504251377079082749843777618462409064427778748309189529799694716) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (320 - x)) = _
  rw [show 321 = 126 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (321 + x) *
        remainder4Coefficient0.coeff (321 - (321 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 321 + x
  · rw [recurrence4LeadingSquare_coeff_high (321 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (321 - (321 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_321 :
    recurrence4Scalar0Left.coeff 321 =
      (((((12569831636944203093 * 10 ^ 70 +
        6807029919647262813411124038860856537698534212153738118311659263327972) * 10 ^ 70 +
        6471198791511277952981610446127036442958920021796578855205634618760085) * 10 ^ 70 +
        8444219727426140553980438530266838805913082972178457923905499275349218) * 10 ^ 70 +
        6455191516875216193495218227944180102672687261255295988200993977483281) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (321 - x)) = _
  rw [show 322 = 127 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (322 + x) *
        remainder4Coefficient0.coeff (322 - (322 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 322 + x
  · rw [recurrence4LeadingSquare_coeff_high (322 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (322 - (322 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_322 :
    recurrence4Scalar0Left.coeff 322 =
      -(((((6287743511366963394 * 10 ^ 70 +
        3385443163850702118589886864746903155524893797320628498922063018870918) * 10 ^ 70 +
        3806489591033005495527859132434921619241118998024774032504870831035456) * 10 ^ 70 +
        3253340088418775207938481742821651839471816202801648013685112669288253) * 10 ^ 70 +
        3734327375704762759172794222555965392260059278849731182497420402598845) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (322 - x)) = _
  rw [show 323 = 128 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (323 + x) *
        remainder4Coefficient0.coeff (323 - (323 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 323 + x
  · rw [recurrence4LeadingSquare_coeff_high (323 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (323 - (323 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_323 :
    recurrence4Scalar0Left.coeff 323 =
      (((((3002122077363566228 * 10 ^ 70 +
        4896826059104912978365373539918480143928516934969934592258556761988133) * 10 ^ 70 +
        0888651751149076535235658665834304840620500705658570277524538522308335) * 10 ^ 70 +
        7761634250351829266645043916188564766177051845228041772408455869679528) * 10 ^ 70 +
        4074400968865432363883100374969076465166575456280485347728081701919986) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (323 - x)) = _
  rw [show 324 = 129 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (324 + x) *
        remainder4Coefficient0.coeff (324 - (324 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 324 + x
  · rw [recurrence4LeadingSquare_coeff_high (324 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (324 - (324 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_324 :
    recurrence4Scalar0Left.coeff 324 =
      -(((((1348913959626982944 * 10 ^ 70 +
        0737055833761907341684247514014240972350883093845361958288454045586299) * 10 ^ 70 +
        8077277734713931854036126745548065971897599055146192128450285507648445) * 10 ^ 70 +
        8840462724590508674351677090799622292560063843759051044373963656436466) * 10 ^ 70 +
        3307319950120082473105638257114415340648009340080538869865641612766926) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (324 - x)) = _
  rw [show 325 = 130 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (325 + x) *
        remainder4Coefficient0.coeff (325 - (325 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 325 + x
  · rw [recurrence4LeadingSquare_coeff_high (325 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (325 - (325 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_325 :
    recurrence4Scalar0Left.coeff 325 =
      (((((554380381465020753 * 10 ^ 70 +
        1532846897064529475437667999145300763470566639532369829478437516276168) * 10 ^ 70 +
        9815416324686333104464494761152958944155310116603213579250513121143855) * 10 ^ 70 +
        6978907501356574981534300391362229300828135351310915863304541814792036) * 10 ^ 70 +
        8976175560175845828352556596524931076761697317235881808320938310329391) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (325 - x)) = _
  rw [show 326 = 131 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (326 + x) *
        remainder4Coefficient0.coeff (326 - (326 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 326 + x
  · rw [recurrence4LeadingSquare_coeff_high (326 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (326 - (326 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_326 :
    recurrence4Scalar0Left.coeff 326 =
      -(((((194407264180134043 * 10 ^ 70 +
        4359832607843018009065435876703624656061076457437494551750375385811616) * 10 ^ 70 +
        7177819356584887719896812352447396972622741746519067954447663332373422) * 10 ^ 70 +
        8868762305974053862737793135249424583317251624304527065516924216706383) * 10 ^ 70 +
        2665547445718285610392314812754537792941414027526792618157734494679820) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (326 - x)) = _
  rw [show 327 = 132 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (327 + x) *
        remainder4Coefficient0.coeff (327 - (327 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 327 + x
  · rw [recurrence4LeadingSquare_coeff_high (327 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (327 - (327 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_327 :
    recurrence4Scalar0Left.coeff 327 =
      (((((44617243512810394 * 10 ^ 70 +
        6649332003986563358001232113733218085922110580025372424256895816096937) * 10 ^ 70 +
        9849521340678688481276497462554952637106912045872982149139048575271838) * 10 ^ 70 +
        9472089015604338786357168653627544868410597567620112409892977047033501) * 10 ^ 70 +
        5738413590918075142846174722215252990347994058646271777473306507393092) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (327 - x)) = _
  rw [show 328 = 133 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (328 + x) *
        remainder4Coefficient0.coeff (328 - (328 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 328 + x
  · rw [recurrence4LeadingSquare_coeff_high (328 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (328 - (328 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_328 :
    recurrence4Scalar0Left.coeff 328 =
      (((((9194787032639301 * 10 ^ 70 +
        2033356689216206312723289103082417421051960308182637483996056037706678) * 10 ^ 70 +
        8572509945359899114562724198093294455255646388510399587538778744469370) * 10 ^ 70 +
        5761547109082033126587581788673149089395617655759450850320968383055175) * 10 ^ 70 +
        7284650128975752661905954176341422460458263533125033205749226408985218) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (328 - x)) = _
  rw [show 329 = 134 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (329 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_329 :
    recurrence4Scalar0Left.coeff 329 =
      -(((((22608633224951657 * 10 ^ 70 +
        9312267408684962971416601050583990437369428919328896630381264716675371) * 10 ^ 70 +
        6831635872892288412171070344544038132322760926731331491514398711425774) * 10 ^ 70 +
        4585063908765813078123405494480060549814559629819094502074687277929799) * 10 ^ 70 +
        0381808514025224777813480449904941635852853776042925260353867922676141) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (329 - x)) = _
  rw [show 330 = 135 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (330 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (330 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_330 :
    recurrence4Scalar0Left.coeff 330 =
      (((((21194825908364070 * 10 ^ 70 +
        7260590360102543372721416747612703415981903643126629890731986320256939) * 10 ^ 70 +
        3454058540649349110148761575935030514703414568615204835163862236883070) * 10 ^ 70 +
        3557269304095087085493750101184962123561091973245611862695060836821836) * 10 ^ 70 +
        1325660348452850701656612899370196973331090707621842590108228678738059) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (330 - x)) = _
  rw [show 331 = 136 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 1 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (331 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (331 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_331 :
    recurrence4Scalar0Left.coeff 331 =
      -(((((15831236289491772 * 10 ^ 70 +
        6475579609625318304682753814011808932366344467286191472167278814689752) * 10 ^ 70 +
        9149837404278009039618681100970040961806380402723147419030548201648357) * 10 ^ 70 +
        7512666546439917669650514982988422777770664201125823783968605930813575) * 10 ^ 70 +
        8775681601715619983734416443613909040740437549804220685041022226389024) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (331 - x)) = _
  rw [show 332 = 137 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (332 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (332 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_332 :
    recurrence4Scalar0Left.coeff 332 =
      (((((10587712520144674 * 10 ^ 70 +
        9407657958446679131740995943689486291816420634162329650438674657244344) * 10 ^ 70 +
        8756545000208565937600759414616800839856527634924671764188530723368249) * 10 ^ 70 +
        6235206403341600904763024440665449798022392512324533293610131054153569) * 10 ^ 70 +
        6549332170790150749617189132295602351841929900646649872847815657853030) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (332 - x)) = _
  rw [show 333 = 138 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 31 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (333 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (333 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_333 :
    recurrence4Scalar0Left.coeff 333 =
      -(((((6609165774858349 * 10 ^ 70 +
        1855250113265282282747938024181180491250502679459175910543926805553276) * 10 ^ 70 +
        6804583647216778808499621326162993849944479633253189342067168637118936) * 10 ^ 70 +
        3521497290809016349525551982493668442699614862389515913263286289109946) * 10 ^ 70 +
        4471377006556271190779952480440690053124003576298255663127914480565549) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (333 - x)) = _
  rw [show 334 = 139 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 30 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (334 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (334 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_334 :
    recurrence4Scalar0Left.coeff 334 =
      (((((3927154956380052 * 10 ^ 70 +
        6402448482987200543191454713590274027824820735670013781901790569202609) * 10 ^ 70 +
        6727904769348355229134139432746925737001646709070912654842619162965324) * 10 ^ 70 +
        0174270397755234125865328078488643264811618451104657079722633574090726) * 10 ^ 70 +
        1327334040329948631069207373595536707337363402629270192487288394160704) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (334 - x)) = _
  rw [show 335 = 140 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 29 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (335 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (335 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_335 :
    recurrence4Scalar0Left.coeff 335 =
      -(((((2245406832710003 * 10 ^ 70 +
        4211061426008746971436860743258361652919950504896544616376872887524684) * 10 ^ 70 +
        4407087167756503591154920271509272151386894844787255676662363417616211) * 10 ^ 70 +
        9945289555376602848429314976557646920399385047028996546457609378319703) * 10 ^ 70 +
        9913194645240222592466111756249514633484042975220854310422182061644504) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (335 - x)) = _
  rw [show 336 = 141 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 28 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (336 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (336 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_336 :
    recurrence4Scalar0Left.coeff 336 =
      (((((1243507338315788 * 10 ^ 70 +
        7632730229118315023536387343111325935980374496076518487412213272701811) * 10 ^ 70 +
        1249104926879734306025809294887664565256454428510953685897061836337184) * 10 ^ 70 +
        6359353982446791759647401165677991738750047653869743653269559174107391) * 10 ^ 70 +
        1038358234996936852911257328006959060939050523438390083525174433793442) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (336 - x)) = _
  rw [show 337 = 142 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 27 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (337 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (337 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_337 :
    recurrence4Scalar0Left.coeff 337 =
      -(((((669858286282407 * 10 ^ 70 +
        4552494608917341954389310989104358416486122053378761460432841434552305) * 10 ^ 70 +
        6912857292949471726214908810160435020003751911511994341600344921500991) * 10 ^ 70 +
        1145502078678942325086008090377526721702258217717976112059488188895718) * 10 ^ 70 +
        4312350191362523871703158588593430843251495235201066359471168438968895) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (337 - x)) = _
  rw [show 338 = 143 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 26 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (338 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (338 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_338 :
    recurrence4Scalar0Left.coeff 338 =
      (((((352002990834944 * 10 ^ 70 +
        8763453302877835908905787847175504396068275187191371606974182128036842) * 10 ^ 70 +
        7816346694623291199599129752358523918547104676155264829959122110292998) * 10 ^ 70 +
        0681842994194906392246417265170850701811746984718851680135129495340277) * 10 ^ 70 +
        9849250585819097073479566305335451622040942278192410491167482139304899) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (338 - x)) = _
  rw [show 339 = 144 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 25 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (339 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (339 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_339 :
    recurrence4Scalar0Left.coeff 339 =
      -(((((180803385631632 * 10 ^ 70 +
        8241191598746332297312104564419367086627018417631299446857457635764068) * 10 ^ 70 +
        9682576402637785949057252129022267993070808844893533427324914670646529) * 10 ^ 70 +
        1339299911857906610923840083430912674681908120876968970249316922103388) * 10 ^ 70 +
        0572292069660256671999696804452612756204633094536833493895185303489944) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (339 - x)) = _
  rw [show 340 = 145 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 24 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (340 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (340 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_340 :
    recurrence4Scalar0Left.coeff 340 =
      (((((90902680022524 * 10 ^ 70 +
        3649348746978160267953387211318516723544002454576124679482694538199830) * 10 ^ 70 +
        3878308806293439489591616903673473798885025705404719867756955095017877) * 10 ^ 70 +
        6129798526128434688398966019850566832145606284302879915968333130415641) * 10 ^ 70 +
        6732584828673257186560176522577869624689544292608715365541196821859640) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (340 - x)) = _
  rw [show 341 = 146 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 23 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (341 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (341 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_341 :
    recurrence4Scalar0Left.coeff 341 =
      -(((((44780686863156 * 10 ^ 70 +
        8550314848222192544648199324309756923012040101427339684490365843179032) * 10 ^ 70 +
        0704693610553392287241120460842080581390303849980609960776166127212300) * 10 ^ 70 +
        1970961365248193656804793653500852995895195159855155292285683586574293) * 10 ^ 70 +
        4845728742818010610336603692633233993379404283810383561460905468230653) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (341 - x)) = _
  rw [show 342 = 147 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 22 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (342 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (342 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_342 :
    recurrence4Scalar0Left.coeff 342 =
      (((((21629756929370 * 10 ^ 70 +
        9284421374341042193539851937058722876375492302391543909478946693911391) * 10 ^ 70 +
        9880288404508210035028809414662710451618815654254120570879038088736842) * 10 ^ 70 +
        7481522294769375082504158778395932844332081718923430974815403884180163) * 10 ^ 70 +
        5852926044970287934617985867897738695815002565853280496619016226933554) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (342 - x)) = _
  rw [show 343 = 148 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 21 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (343 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (343 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_343 :
    recurrence4Scalar0Left.coeff 343 =
      -(((((10248557028154 * 10 ^ 70 +
        1253369360465461411421558000021378374880882706033815686195278377852143) * 10 ^ 70 +
        5377514596394350385124235218565158835393132286497800441135870117140555) * 10 ^ 70 +
        3134220848492503972205201158116128111050364261872212950260751835244225) * 10 ^ 70 +
        7474967108533851054427731240546710835934238828664535700396226248802199) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (343 - x)) = _
  rw [show 344 = 149 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 20 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (344 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (344 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_344 :
    recurrence4Scalar0Left.coeff 344 =
      (((((4764850974428 * 10 ^ 70 +
        3116492940680290056755316856875059727903103049791873928980223083260831) * 10 ^ 70 +
        1373755526358285646713393834121892563593822315879256074751029693121011) * 10 ^ 70 +
        9400085312366835742920105118574641923682357455701590096470783239466284) * 10 ^ 70 +
        3797185031816458078699608287509932265356624121227758421232508616594154) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (344 - x)) = _
  rw [show 345 = 150 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 19 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
