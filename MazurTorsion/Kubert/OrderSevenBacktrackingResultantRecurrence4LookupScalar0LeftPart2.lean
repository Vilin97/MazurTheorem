/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar0Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (269 + x) *
        remainder4Coefficient0.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 269 + x
  · rw [recurrence4LeadingSquare_coeff_high (269 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (269 - (269 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_269 :
    recurrence4Scalar0Left.coeff 269 =
      (((((3751092352073519263571261206 * 10 ^ 70 +
        1045891807062574955542247409544923288018096944046670800554803935871810) * 10 ^ 70 +
        4655987824790400435218791945419913565010636778040476274190457299367164) * 10 ^ 70 +
        7993148494761302011516144903783717545733880888301118796987631994049601) * 10 ^ 70 +
        6107665374582367234785006946392079928284412516953544093003089316813255) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (269 - x)) = _
  rw [show 270 = 75 +
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
  rw [recurrence4Scalar0Left_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (270 + x) *
        remainder4Coefficient0.coeff (270 - (270 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 270 + x
  · rw [recurrence4LeadingSquare_coeff_high (270 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (270 - (270 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_270 :
    recurrence4Scalar0Left.coeff 270 =
      -(((((3074706506639132671083854064 * 10 ^ 70 +
        0450559853256497019827508445209448788707314779240495223651739694845699) * 10 ^ 70 +
        1394607824224328434041573963057912453454194742248438366866147312420002) * 10 ^ 70 +
        6798453052875846177725723948294239302720889258913635517070629380549152) * 10 ^ 70 +
        3887761118568701979809887862862434350971271888742875120380245835832360) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (270 - x)) = _
  rw [show 271 = 76 +
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
  rw [recurrence4Scalar0Left_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (271 + x) *
        remainder4Coefficient0.coeff (271 - (271 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 271 + x
  · rw [recurrence4LeadingSquare_coeff_high (271 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (271 - (271 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_271 :
    recurrence4Scalar0Left.coeff 271 =
      (((((2408107801855545054506516628 * 10 ^ 70 +
        6380618268433260732397584215787886073448244764560183468988477772330732) * 10 ^ 70 +
        1002622797710851178716159814685801369441253268967033390928076661852529) * 10 ^ 70 +
        3262500934320512823163018593482785984436816398769755713210523488114103) * 10 ^ 70 +
        7823246913054029528028341787850298429078049679284297488073679378410846) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (271 - x)) = _
  rw [show 272 = 77 +
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
  rw [recurrence4Scalar0Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (272 + x) *
        remainder4Coefficient0.coeff (272 - (272 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 272 + x
  · rw [recurrence4LeadingSquare_coeff_high (272 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (272 - (272 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_272 :
    recurrence4Scalar0Left.coeff 272 =
      -(((((1785601959471234424862708208 * 10 ^ 70 +
        3749776185879324607043281992765499549657524167758715607467864380709112) * 10 ^ 70 +
        1896742789104457029789188816703552783995665818419683816921873975208446) * 10 ^ 70 +
        6538283435667451190401404889315075985531250706227178865134423368330110) * 10 ^ 70 +
        2509217983323354912753763434324288959376215325400271116865558494286214) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (272 - x)) = _
  rw [show 273 = 78 +
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
  rw [recurrence4Scalar0Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (273 + x) *
        remainder4Coefficient0.coeff (273 - (273 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 273 + x
  · rw [recurrence4LeadingSquare_coeff_high (273 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (273 - (273 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_273 :
    recurrence4Scalar0Left.coeff 273 =
      (((((1231547780160483910977488914 * 10 ^ 70 +
        3688125342924519388051510633534939921609536063570608662154846396479875) * 10 ^ 70 +
        7568762103094828558131345350053955945026422956793006362204011821882760) * 10 ^ 70 +
        6426667711090823140014932222132367087665277349442650305447374888072002) * 10 ^ 70 +
        3133039893815060422322552346596894018621763509905921397046407926247674) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (273 - x)) = _
  rw [show 274 = 79 +
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
  rw [recurrence4Scalar0Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (274 + x) *
        remainder4Coefficient0.coeff (274 - (274 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 274 + x
  · rw [recurrence4LeadingSquare_coeff_high (274 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (274 - (274 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_274 :
    recurrence4Scalar0Left.coeff 274 =
      -(((((760628463321804089429135617 * 10 ^ 70 +
        6808212743405413713692773936776224609398516424407978923694585767530790) * 10 ^ 70 +
        1794977869260450479352973551327661298884415891795034912793382961219749) * 10 ^ 70 +
        4962657210087194986882361641594129802561676199102687358223979657905757) * 10 ^ 70 +
        2515380761687356711719276168614379698612692641330575234812696142629030) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (274 - x)) = _
  rw [show 275 = 80 +
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
  rw [recurrence4Scalar0Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (275 + x) *
        remainder4Coefficient0.coeff (275 - (275 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 275 + x
  · rw [recurrence4LeadingSquare_coeff_high (275 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (275 - (275 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_275 :
    recurrence4Scalar0Left.coeff 275 =
      (((((378858010942192954790454067 * 10 ^ 70 +
        6799258796596637230830796367424693512514137568382269288568089049006605) * 10 ^ 70 +
        3747772071123844150723252914931491425677507568056901150327561764760139) * 10 ^ 70 +
        3622774549783856477923780912864540144409112548773915920883159567282673) * 10 ^ 70 +
        6988472107645548520204959878720634965339388276742955499782251525720840) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (275 - x)) = _
  rw [show 276 = 81 +
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
  rw [recurrence4Scalar0Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (276 + x) *
        remainder4Coefficient0.coeff (276 - (276 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 276 + x
  · rw [recurrence4LeadingSquare_coeff_high (276 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (276 - (276 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_276 :
    recurrence4Scalar0Left.coeff 276 =
      -(((((85084372015185715278614991 * 10 ^ 70 +
        1168125882811349717029523875518785969797600110796195445427778873131067) * 10 ^ 70 +
        6089674402354003002341233626187395323079781092999821756471578364221933) * 10 ^ 70 +
        1019007162317718502884782668798177117610326825106613992567330837983611) * 10 ^ 70 +
        5247934423035640609299500745858757404942039987783552499210514393212069) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (276 - x)) = _
  rw [show 277 = 82 +
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
  rw [recurrence4Scalar0Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (277 + x) *
        remainder4Coefficient0.coeff (277 - (277 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 277 + x
  · rw [recurrence4LeadingSquare_coeff_high (277 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (277 - (277 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_277 :
    recurrence4Scalar0Left.coeff 277 =
      -(((((127252295122054497621420436 * 10 ^ 70 +
        0007452700694267282604510966899335871800142665967417106252707942202276) * 10 ^ 70 +
        4355993512926215472191023162286734767229173336785570741727543875114549) * 10 ^ 70 +
        5800311718023419474500983480318588981838976003470320289471300342134243) * 10 ^ 70 +
        0486413311694653978511077714399448683223084881948147944279769054243645) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (277 - x)) = _
  rw [show 278 = 83 +
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
  rw [recurrence4Scalar0Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (278 + x) *
        remainder4Coefficient0.coeff (278 - (278 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 278 + x
  · rw [recurrence4LeadingSquare_coeff_high (278 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (278 - (278 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_278 :
    recurrence4Scalar0Left.coeff 278 =
      (((((268323250831792212182220747 * 10 ^ 70 +
        5827788950882006022624454453229148673336185476287279155633291931154912) * 10 ^ 70 +
        5005799574146512587854144735468281285191057926765979983097326877701041) * 10 ^ 70 +
        7596130048935731536158873296543116400768354540795662740405100437393844) * 10 ^ 70 +
        2133200098318768014968537876530570009449840227468934543562266258459917) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (278 - x)) = _
  rw [show 279 = 84 +
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
  rw [recurrence4Scalar0Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (279 + x) *
        remainder4Coefficient0.coeff (279 - (279 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 279 + x
  · rw [recurrence4LeadingSquare_coeff_high (279 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (279 - (279 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_279 :
    recurrence4Scalar0Left.coeff 279 =
      -(((((350249931711303134292119132 * 10 ^ 70 +
        0006818130666623856366118930723875928677232979067489659769993306997880) * 10 ^ 70 +
        4901364688407012548071362043843093821467467965160583897863615885174155) * 10 ^ 70 +
        9679813903072974406293481711295487057309481396518755312790498426360377) * 10 ^ 70 +
        3860005493469099554350397079632612722511168814676539993957537389510967) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (279 - x)) = _
  rw [show 280 = 85 +
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
  rw [recurrence4Scalar0Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (280 + x) *
        remainder4Coefficient0.coeff (280 - (280 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 280 + x
  · rw [recurrence4LeadingSquare_coeff_high (280 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (280 - (280 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_280 :
    recurrence4Scalar0Left.coeff 280 =
      (((((385697621085427444366571933 * 10 ^ 70 +
        5556042904531312755404497470420624618071548249832399478808252445488770) * 10 ^ 70 +
        7911196206781212827303511063554237440445235818235623219554330986220578) * 10 ^ 70 +
        5351022039233741411468847870689740182588350207459848863322329703628888) * 10 ^ 70 +
        2391671707399034668692121151292096025997927699387388896740205021034697) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (280 - x)) = _
  rw [show 281 = 86 +
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
  rw [recurrence4Scalar0Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (281 + x) *
        remainder4Coefficient0.coeff (281 - (281 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 281 + x
  · rw [recurrence4LeadingSquare_coeff_high (281 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (281 - (281 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_281 :
    recurrence4Scalar0Left.coeff 281 =
      -(((((386789361700266316337205180 * 10 ^ 70 +
        8084444719022596189664764730694690668016054717307625738640422723236926) * 10 ^ 70 +
        6418457165313706990770678231744169449507813393032978634627067751484530) * 10 ^ 70 +
        7472220822918492894944517660182797925284145468621055010030524693496200) * 10 ^ 70 +
        4639254152022648975305911757384593706710705295427141456420077822844572) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (281 - x)) = _
  rw [show 282 = 87 +
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
  rw [recurrence4Scalar0Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (282 + x) *
        remainder4Coefficient0.coeff (282 - (282 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 282 + x
  · rw [recurrence4LeadingSquare_coeff_high (282 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (282 - (282 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_282 :
    recurrence4Scalar0Left.coeff 282 =
      (((((364356830456920125521582284 * 10 ^ 70 +
        7627723191685887781922021311283777037274741879140974594633830671112537) * 10 ^ 70 +
        8722372663288513143132118569752349238540263496835457724442861076115760) * 10 ^ 70 +
        4625243376271074222753687110002749026408623467073440223422601458933719) * 10 ^ 70 +
        5350249303615172133249568092821711588627792039516211525633090066385472) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (282 - x)) = _
  rw [show 283 = 88 +
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
  rw [recurrence4Scalar0Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (283 + x) *
        remainder4Coefficient0.coeff (283 - (283 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 283 + x
  · rw [recurrence4LeadingSquare_coeff_high (283 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (283 - (283 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_283 :
    recurrence4Scalar0Left.coeff 283 =
      -(((((327506586349909977474925078 * 10 ^ 70 +
        4001760999765060447256563496611923804131728084573606424918488025041026) * 10 ^ 70 +
        6188304352807392841893370920326805127260404656859858046864598324417760) * 10 ^ 70 +
        3776404153627643887209120793807587522008470782029325757125109600994216) * 10 ^ 70 +
        4740237451826817409749604393221075420510383687639096143143390358243548) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (283 - x)) = _
  rw [show 284 = 89 +
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
  rw [recurrence4Scalar0Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (284 + x) *
        remainder4Coefficient0.coeff (284 - (284 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 284 + x
  · rw [recurrence4LeadingSquare_coeff_high (284 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (284 - (284 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_284 :
    recurrence4Scalar0Left.coeff 284 =
      (((((283454109293618417538214871 * 10 ^ 70 +
        3190348863162537268518206270583462442000588497168418007306782232400601) * 10 ^ 70 +
        6191572788906512988332681547607591298033584359841643438941523866921237) * 10 ^ 70 +
        8147405109876477176905765476248392795784684392701795126509059142406269) * 10 ^ 70 +
        5418084327157064090097083316341023890212181111282809085824519496782266) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (284 - x)) = _
  rw [show 285 = 90 +
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
  rw [recurrence4Scalar0Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (285 + x) *
        remainder4Coefficient0.coeff (285 - (285 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 285 + x
  · rw [recurrence4LeadingSquare_coeff_high (285 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (285 - (285 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_285 :
    recurrence4Scalar0Left.coeff 285 =
      -(((((237564268867767407182295129 * 10 ^ 70 +
        0968090555621749648016463844543889220869513147796459600880358475083395) * 10 ^ 70 +
        3238620236766195460645767623025834264438974513032318387453275111169307) * 10 ^ 70 +
        5350763771585921141967486839624523673213455993458735100805641634601408) * 10 ^ 70 +
        5733660705909744839621794762822048717057807476867441427821298460579503) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (285 - x)) = _
  rw [show 286 = 91 +
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
  rw [recurrence4Scalar0Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (286 + x) *
        remainder4Coefficient0.coeff (286 - (286 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 286 + x
  · rw [recurrence4LeadingSquare_coeff_high (286 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (286 - (286 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_286 :
    recurrence4Scalar0Left.coeff 286 =
      (((((193533643440021411306153267 * 10 ^ 70 +
        1446173573942500124183543516565687148397726327489730937034157662790015) * 10 ^ 70 +
        3546264364770250329336926262975059445340328700927208167496786071423090) * 10 ^ 70 +
        0094847115740358759288285468491528081752738886262057610740428079298059) * 10 ^ 70 +
        1298498755780866371333041548415229156920920161674480472592521913142332) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (286 - x)) = _
  rw [show 287 = 92 +
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
  rw [recurrence4Scalar0Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (287 + x) *
        remainder4Coefficient0.coeff (287 - (287 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 287 + x
  · rw [recurrence4LeadingSquare_coeff_high (287 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (287 - (287 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_287 :
    recurrence4Scalar0Left.coeff 287 =
      -(((((153654887470102726923196592 * 10 ^ 70 +
        7536090454557890270878483808962866001421022496616641607726716218498624) * 10 ^ 70 +
        6177721702625039939695438594521361855155493542716838826413889096935767) * 10 ^ 70 +
        2946927640225351923486238566214635307366458977922200958825617638130980) * 10 ^ 70 +
        0246316668294330519691524000504276085715607885745633454392505581535682) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (287 - x)) = _
  rw [show 288 = 93 +
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
  rw [recurrence4Scalar0Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (288 + x) *
        remainder4Coefficient0.coeff (288 - (288 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 288 + x
  · rw [recurrence4LeadingSquare_coeff_high (288 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (288 - (288 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_288 :
    recurrence4Scalar0Left.coeff 288 =
      (((((119113249544993062410468288 * 10 ^ 70 +
        8895368439930737639229483653204627232013428527640755914011242174357739) * 10 ^ 70 +
        1879169284326249961387172245765929924771705367230303046119553793420638) * 10 ^ 70 +
        3195039678402756998276185341350338590687455818177837096687752982339938) * 10 ^ 70 +
        1090047582088053992773868758036807426228054988829558157554112872510924) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (288 - x)) = _
  rw [show 289 = 94 +
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
  rw [recurrence4Scalar0Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (289 + x) *
        remainder4Coefficient0.coeff (289 - (289 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 289 + x
  · rw [recurrence4LeadingSquare_coeff_high (289 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (289 - (289 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_289 :
    recurrence4Scalar0Left.coeff 289 =
      -(((((90277683919075133948998662 * 10 ^ 70 +
        7437500008897643271872406389944219182144058383437595784537660832822077) * 10 ^ 70 +
        1712794211692637758646377948508913161494106933430145940228122177362976) * 10 ^ 70 +
        1037128624906733530700701141784295979055857340986706421532899966808831) * 10 ^ 70 +
        4472744898213048591716811863737618691371153725452780784187208641170025) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (289 - x)) = _
  rw [show 290 = 95 +
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
  rw [recurrence4Scalar0Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (290 + x) *
        remainder4Coefficient0.coeff (290 - (290 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 290 + x
  · rw [recurrence4LeadingSquare_coeff_high (290 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (290 - (290 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_290 :
    recurrence4Scalar0Left.coeff 290 =
      (((((66961575491549468705868928 * 10 ^ 70 +
        8650006605195474975911296103682522033266983940996257724583217211665211) * 10 ^ 70 +
        8745348240116057804283383796632454984029972261654964762860608153108192) * 10 ^ 70 +
        0797069396062679326823536587749168917464519618198081655406663547601306) * 10 ^ 70 +
        7099852849793088770449484503558286188814679906472539281524200094926291) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (290 - x)) = _
  rw [show 291 = 96 +
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
  rw [recurrence4Scalar0Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (291 + x) *
        remainder4Coefficient0.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 291 + x
  · rw [recurrence4LeadingSquare_coeff_high (291 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (291 - (291 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_291 :
    recurrence4Scalar0Left.coeff 291 =
      -(((((48639358196773982379132166 * 10 ^ 70 +
        9595401538338087337509997575422543609125437163696846317558975770716354) * 10 ^ 70 +
        7305626953516057696648333574021461269828175426049305323886163726889232) * 10 ^ 70 +
        1189260259721446225978707058985798807552675601635530040553367449574759) * 10 ^ 70 +
        1403104112781529764090996498849131228918497248600255081948541418550155) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (291 - x)) = _
  rw [show 292 = 97 +
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
  rw [recurrence4Scalar0Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (292 + x) *
        remainder4Coefficient0.coeff (292 - (292 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 292 + x
  · rw [recurrence4LeadingSquare_coeff_high (292 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (292 - (292 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_292 :
    recurrence4Scalar0Left.coeff 292 =
      (((((34614351806002368694445519 * 10 ^ 70 +
        8383470980197029765306180956841955877353172542271315536622914047491843) * 10 ^ 70 +
        6577911245945837384017469066698804975729821860639743090314714984762780) * 10 ^ 70 +
        3501256668234882182613207015921961450839242881758980856317972414335554) * 10 ^ 70 +
        2125390470496325521423071303411424808053751999361924841461870797121376) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (292 - x)) = _
  rw [show 293 = 98 +
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
  rw [recurrence4Scalar0Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (293 + x) *
        remainder4Coefficient0.coeff (293 - (293 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 293 + x
  · rw [recurrence4LeadingSquare_coeff_high (293 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (293 - (293 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_293 :
    recurrence4Scalar0Left.coeff 293 =
      -(((((24139643597479137579764460 * 10 ^ 70 +
        2799766452536806845936242016763382440991949882156015308926791303914633) * 10 ^ 70 +
        2023753927204968873513424342140114034109196985916507109140989120245224) * 10 ^ 70 +
        4278993376870966344351785807762505991641995799483230357937965213634429) * 10 ^ 70 +
        1478597042913504240370615152992644748133425713265870500461154195104853) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (293 - x)) = _
  rw [show 294 = 99 +
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
  rw [recurrence4Scalar0Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (294 + x) *
        remainder4Coefficient0.coeff (294 - (294 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 294 + x
  · rw [recurrence4LeadingSquare_coeff_high (294 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (294 - (294 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_294 :
    recurrence4Scalar0Left.coeff 294 =
      (((((16497899138550805261824915 * 10 ^ 70 +
        3297402351679255855698781746235564982327274220961718093979793521424217) * 10 ^ 70 +
        1768039967636250658522664280582632538317029585512224364291500015353811) * 10 ^ 70 +
        4655501458629432374181708817102183720135228280596257978524947137390895) * 10 ^ 70 +
        0220403045316459890984993238597879342288181171837699743758325354464135) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (294 - x)) = _
  rw [show 295 = 100 +
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
  rw [recurrence4Scalar0Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (295 + x) *
        remainder4Coefficient0.coeff (295 - (295 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 295 + x
  · rw [recurrence4LeadingSquare_coeff_high (295 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (295 - (295 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_295 :
    recurrence4Scalar0Left.coeff 295 =
      -(((((11047972745638533024990341 * 10 ^ 70 +
        6879200328617855031820553390026438362566735982597368593716631262854488) * 10 ^ 70 +
        5220242582349312662011609521759332305822708565463467953438989877634075) * 10 ^ 70 +
        3230731943147417741748569090011561935938791885853606333632224654406434) * 10 ^ 70 +
        5362671574282679526076246977099696751551133183671194827747953371036713) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (295 - x)) = _
  rw [show 296 = 101 +
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
  rw [recurrence4Scalar0Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (296 + x) *
        remainder4Coefficient0.coeff (296 - (296 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 296 + x
  · rw [recurrence4LeadingSquare_coeff_high (296 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (296 - (296 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_296 :
    recurrence4Scalar0Left.coeff 296 =
      (((((7246604950908926593887856 * 10 ^ 70 +
        4939316942553517775809132202992790928786387006304879630654920020952845) * 10 ^ 70 +
        1017848317478754417631670718837828677389307110869689491205846720323179) * 10 ^ 70 +
        6911902613443042936820105401983619675200274860697756928651256911765639) * 10 ^ 70 +
        1291568249470995782020702878504828393419024057873875258623863337267487) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (296 - x)) = _
  rw [show 297 = 102 +
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
  rw [recurrence4Scalar0Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (297 + x) *
        remainder4Coefficient0.coeff (297 - (297 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 297 + x
  · rw [recurrence4LeadingSquare_coeff_high (297 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (297 - (297 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_297 :
    recurrence4Scalar0Left.coeff 297 =
      -(((((4652860976739064663588479 * 10 ^ 70 +
        4592066352103156477901803661911050005784707288457405998370251892048286) * 10 ^ 70 +
        3454928738728223327862420444773793955933837275761172798964086853114437) * 10 ^ 70 +
        4866152881913102856586242807807343850621140679722680450412801937247204) * 10 ^ 70 +
        9819596260952149688147461425972166423408546837414296803644679475461681) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (297 - x)) = _
  rw [show 298 = 103 +
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
  rw [recurrence4Scalar0Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (298 + x) *
        remainder4Coefficient0.coeff (298 - (298 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 298 + x
  · rw [recurrence4LeadingSquare_coeff_high (298 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (298 - (298 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_298 :
    recurrence4Scalar0Left.coeff 298 =
      (((((2921742518873368599346554 * 10 ^ 70 +
        6947627956325718788972864577266062100429341370251376367952423761046507) * 10 ^ 70 +
        2321854509654193560301431782200812803987462394479088401734761620902555) * 10 ^ 70 +
        0475013340823085133025003518975726301166927187620638100514928957807249) * 10 ^ 70 +
        6046879887427581572036111291614998359264780659266852977170983475479455) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (298 - x)) = _
  rw [show 299 = 104 +
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
  rw [recurrence4Scalar0Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (299 + x) *
        remainder4Coefficient0.coeff (299 - (299 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 299 + x
  · rw [recurrence4LeadingSquare_coeff_high (299 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (299 - (299 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_299 :
    recurrence4Scalar0Left.coeff 299 =
      -(((((1791958838712813718463075 * 10 ^ 70 +
        2265838665915451804117859136907342416050679211981992619406347950174241) * 10 ^ 70 +
        6031113453252300329139051139762403864567182418862406765673018346800634) * 10 ^ 70 +
        3315237541864044949334856080254696221777182640640533706438215636645166) * 10 ^ 70 +
        9712648654374854746251207928562472623881636123523977421014320274932261) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (299 - x)) = _
  rw [show 300 = 105 +
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
  rw [recurrence4Scalar0Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (300 + x) *
        remainder4Coefficient0.coeff (300 - (300 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 300 + x
  · rw [recurrence4LeadingSquare_coeff_high (300 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (300 - (300 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_300 :
    recurrence4Scalar0Left.coeff 300 =
      (((((1071426368013068493702595 * 10 ^ 70 +
        5084217754784976691159171845601353167712261643563674048458818244123542) * 10 ^ 70 +
        7328600178277211809038249838845384009419741624122314799900937082529487) * 10 ^ 70 +
        0781905438629513441654674144410902457586305817729079836182969165291640) * 10 ^ 70 +
        7461159055158607779181091928009031753473414748607473370994497513322730) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (300 - x)) = _
  rw [show 301 = 106 +
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
  rw [recurrence4Scalar0Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (301 + x) *
        remainder4Coefficient0.coeff (301 - (301 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 301 + x
  · rw [recurrence4LeadingSquare_coeff_high (301 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (301 - (301 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_301 :
    recurrence4Scalar0Left.coeff 301 =
      -(((((622831205397898523188403 * 10 ^ 70 +
        0475725565543262174377447342393871413996000765173214431276888314569759) * 10 ^ 70 +
        6871515569732321203721603833642439670797405909740683232393595474278634) * 10 ^ 70 +
        3987689572291781202378899540513579283710369605183108459268530437320372) * 10 ^ 70 +
        4635440144207683185816805237733875777034339139973381426154647649779187) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (301 - x)) = _
  rw [show 302 = 107 +
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
  rw [recurrence4Scalar0Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (302 + x) *
        remainder4Coefficient0.coeff (302 - (302 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 302 + x
  · rw [recurrence4LeadingSquare_coeff_high (302 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (302 - (302 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_302 :
    recurrence4Scalar0Left.coeff 302 =
      (((((350606070223201710030992 * 10 ^ 70 +
        0074727351165544226467146705052889981138947664247734451998037690161094) * 10 ^ 70 +
        1155939439052154913543111375902730094223425552771396353897959401463857) * 10 ^ 70 +
        4034552259944450950834482124862535527167232877158068140575056204470834) * 10 ^ 70 +
        4234656943614899789668237942578221736893297184403259052957668996827783) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (302 - x)) = _
  rw [show 303 = 108 +
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
  rw [recurrence4Scalar0Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (303 + x) *
        remainder4Coefficient0.coeff (303 - (303 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 303 + x
  · rw [recurrence4LeadingSquare_coeff_high (303 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (303 - (303 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_303 :
    recurrence4Scalar0Left.coeff 303 =
      -(((((189953342761444793806226 * 10 ^ 70 +
        4882139019035597655626507010440854512692046322453669840803499591845361) * 10 ^ 70 +
        6232190407953685362630916205859126395749383500602621305376519208918262) * 10 ^ 70 +
        2268456441184211107176359068369037616315310052319156010841842350793420) * 10 ^ 70 +
        8020091691963044365967715484356298708304938416646332887951523653825608) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (303 - x)) = _
  rw [show 304 = 109 +
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
  rw [recurrence4Scalar0Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (304 + x) *
        remainder4Coefficient0.coeff (304 - (304 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 304 + x
  · rw [recurrence4LeadingSquare_coeff_high (304 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (304 - (304 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_304 :
    recurrence4Scalar0Left.coeff 304 =
      (((((98062775207008569170814 * 10 ^ 70 +
        1407587388356572512069048216634665341836038459072622049022978709610036) * 10 ^ 70 +
        7825427908947077530537637549789590333066433963559219721315688514811740) * 10 ^ 70 +
        6033439844605559114690376712985979023274223460581936066536840883848932) * 10 ^ 70 +
        0748468005432503810666787049079305885682649387021596979234638290081567) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (304 - x)) = _
  rw [show 305 = 110 +
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
  rw [recurrence4Scalar0Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (305 + x) *
        remainder4Coefficient0.coeff (305 - (305 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 305 + x
  · rw [recurrence4LeadingSquare_coeff_high (305 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (305 - (305 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_305 :
    recurrence4Scalar0Left.coeff 305 =
      -(((((47381930995197572019851 * 10 ^ 70 +
        0514266360010231984069498448363938381605884704752118293609908696970369) * 10 ^ 70 +
        2910638113221676929108174726371816414610319020258018088657706692605909) * 10 ^ 70 +
        4435716145070530758246109158937469602097825077058991174785810336004126) * 10 ^ 70 +
        0389919367742727680046504306554123376386651755457958876283021002958287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (305 - x)) = _
  rw [show 306 = 111 +
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
  rw [recurrence4Scalar0Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (306 + x) *
        remainder4Coefficient0.coeff (306 - (306 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 306 + x
  · rw [recurrence4LeadingSquare_coeff_high (306 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (306 - (306 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_306 :
    recurrence4Scalar0Left.coeff 306 =
      (((((20650091016895952149621 * 10 ^ 70 +
        7773310680564450231763462130246057762117828874722815425764732004108400) * 10 ^ 70 +
        0340592041877041280044420210614143984374240477806069968444383402875407) * 10 ^ 70 +
        5768165320613077899946294215642217634644896125751252788566292446777428) * 10 ^ 70 +
        5680828180984308932576660445128172784453623802273826153814501994619657) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (306 - x)) = _
  rw [show 307 = 112 +
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
  rw [recurrence4Scalar0Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (307 + x) *
        remainder4Coefficient0.coeff (307 - (307 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 307 + x
  · rw [recurrence4LeadingSquare_coeff_high (307 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (307 - (307 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_307 :
    recurrence4Scalar0Left.coeff 307 =
      -(((((7356542555455141946226 * 10 ^ 70 +
        6057240005156943344503846234612874638548357728794556641037174662614408) * 10 ^ 70 +
        2361239552539525292701772879593241353154614260752201644440941239572178) * 10 ^ 70 +
        9459972988326855612881478393123853274778865200107472144276017630273599) * 10 ^ 70 +
        8545409175674305005224394537416539848991786853626884589444050360513711) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (307 - x)) = _
  rw [show 308 = 113 +
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
  rw [recurrence4Scalar0Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (308 + x) *
        remainder4Coefficient0.coeff (308 - (308 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 308 + x
  · rw [recurrence4LeadingSquare_coeff_high (308 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (308 - (308 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_308 :
    recurrence4Scalar0Left.coeff 308 =
      (((((1294144066977620120302 * 10 ^ 70 +
        4133327963853956487756495255875593800127256122810374090607861463861179) * 10 ^ 70 +
        4243567899701663745131823730106842908425593281596020538837555482393909) * 10 ^ 70 +
        3405384376754300418804297744430917338120632479752081460391745974288593) * 10 ^ 70 +
        7333630934623147508582858821671938987659609082020348884439424922767049) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (308 - x)) = _
  rw [show 309 = 114 +
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
  rw [recurrence4Scalar0Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (309 + x) *
        remainder4Coefficient0.coeff (309 - (309 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 309 + x
  · rw [recurrence4LeadingSquare_coeff_high (309 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (309 - (309 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_309 :
    recurrence4Scalar0Left.coeff 309 =
      (((((1079436763579607541378 * 10 ^ 70 +
        7439579287215822056702247808432588831062093030375401510976491871640563) * 10 ^ 70 +
        0920377085234568986314506402941618860474559059881281963603090675450584) * 10 ^ 70 +
        9603232038282923168650207294113873366004175016906728728610376469332185) * 10 ^ 70 +
        7165319261703855308712431900141471250030223210967629847858527400936477) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (309 - x)) = _
  rw [show 310 = 115 +
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
  rw [recurrence4Scalar0Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (310 + x) *
        remainder4Coefficient0.coeff (310 - (310 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 310 + x
  · rw [recurrence4LeadingSquare_coeff_high (310 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (310 - (310 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_310 :
    recurrence4Scalar0Left.coeff 310 =
      -(((((1706741616865847833002 * 10 ^ 70 +
        3103700822541951619628851311418018124899763704618449640426774362893552) * 10 ^ 70 +
        9110755942617648577636605404080343738141730522305693498212316742310061) * 10 ^ 70 +
        1456160917400346504115915774364889949745785096053959480792932576696795) * 10 ^ 70 +
        0192713038786467717895544408772080176160398137618758427121916064072217) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (310 - x)) = _
  rw [show 311 = 116 +
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
  rw [recurrence4Scalar0Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (311 + x) *
        remainder4Coefficient0.coeff (311 - (311 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 311 + x
  · rw [recurrence4LeadingSquare_coeff_high (311 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (311 - (311 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_311 :
    recurrence4Scalar0Left.coeff 311 =
      (((((1601840006842740569914 * 10 ^ 70 +
        8354426259600073105759029194368940883288803638128415697337458020148352) * 10 ^ 70 +
        6619030334546499384564994630867318564347749052211336104820400434115121) * 10 ^ 70 +
        6464965770890861606028020646512199828411800201645859422271537322706044) * 10 ^ 70 +
        9333176375690059617767814803954895462516423564939199200395232720816419) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (311 - x)) = _
  rw [show 312 = 117 +
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
  rw [recurrence4Scalar0Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (312 + x) *
        remainder4Coefficient0.coeff (312 - (312 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 312 + x
  · rw [recurrence4LeadingSquare_coeff_high (312 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (312 - (312 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_312 :
    recurrence4Scalar0Left.coeff 312 =
      -(((((1260285424467334044443 * 10 ^ 70 +
        5849139159842855180433829458273551327228779289413232843324815985706725) * 10 ^ 70 +
        7101744375692449001020276717818266298166023874058572237229666145651186) * 10 ^ 70 +
        7373137827447356714434675714485224574013477441292931766976832217373314) * 10 ^ 70 +
        3057614941670964472771270621774523006213105316032376160045476212825426) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (312 - x)) = _
  rw [show 313 = 118 +
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
  rw [recurrence4Scalar0Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (313 + x) *
        remainder4Coefficient0.coeff (313 - (313 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 313 + x
  · rw [recurrence4LeadingSquare_coeff_high (313 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (313 - (313 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_313 :
    recurrence4Scalar0Left.coeff 313 =
      (((((901120777247119908456 * 10 ^ 70 +
        0004201764020387499328849059937476865950646382191312284851893292179111) * 10 ^ 70 +
        5419534312424391204473918775171565121111684452520021817305854236029082) * 10 ^ 70 +
        0821488405446920091314114579669201165151224377443860470333653316671443) * 10 ^ 70 +
        8632029692482919554219109345644484140549423992474604726398925938270870) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (313 - x)) = _
  rw [show 314 = 119 +
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
  rw [recurrence4Scalar0Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (314 + x) *
        remainder4Coefficient0.coeff (314 - (314 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 314 + x
  · rw [recurrence4LeadingSquare_coeff_high (314 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (314 - (314 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_314 :
    recurrence4Scalar0Left.coeff 314 =
      -(((((604459489676475061250 * 10 ^ 70 +
        6889815953873099531780813115931409551038283967890931157361714736457021) * 10 ^ 70 +
        8372719197888357787674134551003341748602163872809034562929502870015087) * 10 ^ 70 +
        1161168286750204815513652809646154760423105401638719796615044789781062) * 10 ^ 70 +
        3620854674822507127493123139284649614199100897765239240131600184681712) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (314 - x)) = _
  rw [show 315 = 120 +
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
  rw [recurrence4Scalar0Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (315 + x) *
        remainder4Coefficient0.coeff (315 - (315 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 315 + x
  · rw [recurrence4LeadingSquare_coeff_high (315 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (315 - (315 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_315 :
    recurrence4Scalar0Left.coeff 315 =
      (((((386339429827012109196 * 10 ^ 70 +
        1676221583108625800173053679564540514078799611666493421099721703103655) * 10 ^ 70 +
        7653848594952677277322425611024861578026294153994262120042770954813621) * 10 ^ 70 +
        7217792892591656832698227490075658976739890679289983668521174266604931) * 10 ^ 70 +
        5540349388390043208210537672403332732226222693728867445097643749686616) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (315 - x)) = _
  rw [show 316 = 121 +
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
  rw [recurrence4Scalar0Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (316 + x) *
        remainder4Coefficient0.coeff (316 - (316 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 316 + x
  · rw [recurrence4LeadingSquare_coeff_high (316 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (316 - (316 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_316 :
    recurrence4Scalar0Left.coeff 316 =
      -(((((237279127513408087564 * 10 ^ 70 +
        8128819126499599731370244859126603993693682376494814302031229246931512) * 10 ^ 70 +
        2936421156911464485082352789491630237702313801784746080526048580207691) * 10 ^ 70 +
        5948867209890395641385217682173210192442287265215776454522481696836339) * 10 ^ 70 +
        3417967543084476121950235443056835441225257018278496895279388584189439) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (316 - x)) = _
  rw [show 317 = 122 +
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
  rw [recurrence4Scalar0Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (317 + x) *
        remainder4Coefficient0.coeff (317 - (317 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 317 + x
  · rw [recurrence4LeadingSquare_coeff_high (317 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (317 - (317 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_317 :
    recurrence4Scalar0Left.coeff 317 =
      (((((140702692186626200218 * 10 ^ 70 +
        4336092021099237866610518377063306291654540347813270783665362380207690) * 10 ^ 70 +
        7090059775494084386240294795701252163484598144980538353801170336862850) * 10 ^ 70 +
        2972443802975218317938506856763886724241487009987683095698255219499774) * 10 ^ 70 +
        5880262719830520744315073294675484852042351830851623072625219839179029) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (317 - x)) = _
  rw [show 318 = 123 +
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
  rw [recurrence4Scalar0Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (318 + x) *
        remainder4Coefficient0.coeff (318 - (318 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 318 + x
  · rw [recurrence4LeadingSquare_coeff_high (318 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (318 - (318 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_318 :
    recurrence4Scalar0Left.coeff 318 =
      -(((((80756852964960566310 * 10 ^ 70 +
        7479700885271767310521422804013785291615342482860744242668723900010312) * 10 ^ 70 +
        3603843312663939330732312701890575465067861311401223849712030501772113) * 10 ^ 70 +
        3543102955548877224667961792382451611654775761995690804404132579633674) * 10 ^ 70 +
        4252547311832524401681082553489577190806488210190691444984920650533664) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (318 - x)) = _
  rw [show 319 = 124 +
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
  rw [recurrence4Scalar0Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (345 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (345 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_345 :
    recurrence4Scalar0Left.coeff 345 =
      -(((((2174071252849 * 10 ^ 70 +
        5136278565625748124724528636074243445149153234926411779237523100990651) * 10 ^ 70 +
        1594627173207924547246562023256461921783604590565376187047444702683797) * 10 ^ 70 +
        4119808664863938648453568643113816243533964214694321297509800032211799) * 10 ^ 70 +
        6937707522608030192718512972817609373078921463252543131706158449574802) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (345 - x)) = _
  rw [show 346 = 151 +
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
    rw [show 35 = 18 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (346 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (346 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_346 :
    recurrence4Scalar0Left.coeff 346 =
      (((((973523457075 * 10 ^ 70 +
        2111822134557689477876094736300618663973584573800683126065205536121923) * 10 ^ 70 +
        6495346507180547604727762123739881485528110732517279932045493499031273) * 10 ^ 70 +
        9690338278867050930307090328978258713171292312692859712752549928771984) * 10 ^ 70 +
        7368040580351196046417345786863963402554853350582938248089438145052979) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (346 - x)) = _
  rw [show 347 = 152 +
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
    rw [show 35 = 17 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (347 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (347 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_347 :
    recurrence4Scalar0Left.coeff 347 =
      -(((((427793519862 * 10 ^ 70 +
        4920437206528805782890150152090342588248053689393461247127090673212451) * 10 ^ 70 +
        1077509034223973500140480053834407789038320799974743186679684037585695) * 10 ^ 70 +
        7460099068768605554791994226309980406818105767255528878710623150197669) * 10 ^ 70 +
        0395499892920491475331647328611603762768373871582705143153022047139863) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (347 - x)) = _
  rw [show 348 = 153 +
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
    rw [show 35 = 16 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (348 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (348 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_348 :
    recurrence4Scalar0Left.coeff 348 =
      (((((184445549952 * 10 ^ 70 +
        3353851148428168481038487286960034822077649365507170564519522097809304) * 10 ^ 70 +
        9478580844619689411678115905561093493578430971681584908430631465139622) * 10 ^ 70 +
        0386515098077089578083496235552128028104464394941209637904850822463199) * 10 ^ 70 +
        0099754184532925667144067126978093469389564150033916858284268414269139) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (348 - x)) = _
  rw [show 349 = 154 +
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
    rw [show 35 = 15 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (349 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (349 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_349 :
    recurrence4Scalar0Left.coeff 349 =
      -(((((78010202965 * 10 ^ 70 +
        2680630437295514941050820898605989377800930309247335621373730243983144) * 10 ^ 70 +
        6594224655342814286376522277923722346111045497183014031362455457065534) * 10 ^ 70 +
        8974037887703466149901650343810347646721517527970142932784528659786015) * 10 ^ 70 +
        2895497098032076075681887001782453125857105780942843937588351407352297) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (349 - x)) = _
  rw [show 350 = 155 +
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
    rw [show 35 = 14 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (350 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (350 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_350 :
    recurrence4Scalar0Left.coeff 350 =
      (((((32357043160 * 10 ^ 70 +
        5873421130801938932842679432299469476546432531850705447574554953169045) * 10 ^ 70 +
        1701787097866943969243880881934734296862762669237288243358116906918615) * 10 ^ 70 +
        2606443083129912528689201344238226532654340194331384917126581271271070) * 10 ^ 70 +
        9353485100844304146127999716353063257552454419201988246715085011314696) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (350 - x)) = _
  rw [show 351 = 156 +
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
    rw [show 35 = 13 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (351 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (351 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_351 :
    recurrence4Scalar0Left.coeff 351 =
      -(((((13158359632 * 10 ^ 70 +
        4869083774526562990702845797369915608861535153678452699483517736014067) * 10 ^ 70 +
        8353230983443218119438844779750933086960555975111221994262863215228470) * 10 ^ 70 +
        3428477850157762975133216857429652370588916721849880971627577481259806) * 10 ^ 70 +
        5770436180617873781096540496578926362015578306048215796106361160867998) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (351 - x)) = _
  rw [show 352 = 157 +
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
    rw [show 35 = 12 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (352 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (352 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_352 :
    recurrence4Scalar0Left.coeff 352 =
      (((((5245062776 * 10 ^ 70 +
        4476504684044945200052257246807436017075633218379762351109203073000468) * 10 ^ 70 +
        5287158584944157314536490756857575279261866787367383653464765293332486) * 10 ^ 70 +
        2665213288756935929434473375820576053191140949566076539649578705791689) * 10 ^ 70 +
        0336967113824366688438788362883739907436444690559966264822170264043684) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (352 - x)) = _
  rw [show 353 = 158 +
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
    rw [show 35 = 11 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (353 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (353 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_353 :
    recurrence4Scalar0Left.coeff 353 =
      -(((((2049144748 * 10 ^ 70 +
        2215899930669440249062661219896287585513453518922785892224850750315602) * 10 ^ 70 +
        8479115303305333343391333084777489736656745216895338132109125462410912) * 10 ^ 70 +
        1986314250715668993821729797974664848302157860565166262393485051283838) * 10 ^ 70 +
        4342775845749695623369468993960004050370053781234134080002198233404406) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (353 - x)) = _
  rw [show 354 = 159 +
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
    rw [show 35 = 10 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (354 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (354 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_354 :
    recurrence4Scalar0Left.coeff 354 =
      (((((784769803 * 10 ^ 70 +
        0542151327498200437760749114757997440463714844726625006514690704246326) * 10 ^ 70 +
        2588241613887524605088270174267154163423056632533037163658487969319417) * 10 ^ 70 +
        9476023681623261115151999501858408267243335891365770215495456343503025) * 10 ^ 70 +
        9727521381608154357659741731927216985709646634120661063525603044764191) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (354 - x)) = _
  rw [show 355 = 160 +
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
    rw [show 35 = 9 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (355 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (355 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_355 :
    recurrence4Scalar0Left.coeff 355 =
      -(((((294816277 * 10 ^ 70 +
        1939519838460979288105737111843814580521829674805064290806457534770150) * 10 ^ 70 +
        7197423432686303036755893108677424055452883273049380694103803833126369) * 10 ^ 70 +
        3862413073343955116582998665121287292313824929313497640354389005487879) * 10 ^ 70 +
        6579601145450741604484673180909477586130954124611806011839825521368361) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (355 - x)) = _
  rw [show 356 = 161 +
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
    rw [show 35 = 8 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (356 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (356 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_356 :
    recurrence4Scalar0Left.coeff 356 =
      (((((108809371 * 10 ^ 70 +
        9072160129930295473298608150288120742740615274251609733218283056199333) * 10 ^ 70 +
        0458490923591537522026228221261748537006832375805354914695760446772971) * 10 ^ 70 +
        1290309432685878897509950644395045708965223711099667222862410477937592) * 10 ^ 70 +
        8118937907821825220275778066634328403607054106795139780100346805218247) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (356 - x)) = _
  rw [show 357 = 162 +
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
    rw [show 35 = 7 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (357 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (357 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_357 :
    recurrence4Scalar0Left.coeff 357 =
      -(((((39569716 * 10 ^ 70 +
        7749201225464357294678628012303824184932660213214052147156175750598847) * 10 ^ 70 +
        8028784180717937662780822377969704173158477557235674320971847746359254) * 10 ^ 70 +
        3252111883233315749592225021074083532767603104939323243896265313691404) * 10 ^ 70 +
        4451567695267957818871087699814221496742857612161010674650128074619255) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (357 - x)) = _
  rw [show 358 = 163 +
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
    rw [show 35 = 6 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (358 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (358 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_358 :
    recurrence4Scalar0Left.coeff 358 =
      (((((14251035 * 10 ^ 70 +
        1313745301284706506954072525947243953020250733830100299138576010308652) * 10 ^ 70 +
        8492789023771460274140042166278263818217987472309260860611318553842143) * 10 ^ 70 +
        7444438680928220594596822386725434565421625893928321205998425974419250) * 10 ^ 70 +
        6967457640083000060539394971712517693812626971499580999013454518891980) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (358 - x)) = _
  rw [show 359 = 164 +
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
    rw [show 35 = 5 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (359 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (359 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_359 :
    recurrence4Scalar0Left.coeff 359 =
      -(((((5123840 * 10 ^ 70 +
        3483159881866652509982762903305333442801397376282137607858120676113944) * 10 ^ 70 +
        4835277926140854318706566109293979560879177473148890568719390365949758) * 10 ^ 70 +
        3925561283309611814096824109001585056777872876925917740969594148001377) * 10 ^ 70 +
        9585417083612840446906695214779411919585175254753463288427575028593309) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (359 - x)) = _
  rw [show 360 = 165 +
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
    rw [show 35 = 4 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (360 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (360 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_360 :
    recurrence4Scalar0Left.coeff 360 =
      (((((1860080 * 10 ^ 70 +
        3457422729727198983184105734277124927127364536851958453507524624467897) * 10 ^ 70 +
        9061491978812552972713426517403310113299720046141732827666785122954916) * 10 ^ 70 +
        2216434890787460568950382050365500715286063851248102485781718314178564) * 10 ^ 70 +
        9698011987550862447954601688441748451781882094429921777984374746091761) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (360 - x)) = _
  rw [show 361 = 166 +
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
    rw [show 35 = 3 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (361 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (361 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_361 :
    recurrence4Scalar0Left.coeff 361 =
      -(((((691207 * 10 ^ 70 +
        2064523341025470036700161891783890668225304320465465920032154077928611) * 10 ^ 70 +
        1123105775630509637298564788902969119320463169436925655501995119399677) * 10 ^ 70 +
        2120752308170619447039348563070700769372966977519222144303084443477879) * 10 ^ 70 +
        9571237393636929515509956585102614501819187116480327534101526707401266) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (361 - x)) = _
  rw [show 362 = 167 +
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
    rw [show 35 = 2 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (362 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (362 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_362 :
    recurrence4Scalar0Left.coeff 362 =
      (((((266332 * 10 ^ 70 +
        7600880152416258793560405096679990966019569550002860177004689952730475) * 10 ^ 70 +
        3491221393861671323216765535171814901180459527997516805393327938679642) * 10 ^ 70 +
        9844525022504373292915599286196399159550923498549635230080504018734577) * 10 ^ 70 +
        0643700561018746909887808285815946382066708615140079630395435107710218) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (362 - x)) = _
  rw [show 363 = 168 +
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
    rw [show 35 = 1 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (363 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (363 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_363 :
    recurrence4Scalar0Left.coeff 363 =
      -(((((107179 * 10 ^ 70 +
        6295969702721784767028290159417391863831559609367814940876000899306174) * 10 ^ 70 +
        3396904206272306742111364690960258375276021280368241711821710846750967) * 10 ^ 70 +
        4530299806309555030159435275301152153623370088104194376880094465962001) * 10 ^ 70 +
        6926823144448189134767105721818565116789339658629757918888744178581692) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (363 - x)) = _
  rw [show 364 = 169 +
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
  rw [recurrence4Scalar0Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (364 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (364 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_364 :
    recurrence4Scalar0Left.coeff 364 =
      (((((44957 * 10 ^ 70 +
        2277193203811340246809945992751657514362161341507523117254880074165831) * 10 ^ 70 +
        5701091681121040499635456301859549828534302409442448755313259731184356) * 10 ^ 70 +
        6938070990587653395624146166314698627577624535758246336075656067111602) * 10 ^ 70 +
        6656573970514758420962094794659978809081999775134321256555081832410967) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (364 - x)) = _
  rw [show 365 = 170 +
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
    rw [show 67 = 31 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (365 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (365 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_365 :
    recurrence4Scalar0Left.coeff 365 =
      -(((((19451 * 10 ^ 70 +
        4585697702724298151999663037517584743479212006216589490736592634881006) * 10 ^ 70 +
        2617156533033683597730398540813657431496361794033541757893712188578868) * 10 ^ 70 +
        2766090680149057275374279327995622764765102177822104541441494168374031) * 10 ^ 70 +
        3232134280522719102756757087125136438091743911785215214372908174777540) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (365 - x)) = _
  rw [show 366 = 171 +
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
    rw [show 67 = 30 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (366 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (366 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_366 :
    recurrence4Scalar0Left.coeff 366 =
      (((((8556 * 10 ^ 70 +
        1307084040756248859170911180550706123256055105655572109254589478177860) * 10 ^ 70 +
        0900791976439620385297189043619459476978045579074254611457971684780715) * 10 ^ 70 +
        6818291805477751504018471371467511676069350076099690549294771983004025) * 10 ^ 70 +
        4269743229331892580071191606174496465238166217521109815691936103509417) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (366 - x)) = _
  rw [show 367 = 172 +
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
    rw [show 67 = 29 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (367 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (367 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_367 :
    recurrence4Scalar0Left.coeff 367 =
      -(((((3772 * 10 ^ 70 +
        9432272938655342363530114188704130913665097833830845725525746720655484) * 10 ^ 70 +
        3264573586057182554977496955800665613711511024155439022528033706734273) * 10 ^ 70 +
        9411567689156151713195300830794385401576917703859114481506776448184402) * 10 ^ 70 +
        1979185989411426494780022812076191695155062580515748411818828699067078) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (367 - x)) = _
  rw [show 368 = 173 +
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
    rw [show 67 = 28 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (368 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (368 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_368 :
    recurrence4Scalar0Left.coeff 368 =
      (((((1649 * 10 ^ 70 +
        2608913705132371418929334300985681104154878743711635148163772741732524) * 10 ^ 70 +
        1754955286835089643935201961145490347839799010376444757139499742146533) * 10 ^ 70 +
        2171890073376212367350443166837354564374184197400936730456498960910274) * 10 ^ 70 +
        8916774804947390078964886939486316953221220885610832898073906699975891) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (368 - x)) = _
  rw [show 369 = 174 +
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
    rw [show 67 = 27 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (369 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (369 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_369 :
    recurrence4Scalar0Left.coeff 369 =
      -(((((708 * 10 ^ 70 +
        9305006583873124492985109378697117164870453731340425136755107386400671) * 10 ^ 70 +
        9641277262387931284395108834114994408687242654271778375508569367961960) * 10 ^ 70 +
        1157377299035703146874555567749282508678731306595975384733385572537731) * 10 ^ 70 +
        3622741730717055870682718678416731207120646002471179126540293025770519) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (369 - x)) = _
  rw [show 370 = 175 +
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
    rw [show 67 = 26 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (370 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (370 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_370 :
    recurrence4Scalar0Left.coeff 370 =
      (((((297 * 10 ^ 70 +
        9952268699893990495814903817319344873407958148791767314446431470757026) * 10 ^ 70 +
        6774471291710186745895776349152929791400118931203840821270284019381378) * 10 ^ 70 +
        2421844828724165525679402067206685533904955406096396202612972963181914) * 10 ^ 70 +
        6796113626162850258221696828634791168400102508416309265143045180093535) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (370 - x)) = _
  rw [show 371 = 176 +
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
    rw [show 67 = 25 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
