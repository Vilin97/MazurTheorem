/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_1
  recurrence4A1_coeff_10
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_11
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_12
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_13
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_14
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_15
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156

attribute [local simp]
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_16
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_163
  recurrence4A1_coeff_164
  recurrence4A1_coeff_165
  recurrence4A1_coeff_166
  recurrence4A1_coeff_167
  recurrence4A1_coeff_168
  recurrence4A1_coeff_169
  recurrence4A1_coeff_17
  recurrence4A1_coeff_170
  recurrence4A1_coeff_171
  recurrence4A1_coeff_172
  recurrence4A1_coeff_173
  recurrence4A1_coeff_174
  recurrence4A1_coeff_175
  recurrence4A1_coeff_176
  recurrence4A1_coeff_177
  recurrence4A1_coeff_178
  recurrence4A1_coeff_179
  recurrence4A1_coeff_18
  recurrence4A1_coeff_180
  recurrence4A1_coeff_181
  recurrence4A1_coeff_182
  recurrence4A1_coeff_183
  recurrence4A1_coeff_184
  recurrence4A1_coeff_185
  recurrence4A1_coeff_186
  recurrence4A1_coeff_187
  recurrence4A1_coeff_188
  recurrence4A1_coeff_189
  recurrence4A1_coeff_19
  recurrence4A1_coeff_190
  recurrence4A1_coeff_2
  recurrence4A1_coeff_20
  recurrence4A1_coeff_21
  recurrence4A1_coeff_22
  recurrence4A1_coeff_23
  recurrence4A1_coeff_24
  recurrence4A1_coeff_25
  recurrence4A1_coeff_26
  recurrence4A1_coeff_27
  recurrence4A1_coeff_28
  recurrence4A1_coeff_29
  recurrence4A1_coeff_3
  recurrence4A1_coeff_30
  recurrence4A1_coeff_31
  recurrence4A1_coeff_32
  recurrence4A1_coeff_33
  recurrence4A1_coeff_34
  recurrence4A1_coeff_35
  recurrence4A1_coeff_36
  recurrence4A1_coeff_37
  recurrence4A1_coeff_38
  recurrence4A1_coeff_39
  recurrence4A1_coeff_4
  recurrence4A1_coeff_40
  recurrence4A1_coeff_41
  recurrence4A1_coeff_42

attribute [local simp]
  recurrence4A1_coeff_43
  recurrence4A1_coeff_44
  recurrence4A1_coeff_45
  recurrence4A1_coeff_46
  recurrence4A1_coeff_47
  recurrence4A1_coeff_48
  recurrence4A1_coeff_49
  recurrence4A1_coeff_5
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_6
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68
  recurrence4A1_coeff_69
  recurrence4A1_coeff_7
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_8
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_9
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_226
  recurrence4LeadingSquare_coeff_227
  recurrence4LeadingSquare_coeff_228
  recurrence4LeadingSquare_coeff_229

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_290
  recurrence4LeadingSquare_coeff_291
  recurrence4LeadingSquare_coeff_292
  recurrence4LeadingSquare_coeff_293

attribute [local simp]
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

private theorem recurrence4Scalar1Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (351 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (351 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_351 :
    recurrence4Scalar1Left.coeff 351 =
      -(((((120286399 * 10 ^ 70 +
        0795038765951331920897207116586230168831949434851944686391246222478535) * 10 ^ 70 +
        3170646420601931149474393535555852897975475092641430907566193859481786) * 10 ^ 70 +
        9931412122058466957116036521421166058537805424629585413411461700837005) * 10 ^ 70 +
        4305759525204934575818925362936159859111166508380130147864848546677256) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (351 - x)) = _
  rw [show 352 = 161 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 8 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (352 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (352 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_352 :
    recurrence4Scalar1Left.coeff 352 =
      (((((39750395 * 10 ^ 70 +
        4895933724983486957291997673262798359616458752261978712710696761109721) * 10 ^ 70 +
        9690490479356282465846809456540700770584571548990898758513610632271569) * 10 ^ 70 +
        8000131154726115542605536590617349564753545793296735355571021421996366) * 10 ^ 70 +
        7098130896101350151410972019116849254807403306547578922430607669640692) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (352 - x)) = _
  rw [show 353 = 162 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 7 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (353 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (353 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_353 :
    recurrence4Scalar1Left.coeff 353 =
      -(((((12508380 * 10 ^ 70 +
        3822864057199264277008250289671112121936538592286236274624506262232969) * 10 ^ 70 +
        5211538758935952474923407541051599852913536618931787936836206180221562) * 10 ^ 70 +
        7353066898691548108641884256060364851509696060621916698499939876936286) * 10 ^ 70 +
        2729635835965326414801694891989242667758055331427046977876244108740500) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (353 - x)) = _
  rw [show 354 = 163 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 6 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (354 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (354 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_354 :
    recurrence4Scalar1Left.coeff 354 =
      (((((3702217 * 10 ^ 70 +
        6048683527745052234162796340102877244477409361896842778672857778717918) * 10 ^ 70 +
        1378792908939720899282292590522060747821464216169142366910998601633874) * 10 ^ 70 +
        4094045549776260302174692562376838102045154190706934251941268141948537) * 10 ^ 70 +
        2025915748261855018581452350036285005549716742193880653700831481580424) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (354 - x)) = _
  rw [show 355 = 164 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 5 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (355 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (355 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_355 :
    recurrence4Scalar1Left.coeff 355 =
      -(((((1008821 * 10 ^ 70 +
        7078188887706410615125952080603839580566535273510190276019296667627549) * 10 ^ 70 +
        6960559706073206808417326886987555289086788853897984522955492491276380) * 10 ^ 70 +
        2463867411540786945414342065290589124853637392750252316664262986739641) * 10 ^ 70 +
        9796620994238398601359577760997012736139317986644669469303511475087798) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (355 - x)) = _
  rw [show 356 = 165 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 4 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (356 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (356 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_356 :
    recurrence4Scalar1Left.coeff 356 =
      (((((242040 * 10 ^ 70 +
        2734782211184569437857577781202285894705612270552190508367122430379784) * 10 ^ 70 +
        0028154159435781260643288699911717190929129712933786682421754260334678) * 10 ^ 70 +
        1676746829210537340907688805310085752698742612835737999207864014248562) * 10 ^ 70 +
        2490027564600020418600592700262679685594937268070513437958773365609253) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (356 - x)) = _
  rw [show 357 = 166 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 3 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (357 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (357 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_357 :
    recurrence4Scalar1Left.coeff 357 =
      -(((((45009 * 10 ^ 70 +
        6429947153173596642186269220382339193702331069644871908110180211754309) * 10 ^ 70 +
        5437867231745068921048131476961172457100290874897304264304708309123095) * 10 ^ 70 +
        4084372780516176027991563013797734349523731932984732734297868879569307) * 10 ^ 70 +
        6214594004021226323401238639367265695268880671683511417937432467036382) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (357 - x)) = _
  rw [show 358 = 167 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 2 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (358 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (358 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_358 :
    recurrence4Scalar1Left.coeff 358 =
      (((((2522 * 10 ^ 70 +
        5473627353250655218723292126653984080577593569814931331138311581748910) * 10 ^ 70 +
        0444941501286623502366299094756145390640184595435028412202557925316629) * 10 ^ 70 +
        4934388009095920273739962114443318195907046866293496653586532263007504) * 10 ^ 70 +
        3975382954877129045779227158368187865542959522070001823308692916198060) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (358 - x)) = _
  rw [show 359 = 168 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 1 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (359 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (359 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_359 :
    recurrence4Scalar1Left.coeff 359 =
      (((((3285 * 10 ^ 70 +
        4684946195347600780689717787337192974115760272326855531161497617592677) * 10 ^ 70 +
        2657269964132117130598035816083669645967009490513332630595355675830421) * 10 ^ 70 +
        4997378310377322136942044040915842153600781778704523429889560306326127) * 10 ^ 70 +
        7924246084221425929490450624078068886351293727272941451913070811766492) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (359 - x)) = _
  rw [show 360 = 169 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (360 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (360 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_360 :
    recurrence4Scalar1Left.coeff 360 =
      -(((((2439 * 10 ^ 70 +
        7111159326811674972724991872578269905493061166865976424188110402557158) * 10 ^ 70 +
        3074489799371091814897727583871586782218233510271723569857200208303280) * 10 ^ 70 +
        3891078606433710878959895989243387948028255039710995342413589973639094) * 10 ^ 70 +
        6170694491980429154087177133016560504498613421222209562296117700433462) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (360 - x)) = _
  rw [show 361 = 170 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 31 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (361 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (361 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_361 :
    recurrence4Scalar1Left.coeff 361 =
      (((((1281 * 10 ^ 70 +
        3026419537936591367750635730823830446013824065819929617539404729556377) * 10 ^ 70 +
        7304228034957503374529507168804816981553333071287055169521268315195512) * 10 ^ 70 +
        7748175043383812473894076592194591863238353949179435229586782521382848) * 10 ^ 70 +
        2303240187442587373866573187221444245734640933006675074770160394215236) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (361 - x)) = _
  rw [show 362 = 171 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 30 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (362 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (362 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_362 :
    recurrence4Scalar1Left.coeff 362 =
      -(((((618 * 10 ^ 70 +
        3292519100409134695379961765047851174977949146156796973109956338415372) * 10 ^ 70 +
        2534400982492667807980671999130790049404194875826922639465879359774619) * 10 ^ 70 +
        3167358378072989183394801113263746305513584599206997751924099929364351) * 10 ^ 70 +
        5578251181237359865942095772817200443247309388406649831480544131453476) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (362 - x)) = _
  rw [show 363 = 172 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 29 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (363 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (363 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_363 :
    recurrence4Scalar1Left.coeff 363 =
      (((((299 * 10 ^ 70 +
        0998890255914638537770806959875256440834070846262967403238745649121076) * 10 ^ 70 +
        9899227803492068755333069395650921599742571367950437779399482921441886) * 10 ^ 70 +
        2453320011613009020037094819290724536292193682102333584060421844048833) * 10 ^ 70 +
        4014332220827166327012822261110088958210302619303569366077173062668323) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (363 - x)) = _
  rw [show 364 = 173 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 28 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (364 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (364 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_364 :
    recurrence4Scalar1Left.coeff 364 =
      -(((((149 * 10 ^ 70 +
        2606646650913087244911236140376805647780768877393350541769153505836551) * 10 ^ 70 +
        2135858228637600966357641320988686250058814036674464656472041011941957) * 10 ^ 70 +
        5156535097862686436428054144577499623781145062512414108866966119449214) * 10 ^ 70 +
        4876434431694021772123593735037298874877611465426583708012508290779253) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (364 - x)) = _
  rw [show 365 = 174 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 27 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (365 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (365 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_365 :
    recurrence4Scalar1Left.coeff 365 =
      (((((76 * 10 ^ 70 +
        3273487151685051300598831661791858694525140396988790013458473645254696) * 10 ^ 70 +
        8723640428857386799950804889451816770789325948192003177053961344549762) * 10 ^ 70 +
        4735118820421107204108316104921710323682788372439066977935644872503208) * 10 ^ 70 +
        8391588697333888273031927034784870641324403565952339767078465772921561) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (365 - x)) = _
  rw [show 366 = 175 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 26 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (366 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (366 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_366 :
    recurrence4Scalar1Left.coeff 366 =
      -(((((39 * 10 ^ 70 +
        1468758905629910596849839831366868032581380920786593813955763412233008) * 10 ^ 70 +
        1828221700820030429265598331883316203270814611207625271838883513311025) * 10 ^ 70 +
        2547741186217554787974569181990505064485556528137173635268972292808932) * 10 ^ 70 +
        9183851681381670201569228756034977831936617308229891764734093797797269) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (366 - x)) = _
  rw [show 367 = 176 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 25 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (367 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (367 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_367 :
    recurrence4Scalar1Left.coeff 367 =
      (((((19 * 10 ^ 70 +
        7336275690798807945599269190305428904004797835404189367305271988838503) * 10 ^ 70 +
        8741989554930283786392657351603025519575230724431383274503286923079820) * 10 ^ 70 +
        2802369499066589427466513298936511507868580259595788215871963328752084) * 10 ^ 70 +
        0644222007873088859592204207811773614894422035530570831033817477871954) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (367 - x)) = _
  rw [show 368 = 177 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 24 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (368 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (368 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_368 :
    recurrence4Scalar1Left.coeff 368 =
      -(((((9 * 10 ^ 70 +
        6465043000196833101638524330239864479766768207671266510395801052487523) * 10 ^ 70 +
        3761360259714485838332306918138413099587472761014650766202639963005127) * 10 ^ 70 +
        2838594862038518218738535975113015699004737080823063307020211020543760) * 10 ^ 70 +
        0370861328728594211005818480910128939754373468487102295575729516102141) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (368 - x)) = _
  rw [show 369 = 178 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 23 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (369 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (369 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_369 :
    recurrence4Scalar1Left.coeff 369 =
      (((((4 * 10 ^ 70 +
        5389401878868888227414780227184253382070741584795134157710049474816653) * 10 ^ 70 +
        1928043833073265087657853752866389282218341066489388010794865675287128) * 10 ^ 70 +
        2598793490802050409125458690862019509046199794408810721424568710058378) * 10 ^ 70 +
        6618617878232280657264859288218716680842946654166920191159499713367884) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (369 - x)) = _
  rw [show 370 = 179 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 22 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (370 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (370 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_370 :
    recurrence4Scalar1Left.coeff 370 =
      -(((((2 * 10 ^ 70 +
        0479733218762221458447180188128221889762229455988177374945681634988599) * 10 ^ 70 +
        7343267896931898430714429283376078668804392859571180372040668848072189) * 10 ^ 70 +
        2418620621461948136756500304630196610965698007171591761418423784788696) * 10 ^ 70 +
        7370229509365208150520678304248380806224991048329319980559809676390267) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (370 - x)) = _
  rw [show 371 = 180 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 21 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (371 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (371 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_371 :
    recurrence4Scalar1Left.coeff 371 =
      ((((8843006645530847008283591501381994255816421574603555224117913879215202 * 10 ^ 70 +
        9636131120485547244753483961918262721168067547225524532880930659226610) * 10 ^ 70 +
        8012860776328367651443428520480373108089372773896509990992763740177727) * 10 ^ 70 +
        0844914282464492881664292484368015765477574926469148255332622315101696) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (371 - x)) = _
  rw [show 372 = 181 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 20 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (372 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (372 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_372 :
    recurrence4Scalar1Left.coeff 372 =
      -((((3648382073412333222061561348652906840256521808867092491287770212749070 * 10 ^ 70 +
        7240413498609567050821700023362432779178341824701445608935046649377637) * 10 ^ 70 +
        5586701636989314276186645498549090123957202742767383381015591983536592) * 10 ^ 70 +
        4891286175216737993559677057345066343741104546926511948948937144546611) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (372 - x)) = _
  rw [show 373 = 182 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 19 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (373 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (373 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_373 :
    recurrence4Scalar1Left.coeff 373 =
      ((((1435361067908708978519196850778050859103179526633042196374572991383475 * 10 ^ 70 +
        8470723994943814647364911403169693295245344660306176237253268604766895) * 10 ^ 70 +
        3566002918688584564743675700297277429384642273002852269873417836730392) * 10 ^ 70 +
        1314461527100605539055434015342209642703763886775615503848465719335187) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (373 - x)) = _
  rw [show 374 = 183 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 18 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (374 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (374 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_374 :
    recurrence4Scalar1Left.coeff 374 =
      -((((536784570330817203783269972957417230245697976627476645565931969367078 * 10 ^ 70 +
        5350571527158693427593424886505071546125563152288390378816938253707857) * 10 ^ 70 +
        1385460374595518709148559526998680397926687702365799340621817638895141) * 10 ^ 70 +
        3826748285161867671589983929755363021271738758555721391840691888070940) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (374 - x)) = _
  rw [show 375 = 184 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 17 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (375 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (375 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_375 :
    recurrence4Scalar1Left.coeff 375 =
      ((((189793332144890435190517802965787706757234988976009536977860560593633 * 10 ^ 70 +
        8017998170692158779341176962781789707305335671078780376434657519894958) * 10 ^ 70 +
        3486344398812608423256787257906251838188553179460854119967674293196670) * 10 ^ 70 +
        8165234753002904511137324815335811951801777863260907092789586762632005) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (375 - x)) = _
  rw [show 376 = 185 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 16 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (376 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (376 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_376 :
    recurrence4Scalar1Left.coeff 376 =
      -((((62854138855448405342118671084633626610654951268749638312312524898154 * 10 ^ 70 +
        7815946378458163527052963659437132901315476230760947871183191329877763) * 10 ^ 70 +
        9376289580230863958256638946437135427206097973769861535385937327969902) * 10 ^ 70 +
        2532164795404017709461322435853553916236266707364159162334449599573608) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (376 - x)) = _
  rw [show 377 = 186 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 15 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (377 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (377 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_377 :
    recurrence4Scalar1Left.coeff 377 =
      ((((19160771257707081781073292680202174845763607484571715127607680662851 * 10 ^ 70 +
        8157120390339633258717415796223669776706272047452964839076459144360447) * 10 ^ 70 +
        5781648981856297595764885333483262565403136559220271211981661493914946) * 10 ^ 70 +
        4649280921232186415501905639390271782096058074411047213253144588036517) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (377 - x)) = _
  rw [show 378 = 187 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 14 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
