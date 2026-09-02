/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0MainPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

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
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
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

attribute [local simp]
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122
  recurrence4QuotientConstant_coeff_123
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

attribute [local simp]
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
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

attribute [local simp]
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_250
  recurrence4QuotientConstant_coeff_251
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

attribute [local simp]
  recurrence4QuotientConstant_coeff_309
  recurrence4QuotientConstant_coeff_310
  recurrence4QuotientConstant_coeff_311
  recurrence4QuotientConstant_coeff_312
  recurrence4QuotientConstant_coeff_313
  recurrence4QuotientConstant_coeff_314
  recurrence4QuotientConstant_coeff_315
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

private theorem recurrence4Scalar0Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (303 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (303 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_303 :
    recurrence4Scalar0Main.coeff 303 =
      -(((((111078813538045498134178 * 10 ^ 70 +
        8677765512531565530009819875068159235015676544681763256089196775289662) * 10 ^ 70 +
        4338921666306508713595575378658249075855633616416291598591654011188156) * 10 ^ 70 +
        2580251251442499763965988932996260560356733674127062536776941722816128) * 10 ^ 70 +
        6757800609184230672693926789063354156330831887373030581485962032859178) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (303 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (304 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (304 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_304 :
    recurrence4Scalar0Main.coeff 304 =
      (((((82018817251037684336264 * 10 ^ 70 +
        5929091192724838808011714161762788192866569453411299340274555895443272) * 10 ^ 70 +
        3309615799768768656034304272154709667620269356631919277242500634638624) * 10 ^ 70 +
        2429594745916105107666340999583965905365782354652531965889927987348999) * 10 ^ 70 +
        0357892822321212983839100652326147217057346563936091972707579202039159) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (304 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (305 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (305 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_305 :
    recurrence4Scalar0Main.coeff 305 =
      -(((((57336139153211440772763 * 10 ^ 70 +
        8435718425024741634750523530074414251071523455472226658994644715489018) * 10 ^ 70 +
        3613644646428161043906987354150260769563891175469887472858431393492984) * 10 ^ 70 +
        8720455505549727581520761422712992918785220494465710518372245243730118) * 10 ^ 70 +
        3335849961275475333182068235474871196769307078972173940401685889665953) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (305 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (306 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (306 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_306 :
    recurrence4Scalar0Main.coeff 306 =
      (((((38467194888837402115653 * 10 ^ 70 +
        1854805801827636201792026526061501275830835156734253307077471140426651) * 10 ^ 70 +
        5707549215714273035509327354962942947539236485131543245252027299078125) * 10 ^ 70 +
        8735376399001398285826767223986794250913395696671368095885713409611034) * 10 ^ 70 +
        4396690583766461512047141150133638531937128491602989242205377085377693) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (306 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (307 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (307 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_307 :
    recurrence4Scalar0Main.coeff 307 =
      -(((((24968971241726878932254 * 10 ^ 70 +
        8595221368633817671159249370242272714128219515904210251456802135471848) * 10 ^ 70 +
        1402021513432849688307191405211543468747366807248555798062227462982542) * 10 ^ 70 +
        0204321585486326368182076809489007228388693269689166746588249601989542) * 10 ^ 70 +
        5495179091972492202962485641513732896511797803608747865210369370024299) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (307 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (308 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (308 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_308 :
    recurrence4Scalar0Main.coeff 308 =
      (((((15762031548795338676648 * 10 ^ 70 +
        2114011299105661986665477212616353737706438651638620241351111930119433) * 10 ^ 70 +
        5606947575568265548366578948720567996684818819980315713748818975734608) * 10 ^ 70 +
        6782787819131230729945758845406352658589219905785944523779636029354804) * 10 ^ 70 +
        1656961124785966103717087254677926294410994628794202761801202905552911) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (308 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (309 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (309 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_309 :
    recurrence4Scalar0Main.coeff 309 =
      -(((((9711214639921587205327 * 10 ^ 70 +
        5335541961331792641181739702137288926998840593604500245445654531411461) * 10 ^ 70 +
        5638494228674869800132972888120202002926817579424655842353969079596390) * 10 ^ 70 +
        0982638799817992828301287765404831547020655318658638974601790559101881) * 10 ^ 70 +
        3337557894303768122367247228420258980319994191388377379729053438919203) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (309 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (310 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (310 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_310 :
    recurrence4Scalar0Main.coeff 310 =
      (((((5854805746344612140409 * 10 ^ 70 +
        5774093296924176695971097831182964817486758014253478770911533802486393) * 10 ^ 70 +
        7620763579773698954343955956246711971967969038311218607408113651265433) * 10 ^ 70 +
        4559575475455285635559739566773638298252201894536421238994942943520806) * 10 ^ 70 +
        6672770683069232382494218751963998060217053033372138107514802525494625) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (310 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (311 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (311 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_311 :
    recurrence4Scalar0Main.coeff 311 =
      -(((((3460996738315403120738 * 10 ^ 70 +
        4693103761886092323211124011925588516547898820336706140152679868108193) * 10 ^ 70 +
        3006775074882126653300974093358192701738410284788985102888684926052163) * 10 ^ 70 +
        9575364148765267584828598120967447592034756487093195706755220936260284) * 10 ^ 70 +
        6022059200360008514865278197975840373187541492848590667520210462186747) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (311 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (312 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (312 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_312 :
    recurrence4Scalar0Main.coeff 312 =
      (((((2009382175563633478846 * 10 ^ 70 +
        3709280676339966354660265564251865785106012327710971813082092428730364) * 10 ^ 70 +
        4940288973215779002167336917525042399320957851946990947224149059041552) * 10 ^ 70 +
        1906565637923740092151480020954008540653874338235424704094233071754050) * 10 ^ 70 +
        9889413933363900205076843705410344524996530624353861504670427140031677) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (312 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (313 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (313 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_313 :
    recurrence4Scalar0Main.coeff 313 =
      -(((((1147484285448696535356 * 10 ^ 70 +
        3043754522491883125352363677498880380537549386197247888958901910079477) * 10 ^ 70 +
        1302406245872566289296720734583965703507691882086149318641436262695635) * 10 ^ 70 +
        8820770552590450389763425803912340657453061926784107227293367364674611) * 10 ^ 70 +
        1138507653209809828665142807370742991102165105378120916807612708866953) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (313 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (314 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (314 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_314 :
    recurrence4Scalar0Main.coeff 314 =
      (((((645495581404073329867 * 10 ^ 70 +
        2772785141712157800532335205563299066140293060877188191266651641944273) * 10 ^ 70 +
        7727798812528648859756912489014858801142995195056328829667825752102128) * 10 ^ 70 +
        1912403407579162567480485139731591969487467516170064380571792560602551) * 10 ^ 70 +
        4654548332927390816359060304265558157413375726583233001855372648914908) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (314 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (315 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (315 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_315 :
    recurrence4Scalar0Main.coeff 315 =
      -(((((358249997323423513020 * 10 ^ 70 +
        7249459168469871739274956276169164128714648593402196143427506538640457) * 10 ^ 70 +
        0993431456370274135551381965383142531598416055694015067790546905144320) * 10 ^ 70 +
        8796637113475539716624423452282885240971707500107512152570991934263619) * 10 ^ 70 +
        7629731612280373664863733451532975861748467344562648513604947753472166) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (315 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (316 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (316 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_316 :
    recurrence4Scalar0Main.coeff 316 =
      (((((196519634645896512827 * 10 ^ 70 +
        8205298588034154363846956514542302824189985348080868535122568168746031) * 10 ^ 70 +
        4066025465607033313425748945440225377237953794957067437785386926482707) * 10 ^ 70 +
        3769149241926929743092324543470182466638863387704298533687144407510006) * 10 ^ 70 +
        5091040101453408860047663429950781565431075428141855599775352937172231) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (316 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (317 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (317 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_317 :
    recurrence4Scalar0Main.coeff 317 =
      -(((((106776673191604576864 * 10 ^ 70 +
        1380753688051804974647516859096209770837954783179446970485880511952300) * 10 ^ 70 +
        9348151771218028194183848888353306723953761063577510141745713751625492) * 10 ^ 70 +
        4187970073737748772581733871274529534564716517550727680661685320958447) * 10 ^ 70 +
        4317874816066275774896164620590571119399411566252638608638669652001284) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (317 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (318 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (318 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_318 :
    recurrence4Scalar0Main.coeff 318 =
      (((((57610383413981833400 * 10 ^ 70 +
        7933327879043746425288298756359608284095485478980337326116642852718732) * 10 ^ 70 +
        2255501889850190922919218139445031773595093335468173691423028684432144) * 10 ^ 70 +
        0220753362843478640931513173140514474636036917857139908467469209334850) * 10 ^ 70 +
        5651980621701468176463800058503131644539810114795787779262584347163882) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (318 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (319 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (319 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_319 :
    recurrence4Scalar0Main.coeff 319 =
      -(((((30958097155528230078 * 10 ^ 70 +
        7858375345093829489310279095691871928644198548898365844469607973209105) * 10 ^ 70 +
        6914208780869479156201800759889666853667484634809671624620645165604166) * 10 ^ 70 +
        5948344713607108179145944576161622187918612707105818356612959420190239) * 10 ^ 70 +
        3650586289201891391620885606626650287229868820997750958992212581619314) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (319 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (320 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (320 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_320 :
    recurrence4Scalar0Main.coeff 320 =
      (((((16624753873284471845 * 10 ^ 70 +
        4329029895554772450783938411259680846237828172101341223185651270919539) * 10 ^ 70 +
        8641586970130280991177223289098876822278446096522686507250114758904273) * 10 ^ 70 +
        0743545332888018190669429286344392492131493294039482569998545793156133) * 10 ^ 70 +
        5821926979027039615824782088115356964694437677746687171778052734300963) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (320 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (321 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (321 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_321 :
    recurrence4Scalar0Main.coeff 321 =
      -(((((8953172881090783493 * 10 ^ 70 +
        4009486032316554850560417882071775192299752508289244141208348064938647) * 10 ^ 70 +
        8807306600769249106976843702309529961489557918062268416789779761272416) * 10 ^ 70 +
        1895925108679886962916234832167012728820072951404322423353138098312249) * 10 ^ 70 +
        9712956281715955697908296047594671985157877040940530559483501220176941) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (321 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (322 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (322 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_322 :
    recurrence4Scalar0Main.coeff 322 =
      (((((4851680400047337302 * 10 ^ 70 +
        6236101608266855298702604040894710107966339737507887470417043505318495) * 10 ^ 70 +
        1786761385267240171155401928401928826750658539003209815914082072089175) * 10 ^ 70 +
        5489420439055363395236079381390288459246503074805610506154088698198136) * 10 ^ 70 +
        2547007914778883104656668914581131928792700258679154268181258543796495) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (322 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (323 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (323 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_323 :
    recurrence4Scalar0Main.coeff 323 =
      -(((((2652572313993869432 * 10 ^ 70 +
        3876807110247685232639841174988882158099150320374095877065488958319502) * 10 ^ 70 +
        4669424573320442749976488658550255195132851834697593235674638237874751) * 10 ^ 70 +
        6938578877910529370654940660074409399899772603738771912828278648218436) * 10 ^ 70 +
        2053744777083973454133550122453995350075559002492489174303064652343841) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (323 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (324 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (324 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_324 :
    recurrence4Scalar0Main.coeff 324 =
      (((((1465467680961098030 * 10 ^ 70 +
        6771369106946290862594632688514884980056229420321250938691755815631840) * 10 ^ 70 +
        0889380237756859918232649660361858311185038202076947046637862420857601) * 10 ^ 70 +
        4644046644102379606177953907948771066902825110277470334429103783812923) * 10 ^ 70 +
        9929650028627591943773013710176617127448741184127940362742388476353423) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (324 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (325 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (325 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_325 :
    recurrence4Scalar0Main.coeff 325 =
      -(((((818209732884394916 * 10 ^ 70 +
        0741800085181816027836436233597902010983878775475021692614382805486392) * 10 ^ 70 +
        7179938124958185308984864581737681098645306895668596327953756802650177) * 10 ^ 70 +
        1530086053821339909228216229459394315574378524518815884799008858151335) * 10 ^ 70 +
        5131768846998606225644849653299273819270453139618481291315353347678003) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (325 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (326 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (326 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_326 :
    recurrence4Scalar0Main.coeff 326 =
      (((((461038087234618026 * 10 ^ 70 +
        1313090122305773921245031369669702359385800393985156058661254930080440) * 10 ^ 70 +
        7850032133566574182477009770656860937463833710544932664480121925141450) * 10 ^ 70 +
        3049988834349893805576425715459608449831404747776410055172424004756747) * 10 ^ 70 +
        5942492655436142981969483393456857624561320247580108168609899977000367) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (326 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (327 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (327 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_327 :
    recurrence4Scalar0Main.coeff 327 =
      -(((((261501275415638026 * 10 ^ 70 +
        1019717520759204154250282847704894409204028547018500923133627280577412) * 10 ^ 70 +
        6932312302215502516979111200555828814515256874435909781053620107683913) * 10 ^ 70 +
        9200486080933578579456093780606601904196194235418435246821005026722690) * 10 ^ 70 +
        8872339696920370650890558446997462708276591996180746801144360245201747) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (327 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (328 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (328 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_328 :
    recurrence4Scalar0Main.coeff 328 =
      (((((148810791872770289 * 10 ^ 70 +
        8932516608052616981045198457249838548669877432377242103765220336760227) * 10 ^ 70 +
        1947682671908948016001774947947611408719301309359884328714583081490125) * 10 ^ 70 +
        5512337935894245183478966821341790878942415597122948285965851518897909) * 10 ^ 70 +
        7550599524028479612033841940348523836398075968236620195333415370190637) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (328 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
