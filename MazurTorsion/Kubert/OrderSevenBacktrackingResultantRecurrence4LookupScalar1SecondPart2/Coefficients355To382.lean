/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
