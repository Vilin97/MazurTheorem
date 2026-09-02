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

private theorem recurrence4Scalar2First_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (302 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (302 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_302 :
    recurrence4Scalar2First.coeff 302 =
      (((((2350978343293408902296 * 10 ^ 70 +
        7163060501467373884676347968970682674660052954119809068814467580772260) * 10 ^ 70 +
        4950806937452944378627758335956572872439535482241189462026751273038912) * 10 ^ 70 +
        0894596023779738591297861204567308654038324143865498455605342054129033) * 10 ^ 70 +
        2861332333903759709682256132750388855848419607738096334084413446727645) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (302 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (303 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (303 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_303 :
    recurrence4Scalar2First.coeff 303 =
      -(((((1142445933958270856080 * 10 ^ 70 +
        6189117464907327396474437662638815873402024824106559378994512589369965) * 10 ^ 70 +
        6716244149757620813264487749522673122218809068434011599324123940172232) * 10 ^ 70 +
        1225650972587925838756062511928115268527448715847643389234094758940984) * 10 ^ 70 +
        4193012967631853103430248890338698232284665699600919872320575530088266) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (303 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (304 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (304 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_304 :
    recurrence4Scalar2First.coeff 304 =
      (((((513257842877035667169 * 10 ^ 70 +
        5116332066180545693473164763988234349189493144626860526216856558124411) * 10 ^ 70 +
        9191505994385226949299197026915149402637291903002707611206527622120133) * 10 ^ 70 +
        9931851593348198742090231656623470215744386433383503362645072258637218) * 10 ^ 70 +
        0155249839025789618370072573761645714007452441936354447344173965417815) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (304 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (305 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (305 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_305 :
    recurrence4Scalar2First.coeff 305 =
      -(((((202432317926400756013 * 10 ^ 70 +
        1268296256813452016722577912520966998692052550820021215699134375910898) * 10 ^ 70 +
        0310396166259748148197511680477503439731382590736878045382361997515836) * 10 ^ 70 +
        2471246800982139761041442919583500357936532674109132164158182309476228) * 10 ^ 70 +
        3308876753659305524457653658900141048279376053573101496489600562623912) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (305 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (306 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (306 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_306 :
    recurrence4Scalar2First.coeff 306 =
      (((((59545950052908872125 * 10 ^ 70 +
        6188488877064029856414702659063856319890881313232066908408625219022113) * 10 ^ 70 +
        8963275732120557441254501101358403425836710963719054572125089470252908) * 10 ^ 70 +
        3127146222733715329358285154855839176917551379940273215330812012021387) * 10 ^ 70 +
        3661863800822207912798334676162869162364356870506046308354148725453141) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (306 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (307 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (307 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_307 :
    recurrence4Scalar2First.coeff 307 =
      -(((((918872566419590201 * 10 ^ 70 +
        6257421017316979899330844670887879514005137994218459007664998587151429) * 10 ^ 70 +
        4400435268018476296104487361836897491769113821091940435812546776764251) * 10 ^ 70 +
        5545524385932345067341733535721696051010697309014796510670596941075357) * 10 ^ 70 +
        3282987188148124616950899586831788131336940176365903754636404488860275) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (307 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (308 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (308 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_308 :
    recurrence4Scalar2First.coeff 308 =
      -(((((18163917094428496012 * 10 ^ 70 +
        5554579324897153825661062214191793880506950778505202422884864661434277) * 10 ^ 70 +
        4563475499125782668286855104030010920123046027343403224664242304658665) * 10 ^ 70 +
        1230408942281665546379347043145332587866001738432048507300400368243444) * 10 ^ 70 +
        0970288347573825805510433011041466253752996505579393980351535070784930) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (308 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (309 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (309 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_309 :
    recurrence4Scalar2First.coeff 309 =
      (((((20470094292645426314 * 10 ^ 70 +
        3901815900904452186138061772462989759080370668412352188427135074507216) * 10 ^ 70 +
        0062677902969095992032604638251047752658735402835473258502991450968853) * 10 ^ 70 +
        6966439460178583492080155625035918138293293511298620892731800682421144) * 10 ^ 70 +
        2108272522069941916941849345707861459931277801307709583828652800043671) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (309 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (310 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (310 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_310 :
    recurrence4Scalar2First.coeff 310 =
      -(((((16888889723697081027 * 10 ^ 70 +
        5519423857492563217287579025222216544259353855963105621497452388587543) * 10 ^ 70 +
        3452877782694317978455362163226640552867134059011293141195095318765364) * 10 ^ 70 +
        2228849650489787615071859479449964984591221840223288144349374254224902) * 10 ^ 70 +
        3472380008907804625612666990501585808180378895033817700095681236792687) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (310 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (311 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (311 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_311 :
    recurrence4Scalar2First.coeff 311 =
      (((((12175168216780580082 * 10 ^ 70 +
        7735052475375846848082053269772873398716941647172002690693294016802110) * 10 ^ 70 +
        0060548593976345109742375328250887694236513533312386660294216915681944) * 10 ^ 70 +
        8518585240903512282339098451346565936847761413448978343096549522410792) * 10 ^ 70 +
        3299629090701935298037545094063041412226022766044300528658757293064812) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (311 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (312 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (312 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_312 :
    recurrence4Scalar2First.coeff 312 =
      -(((((8098143510143236684 * 10 ^ 70 +
        8055840793919836154445646217815034629562610609510234212389316809357907) * 10 ^ 70 +
        7914938651684249482273063947582934467915648728903257245833558909907031) * 10 ^ 70 +
        9911996994905186649353123174817590950434037506542993558143264393238467) * 10 ^ 70 +
        3206753206571144868466872498849312856774012924364887256399539600408941) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (312 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (313 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (313 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_313 :
    recurrence4Scalar2First.coeff 313 =
      (((((5089910867474364990 * 10 ^ 70 +
        5958993229029433504712860778693664250830574097421726727796508882702018) * 10 ^ 70 +
        0702469414396354375558201316491003897047941727526738805149179111356111) * 10 ^ 70 +
        0612399222333256161029809408980566833754241737177893533107215260573602) * 10 ^ 70 +
        0016663649130031015753005377266830233171205456675176556419881083968583) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (313 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (314 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (314 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_314 :
    recurrence4Scalar2First.coeff 314 =
      -(((((3061016630163676945 * 10 ^ 70 +
        6323744787306049395997734615059879128942193621677252199730014036861232) * 10 ^ 70 +
        7750302883643697325871364152096307436905355418590636286888252400795970) * 10 ^ 70 +
        0385507372902447655787983649318208583934310755747992944421519099716440) * 10 ^ 70 +
        4078539531312252468849473459427664676259452939654329796143731181015021) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (314 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (315 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (315 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_315 :
    recurrence4Scalar2First.coeff 315 =
      (((((1774040278527762005 * 10 ^ 70 +
        0292318901181587883851879098927579324341860201964239288604515350058777) * 10 ^ 70 +
        5211586592983144173276340280996551099907607760428291578135902095277738) * 10 ^ 70 +
        8313382364787040094594529424194805787432850385129402814562844018316874) * 10 ^ 70 +
        7638375202161871710010947221637019081628489480757983650312684542406562) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (315 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (316 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (316 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_316 :
    recurrence4Scalar2First.coeff 316 =
      -(((((995115844259452310 * 10 ^ 70 +
        5661644728926828482527323196400277508459047395278126501995212677982428) * 10 ^ 70 +
        9856195254095109285600271049617787676644763817025741964474431158432181) * 10 ^ 70 +
        9234531170326314234032738841914581746771639463040832993902769436871876) * 10 ^ 70 +
        2465935207341608233172134466723801721628067849554556159780500457204218) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (316 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (317 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (317 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_317 :
    recurrence4Scalar2First.coeff 317 =
      (((((541642068458239220 * 10 ^ 70 +
        6421351687260349497718295915418039028318658498777710162511897149468522) * 10 ^ 70 +
        4346553112788279220203100304780687694471384015436694562606641836443757) * 10 ^ 70 +
        0434344717923347784931325824036924734414640673335764747607697885600532) * 10 ^ 70 +
        4646708304203300676387846411567552724929279031570201740855459997473192) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (317 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (318 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (318 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_318 :
    recurrence4Scalar2First.coeff 318 =
      -(((((286471377129265032 * 10 ^ 70 +
        0232206181320273295885859723497760320439783158904899453961232627744390) * 10 ^ 70 +
        4218283091504140010376187929121870211842254082640263558792290240122494) * 10 ^ 70 +
        0602326130990485902307349829943443883189666056446954676348079013125777) * 10 ^ 70 +
        0543611629966592362910480495935216025157407742955420862299655000767277) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (318 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (319 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (319 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_319 :
    recurrence4Scalar2First.coeff 319 =
      (((((147292756183363980 * 10 ^ 70 +
        4160840229423160112691425548338441018038695294080599370871497031185115) * 10 ^ 70 +
        9235743449153701602191340192580183420142632515001930807406207448716202) * 10 ^ 70 +
        4894639041699539348210191129840045187098083022490561590658269737315904) * 10 ^ 70 +
        7761627147008659210908805553878846132150657902327603711768984909725967) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (319 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (320 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (320 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_320 :
    recurrence4Scalar2First.coeff 320 =
      -(((((73595646832986639 * 10 ^ 70 +
        4968378449120169232205436158248773434206101122911373597626612233759666) * 10 ^ 70 +
        2170680552492845061597077605670722342417957881756031024032178431023023) * 10 ^ 70 +
        2061653890298502585035342956696927048163833660292897454853800129896979) * 10 ^ 70 +
        1471106043105545077373134575464770955045044515360392059394857950888034) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (320 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (321 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (321 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_321 :
    recurrence4Scalar2First.coeff 321 =
      (((((35690116032128885 * 10 ^ 70 +
        6100482838622274617228250295545411171833998863351046010374788135947669) * 10 ^ 70 +
        0081378780728721565767407331721448555331682567773363263758275437477875) * 10 ^ 70 +
        4736992923196106674246201944491895138069995765591901742942028919272034) * 10 ^ 70 +
        1438664849704082717296151665494177975561181794377299310389192438062510) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (321 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (322 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (322 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_322 :
    recurrence4Scalar2First.coeff 322 =
      -(((((16758909961233988 * 10 ^ 70 +
        8083155797152062137404676904806035825915845003136868260424420775777413) * 10 ^ 70 +
        3299060595133492481778444928075518890217402761104212862918161532475232) * 10 ^ 70 +
        1143239597114865140188382256597914484148998092867748496550980057349481) * 10 ^ 70 +
        6243394717266348780480073156825985877309461674846334992903459749905450) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (322 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (323 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (323 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_323 :
    recurrence4Scalar2First.coeff 323 =
      (((((7590028474645244 * 10 ^ 70 +
        5842401560757735283608318704991931590274329834939438406064779196257943) * 10 ^ 70 +
        5598523689040597603532520589421042428726880074383990437767085926372315) * 10 ^ 70 +
        3124587362395922372838943878497303880403997793056708854874827821983759) * 10 ^ 70 +
        0599683270142624781303789379816956504818557947811030135329307310775676) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (323 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (324 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (324 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_324 :
    recurrence4Scalar2First.coeff 324 =
      -(((((3294208595442310 * 10 ^ 70 +
        6650626767543319914813332433382009918120083594600365352352024903828627) * 10 ^ 70 +
        2008882877009908301703072640033879554572580232477989781072506156197049) * 10 ^ 70 +
        6749002115160206593806290431082509188314930672084114432752761522831558) * 10 ^ 70 +
        6837415753679247277208660681406255124433347761515258845791929598203893) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (324 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (325 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (325 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_325 :
    recurrence4Scalar2First.coeff 325 =
      (((((1355250264614926 * 10 ^ 70 +
        9171676662527549037188703825914475563033965774413249824140440181206246) * 10 ^ 70 +
        7363702974204881596404829093443682814471891495471679890700512607874969) * 10 ^ 70 +
        5999119450111036992751100061974113451031129634957092403026040968119047) * 10 ^ 70 +
        9101250934637101406868571182865464068822810616219223756870886990687138) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (325 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (326 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (326 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_326 :
    recurrence4Scalar2First.coeff 326 =
      -(((((517900336187960 * 10 ^ 70 +
        8299028799251242138192922196894541449850273339386446838128295897003757) * 10 ^ 70 +
        4344334217377342227944820692072927803771592917050179783527916348453975) * 10 ^ 70 +
        3901041666324367790701731570963400703960552590876038203720518492916460) * 10 ^ 70 +
        5399133221402149833886450763777665794650331478105381894129423030693704) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (326 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (327 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (327 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_327 :
    recurrence4Scalar2First.coeff 327 =
      (((((175974047097632 * 10 ^ 70 +
        2952304925611128469816892395146589670630866594699380824548254488253128) * 10 ^ 70 +
        2993990779493950964160392204580526096341882277696477043997726251154582) * 10 ^ 70 +
        4091873381778719973733252970290612298510842982979717345454325597672421) * 10 ^ 70 +
        3204017272147044116540251669350021242344659562601181983066615068072124) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (327 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (328 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (328 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_328 :
    recurrence4Scalar2First.coeff 328 =
      -(((((46861528527082 * 10 ^ 70 +
        2310272360264606598189485857633747428511186194699796993116084888014254) * 10 ^ 70 +
        6461238048334946418828369715100379615818238836816898764545498696268354) * 10 ^ 70 +
        7260846246878073911081254526291849990267089731148484785489618120404000) * 10 ^ 70 +
        3100662265371943511269480198598802123398023738217445796970961392181863) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (328 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
