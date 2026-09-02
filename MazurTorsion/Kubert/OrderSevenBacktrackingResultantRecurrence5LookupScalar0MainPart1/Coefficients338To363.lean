/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B0_coeff_0
  recurrence5B0_coeff_1
  recurrence5B0_coeff_2
  recurrence5B0_coeff_3
  recurrence5B0_coeff_4
  recurrence5B0_coeff_5
  recurrence5B0_coeff_6
  recurrence5B0_coeff_7
  recurrence5B0_coeff_8
  recurrence5B0_coeff_9
  recurrence5B0_coeff_10
  recurrence5B0_coeff_11
  recurrence5B0_coeff_12
  recurrence5B0_coeff_13
  recurrence5B0_coeff_14
  recurrence5B0_coeff_15
  recurrence5B0_coeff_16
  recurrence5B0_coeff_17
  recurrence5B0_coeff_18
  recurrence5B0_coeff_19
  recurrence5B0_coeff_20
  recurrence5B0_coeff_21
  recurrence5B0_coeff_22
  recurrence5B0_coeff_23
  recurrence5B0_coeff_24
  recurrence5B0_coeff_25
  recurrence5B0_coeff_26
  recurrence5B0_coeff_27
  recurrence5B0_coeff_28
  recurrence5B0_coeff_29
  recurrence5B0_coeff_30
  recurrence5B0_coeff_31
  recurrence5B0_coeff_32
  recurrence5B0_coeff_33
  recurrence5B0_coeff_34
  recurrence5B0_coeff_35
  recurrence5B0_coeff_36
  recurrence5B0_coeff_37
  recurrence5B0_coeff_38
  recurrence5B0_coeff_39
  recurrence5B0_coeff_40
  recurrence5B0_coeff_41
  recurrence5B0_coeff_42
  recurrence5B0_coeff_43
  recurrence5B0_coeff_44
  recurrence5B0_coeff_45
  recurrence5B0_coeff_46
  recurrence5B0_coeff_47
  recurrence5B0_coeff_48
  recurrence5B0_coeff_49
  recurrence5B0_coeff_50
  recurrence5B0_coeff_51
  recurrence5B0_coeff_52
  recurrence5B0_coeff_53
  recurrence5B0_coeff_54
  recurrence5B0_coeff_55
  recurrence5B0_coeff_56
  recurrence5B0_coeff_57
  recurrence5B0_coeff_58
  recurrence5B0_coeff_59
  recurrence5B0_coeff_60
  recurrence5B0_coeff_61
  recurrence5B0_coeff_62
  recurrence5B0_coeff_63

attribute [local simp]
  recurrence5B0_coeff_64
  recurrence5B0_coeff_65
  recurrence5B0_coeff_66
  recurrence5B0_coeff_67
  recurrence5B0_coeff_68
  recurrence5B0_coeff_69
  recurrence5B0_coeff_70
  recurrence5B0_coeff_71
  recurrence5B0_coeff_72
  recurrence5B0_coeff_73
  recurrence5B0_coeff_74
  recurrence5B0_coeff_75
  recurrence5B0_coeff_76
  recurrence5B0_coeff_77
  recurrence5B0_coeff_78
  recurrence5B0_coeff_79
  recurrence5B0_coeff_80
  recurrence5B0_coeff_81
  recurrence5B0_coeff_82
  recurrence5B0_coeff_83
  recurrence5B0_coeff_84
  recurrence5B0_coeff_85
  recurrence5B0_coeff_86
  recurrence5B0_coeff_87
  recurrence5B0_coeff_88
  recurrence5B0_coeff_89
  recurrence5B0_coeff_90
  recurrence5B0_coeff_91
  recurrence5B0_coeff_92
  recurrence5B0_coeff_93
  recurrence5B0_coeff_94
  recurrence5B0_coeff_95
  recurrence5B0_coeff_96
  recurrence5B0_coeff_97
  recurrence5B0_coeff_98
  recurrence5B0_coeff_99
  recurrence5B0_coeff_100
  recurrence5B0_coeff_101
  recurrence5B0_coeff_102
  recurrence5B0_coeff_103
  recurrence5B0_coeff_104
  recurrence5B0_coeff_105
  recurrence5B0_coeff_106
  recurrence5B0_coeff_107
  recurrence5B0_coeff_108
  recurrence5B0_coeff_109
  recurrence5B0_coeff_110
  recurrence5B0_coeff_111
  recurrence5B0_coeff_112
  recurrence5B0_coeff_113
  recurrence5B0_coeff_114
  recurrence5B0_coeff_115
  recurrence5B0_coeff_116
  recurrence5B0_coeff_117
  recurrence5B0_coeff_118
  recurrence5B0_coeff_119
  recurrence5B0_coeff_120
  recurrence5B0_coeff_121
  recurrence5B0_coeff_122
  recurrence5B0_coeff_123
  recurrence5B0_coeff_124
  recurrence5B0_coeff_125
  recurrence5B0_coeff_126
  recurrence5B0_coeff_127

attribute [local simp]
  recurrence5B0_coeff_128
  recurrence5B0_coeff_129
  recurrence5B0_coeff_130
  recurrence5B0_coeff_131
  recurrence5B0_coeff_132
  recurrence5B0_coeff_133
  recurrence5B0_coeff_134
  recurrence5B0_coeff_135
  recurrence5B0_coeff_136
  recurrence5B0_coeff_137
  recurrence5B0_coeff_138
  recurrence5B0_coeff_139
  recurrence5B0_coeff_140
  recurrence5B0_coeff_141
  recurrence5B0_coeff_142
  recurrence5B0_coeff_143
  recurrence5B0_coeff_144
  recurrence5B0_coeff_145
  recurrence5B0_coeff_146
  recurrence5B0_coeff_147
  recurrence5B0_coeff_148
  recurrence5B0_coeff_149
  recurrence5B0_coeff_150
  recurrence5B0_coeff_151
  recurrence5B0_coeff_152
  recurrence5B0_coeff_153
  recurrence5QuotientConstant_coeff_0
  recurrence5QuotientConstant_coeff_1
  recurrence5QuotientConstant_coeff_2
  recurrence5QuotientConstant_coeff_3
  recurrence5QuotientConstant_coeff_4
  recurrence5QuotientConstant_coeff_5
  recurrence5QuotientConstant_coeff_6
  recurrence5QuotientConstant_coeff_7
  recurrence5QuotientConstant_coeff_8
  recurrence5QuotientConstant_coeff_9
  recurrence5QuotientConstant_coeff_10
  recurrence5QuotientConstant_coeff_11
  recurrence5QuotientConstant_coeff_12
  recurrence5QuotientConstant_coeff_13
  recurrence5QuotientConstant_coeff_14
  recurrence5QuotientConstant_coeff_15
  recurrence5QuotientConstant_coeff_16
  recurrence5QuotientConstant_coeff_17
  recurrence5QuotientConstant_coeff_18
  recurrence5QuotientConstant_coeff_19
  recurrence5QuotientConstant_coeff_20
  recurrence5QuotientConstant_coeff_21
  recurrence5QuotientConstant_coeff_22
  recurrence5QuotientConstant_coeff_23
  recurrence5QuotientConstant_coeff_24
  recurrence5QuotientConstant_coeff_25
  recurrence5QuotientConstant_coeff_26
  recurrence5QuotientConstant_coeff_27
  recurrence5QuotientConstant_coeff_28
  recurrence5QuotientConstant_coeff_29
  recurrence5QuotientConstant_coeff_30
  recurrence5QuotientConstant_coeff_31
  recurrence5QuotientConstant_coeff_32
  recurrence5QuotientConstant_coeff_33
  recurrence5QuotientConstant_coeff_34
  recurrence5QuotientConstant_coeff_35
  recurrence5QuotientConstant_coeff_36
  recurrence5QuotientConstant_coeff_37

attribute [local simp]
  recurrence5QuotientConstant_coeff_38
  recurrence5QuotientConstant_coeff_39
  recurrence5QuotientConstant_coeff_40
  recurrence5QuotientConstant_coeff_41
  recurrence5QuotientConstant_coeff_42
  recurrence5QuotientConstant_coeff_43
  recurrence5QuotientConstant_coeff_44
  recurrence5QuotientConstant_coeff_45
  recurrence5QuotientConstant_coeff_46
  recurrence5QuotientConstant_coeff_47
  recurrence5QuotientConstant_coeff_48
  recurrence5QuotientConstant_coeff_49
  recurrence5QuotientConstant_coeff_50
  recurrence5QuotientConstant_coeff_51
  recurrence5QuotientConstant_coeff_52
  recurrence5QuotientConstant_coeff_53
  recurrence5QuotientConstant_coeff_54
  recurrence5QuotientConstant_coeff_55
  recurrence5QuotientConstant_coeff_56
  recurrence5QuotientConstant_coeff_57
  recurrence5QuotientConstant_coeff_58
  recurrence5QuotientConstant_coeff_59
  recurrence5QuotientConstant_coeff_60
  recurrence5QuotientConstant_coeff_61
  recurrence5QuotientConstant_coeff_62
  recurrence5QuotientConstant_coeff_63
  recurrence5QuotientConstant_coeff_64
  recurrence5QuotientConstant_coeff_65
  recurrence5QuotientConstant_coeff_66
  recurrence5QuotientConstant_coeff_67
  recurrence5QuotientConstant_coeff_68
  recurrence5QuotientConstant_coeff_69
  recurrence5QuotientConstant_coeff_70
  recurrence5QuotientConstant_coeff_71
  recurrence5QuotientConstant_coeff_72
  recurrence5QuotientConstant_coeff_73
  recurrence5QuotientConstant_coeff_74
  recurrence5QuotientConstant_coeff_75
  recurrence5QuotientConstant_coeff_76
  recurrence5QuotientConstant_coeff_77
  recurrence5QuotientConstant_coeff_78
  recurrence5QuotientConstant_coeff_79
  recurrence5QuotientConstant_coeff_80
  recurrence5QuotientConstant_coeff_81
  recurrence5QuotientConstant_coeff_82
  recurrence5QuotientConstant_coeff_83
  recurrence5QuotientConstant_coeff_84
  recurrence5QuotientConstant_coeff_85
  recurrence5QuotientConstant_coeff_86
  recurrence5QuotientConstant_coeff_87
  recurrence5QuotientConstant_coeff_88
  recurrence5QuotientConstant_coeff_89
  recurrence5QuotientConstant_coeff_90
  recurrence5QuotientConstant_coeff_91
  recurrence5QuotientConstant_coeff_92
  recurrence5QuotientConstant_coeff_93
  recurrence5QuotientConstant_coeff_94
  recurrence5QuotientConstant_coeff_95
  recurrence5QuotientConstant_coeff_96
  recurrence5QuotientConstant_coeff_97
  recurrence5QuotientConstant_coeff_98
  recurrence5QuotientConstant_coeff_99
  recurrence5QuotientConstant_coeff_100
  recurrence5QuotientConstant_coeff_101

attribute [local simp]
  recurrence5QuotientConstant_coeff_102
  recurrence5QuotientConstant_coeff_103
  recurrence5QuotientConstant_coeff_104
  recurrence5QuotientConstant_coeff_105
  recurrence5QuotientConstant_coeff_106
  recurrence5QuotientConstant_coeff_107
  recurrence5QuotientConstant_coeff_108
  recurrence5QuotientConstant_coeff_109
  recurrence5QuotientConstant_coeff_110
  recurrence5QuotientConstant_coeff_111
  recurrence5QuotientConstant_coeff_112
  recurrence5QuotientConstant_coeff_113
  recurrence5QuotientConstant_coeff_114
  recurrence5QuotientConstant_coeff_115
  recurrence5QuotientConstant_coeff_116
  recurrence5QuotientConstant_coeff_117
  recurrence5QuotientConstant_coeff_118
  recurrence5QuotientConstant_coeff_119
  recurrence5QuotientConstant_coeff_120
  recurrence5QuotientConstant_coeff_121
  recurrence5QuotientConstant_coeff_122
  recurrence5QuotientConstant_coeff_123
  recurrence5QuotientConstant_coeff_124
  recurrence5QuotientConstant_coeff_125
  recurrence5QuotientConstant_coeff_126
  recurrence5QuotientConstant_coeff_127
  recurrence5QuotientConstant_coeff_128
  recurrence5QuotientConstant_coeff_129
  recurrence5QuotientConstant_coeff_130
  recurrence5QuotientConstant_coeff_131
  recurrence5QuotientConstant_coeff_132
  recurrence5QuotientConstant_coeff_133
  recurrence5QuotientConstant_coeff_134
  recurrence5QuotientConstant_coeff_135
  recurrence5QuotientConstant_coeff_136
  recurrence5QuotientConstant_coeff_137
  recurrence5QuotientConstant_coeff_138
  recurrence5QuotientConstant_coeff_139
  recurrence5QuotientConstant_coeff_140
  recurrence5QuotientConstant_coeff_141
  recurrence5QuotientConstant_coeff_142
  recurrence5QuotientConstant_coeff_143
  recurrence5QuotientConstant_coeff_144
  recurrence5QuotientConstant_coeff_145
  recurrence5QuotientConstant_coeff_146
  recurrence5QuotientConstant_coeff_147
  recurrence5QuotientConstant_coeff_148
  recurrence5QuotientConstant_coeff_149
  recurrence5QuotientConstant_coeff_150
  recurrence5QuotientConstant_coeff_151
  recurrence5QuotientConstant_coeff_152
  recurrence5QuotientConstant_coeff_153
  recurrence5QuotientConstant_coeff_154
  recurrence5QuotientConstant_coeff_155
  recurrence5QuotientConstant_coeff_156
  recurrence5QuotientConstant_coeff_157
  recurrence5QuotientConstant_coeff_158
  recurrence5QuotientConstant_coeff_159
  recurrence5QuotientConstant_coeff_160
  recurrence5QuotientConstant_coeff_161
  recurrence5QuotientConstant_coeff_162
  recurrence5QuotientConstant_coeff_163
  recurrence5QuotientConstant_coeff_164
  recurrence5QuotientConstant_coeff_165

attribute [local simp]
  recurrence5QuotientConstant_coeff_166
  recurrence5QuotientConstant_coeff_167
  recurrence5QuotientConstant_coeff_168
  recurrence5QuotientConstant_coeff_169
  recurrence5QuotientConstant_coeff_170
  recurrence5QuotientConstant_coeff_171
  recurrence5QuotientConstant_coeff_172
  recurrence5QuotientConstant_coeff_173
  recurrence5QuotientConstant_coeff_174
  recurrence5QuotientConstant_coeff_175
  recurrence5QuotientConstant_coeff_176
  recurrence5QuotientConstant_coeff_177
  recurrence5QuotientConstant_coeff_178
  recurrence5QuotientConstant_coeff_179
  recurrence5QuotientConstant_coeff_180
  recurrence5QuotientConstant_coeff_181
  recurrence5QuotientConstant_coeff_182
  recurrence5QuotientConstant_coeff_183
  recurrence5QuotientConstant_coeff_184
  recurrence5QuotientConstant_coeff_185
  recurrence5QuotientConstant_coeff_186
  recurrence5QuotientConstant_coeff_187
  recurrence5QuotientConstant_coeff_188
  recurrence5QuotientConstant_coeff_189
  recurrence5QuotientConstant_coeff_190
  recurrence5QuotientConstant_coeff_191
  recurrence5QuotientConstant_coeff_192
  recurrence5QuotientConstant_coeff_193
  recurrence5QuotientConstant_coeff_194
  recurrence5QuotientConstant_coeff_195
  recurrence5QuotientConstant_coeff_196
  recurrence5QuotientConstant_coeff_197
  recurrence5QuotientConstant_coeff_198
  recurrence5QuotientConstant_coeff_199
  recurrence5QuotientConstant_coeff_200
  recurrence5QuotientConstant_coeff_201
  recurrence5QuotientConstant_coeff_202
  recurrence5QuotientConstant_coeff_203
  recurrence5QuotientConstant_coeff_204
  recurrence5QuotientConstant_coeff_205
  recurrence5QuotientConstant_coeff_206
  recurrence5QuotientConstant_coeff_207
  recurrence5QuotientConstant_coeff_208
  recurrence5QuotientConstant_coeff_209
  recurrence5QuotientConstant_coeff_210
  recurrence5QuotientConstant_coeff_211
  recurrence5QuotientConstant_coeff_212
  recurrence5QuotientConstant_coeff_213
  recurrence5QuotientConstant_coeff_214
  recurrence5QuotientConstant_coeff_215
  recurrence5QuotientConstant_coeff_216
  recurrence5QuotientConstant_coeff_217
  recurrence5QuotientConstant_coeff_218
  recurrence5QuotientConstant_coeff_219
  recurrence5QuotientConstant_coeff_220
  recurrence5QuotientConstant_coeff_221
  recurrence5QuotientConstant_coeff_222
  recurrence5QuotientConstant_coeff_223
  recurrence5QuotientConstant_coeff_224
  recurrence5QuotientConstant_coeff_225
  recurrence5QuotientConstant_coeff_226
  recurrence5QuotientConstant_coeff_227
  recurrence5QuotientConstant_coeff_228
  recurrence5QuotientConstant_coeff_229

attribute [local simp]
  recurrence5QuotientConstant_coeff_230
  recurrence5QuotientConstant_coeff_231
  recurrence5QuotientConstant_coeff_232
  recurrence5QuotientConstant_coeff_233
  recurrence5QuotientConstant_coeff_234
  recurrence5QuotientConstant_coeff_235
  recurrence5QuotientConstant_coeff_236
  recurrence5QuotientConstant_coeff_237
  recurrence5QuotientConstant_coeff_238
  recurrence5QuotientConstant_coeff_239
  recurrence5QuotientConstant_coeff_240
  recurrence5QuotientConstant_coeff_241
  recurrence5QuotientConstant_coeff_242
  recurrence5QuotientConstant_coeff_243
  recurrence5QuotientConstant_coeff_244
  recurrence5QuotientConstant_coeff_245
  recurrence5QuotientConstant_coeff_246
  recurrence5QuotientConstant_coeff_247
  recurrence5QuotientConstant_coeff_248
  recurrence5QuotientConstant_coeff_249
  recurrence5QuotientConstant_coeff_250
  recurrence5QuotientConstant_coeff_251
  recurrence5QuotientConstant_coeff_252
  recurrence5QuotientConstant_coeff_253
  recurrence5QuotientConstant_coeff_254
  recurrence5QuotientConstant_coeff_255
  recurrence5QuotientConstant_coeff_256
  recurrence5QuotientConstant_coeff_257
  recurrence5QuotientConstant_coeff_258
  recurrence5QuotientConstant_coeff_259
  recurrence5QuotientConstant_coeff_260
  recurrence5QuotientConstant_coeff_261
  recurrence5QuotientConstant_coeff_262
  recurrence5QuotientConstant_coeff_263
  recurrence5QuotientConstant_coeff_264
  recurrence5QuotientConstant_coeff_265
  recurrence5QuotientConstant_coeff_266
  recurrence5QuotientConstant_coeff_267
  recurrence5QuotientConstant_coeff_268
  recurrence5QuotientConstant_coeff_269
  recurrence5QuotientConstant_coeff_270
  recurrence5QuotientConstant_coeff_271
  recurrence5QuotientConstant_coeff_272
  recurrence5QuotientConstant_coeff_273
  recurrence5QuotientConstant_coeff_274
  recurrence5QuotientConstant_coeff_275
  recurrence5QuotientConstant_coeff_276
  recurrence5QuotientConstant_coeff_277
  recurrence5QuotientConstant_coeff_278
  recurrence5QuotientConstant_coeff_279
  recurrence5QuotientConstant_coeff_280
  recurrence5QuotientConstant_coeff_281
  recurrence5QuotientConstant_coeff_282
  recurrence5QuotientConstant_coeff_283
  recurrence5QuotientConstant_coeff_284
  recurrence5QuotientConstant_coeff_285
  recurrence5QuotientConstant_coeff_286
  recurrence5QuotientConstant_coeff_287
  recurrence5QuotientConstant_coeff_288
  recurrence5QuotientConstant_coeff_289
  recurrence5QuotientConstant_coeff_290
  recurrence5QuotientConstant_coeff_291
  recurrence5QuotientConstant_coeff_292
  recurrence5QuotientConstant_coeff_293

attribute [local simp]
  recurrence5QuotientConstant_coeff_294
  recurrence5QuotientConstant_coeff_295
  recurrence5QuotientConstant_coeff_296
  recurrence5QuotientConstant_coeff_297
  recurrence5QuotientConstant_coeff_298
  recurrence5QuotientConstant_coeff_299
  recurrence5QuotientConstant_coeff_300
  recurrence5QuotientConstant_coeff_301
  recurrence5QuotientConstant_coeff_302
  recurrence5QuotientConstant_coeff_303
  recurrence5QuotientConstant_coeff_304
  recurrence5QuotientConstant_coeff_305
  recurrence5QuotientConstant_coeff_306
  recurrence5QuotientConstant_coeff_307
  recurrence5QuotientConstant_coeff_308
  recurrence5QuotientConstant_coeff_309
  recurrence5QuotientConstant_coeff_310
  recurrence5QuotientConstant_coeff_311
  recurrence5QuotientConstant_coeff_312
  recurrence5QuotientConstant_coeff_313

private theorem recurrence5Scalar0Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (338 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_338 :
    recurrence5Scalar0Main.coeff 338 =
      -(((((6646357345391990589873980274999034270275942817721674 * 10 ^ 70 +
        8206552704166840089172179052466680567841862808936275469362818660061539) * 10 ^ 70 +
        5449318942182964694145910849767182896210363827674753963617176125835132) * 10 ^ 70 +
        1295708000405656406642431125121267720870924498335333968610711338501465) * 10 ^ 70 +
        5409496030908431523924005472709228983523852050620381097759676886446154) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 25 +
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
    rw [show 186 = 1 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (339 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_339 :
    recurrence5Scalar0Main.coeff 339 =
      (((((2683013380076624365589390630382915085175777860574192 * 10 ^ 70 +
        5311887831277130821034085640336663527954412666419526031012658740949778) * 10 ^ 70 +
        9519342747150664148683741412874819369347581947040861405951938768622514) * 10 ^ 70 +
        3439070870045670106812098519975140401874503933934866058748491729305426) * 10 ^ 70 +
        4140436586945502607102837367340592275633310657793613035946715993187988) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 26 +
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
  rw [recurrence5Scalar0Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (340 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_340 :
    recurrence5Scalar0Main.coeff 340 =
      -(((((1062711968951584695708929105054550428615221388143248 * 10 ^ 70 +
        3159167105032165531248517800472964386025295315492503827121035107592690) * 10 ^ 70 +
        3564651494302620467206653715849979071489083859594692717050376804992342) * 10 ^ 70 +
        8582625551029102708319690827129583849126523453926592513328064250712184) * 10 ^ 70 +
        8680487875019425458320380620090171263302235868530888161406273670447404) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 27 +
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
    rw [show 218 = 31 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (341 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_341 :
    recurrence5Scalar0Main.coeff 341 =
      (((((412614423602051147332769585116830194933310297003152 * 10 ^ 70 +
        7027576619837143324751097814215094352940309553195608177194191883688308) * 10 ^ 70 +
        3901458489216989482043798679759224215260775806664413838512161314616541) * 10 ^ 70 +
        1765867390105823159330281927028139863739567168390905267216541188325166) * 10 ^ 70 +
        3274891902216062892143282737870304071331569098018983270382945719757224) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 28 +
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
    rw [show 218 = 30 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (342 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_342 :
    recurrence5Scalar0Main.coeff 342 =
      -(((((156893598880308479146161843550886527954486325079394 * 10 ^ 70 +
        7540148030758026237456251321519120761686027282542259270505864823882649) * 10 ^ 70 +
        4586283771698366000697235413542726981935735433985267655978366854259117) * 10 ^ 70 +
        0174058310701873179109067048082680126259928054952449466215752576494867) * 10 ^ 70 +
        8147453832263612487009603878071830735008708642382009439453239584890892) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 29 +
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
    rw [show 218 = 29 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (343 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_343 :
    recurrence5Scalar0Main.coeff 343 =
      (((((58372351227104008884886475990617311145099943910678 * 10 ^ 70 +
        3775670328312124147006468825137356486808451961986596433646026084798947) * 10 ^ 70 +
        4576939653390862384925275857866862797007679204966536371495712283219020) * 10 ^ 70 +
        5873869483534466255343263947440749734146647161466649669044446331060214) * 10 ^ 70 +
        6586770590761164986502330456903060245198068536432951144777540405651937) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 30 +
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
    rw [show 218 = 28 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (344 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_344 :
    recurrence5Scalar0Main.coeff 344 =
      -(((((21230677262887106905479756858647388834658369646683 * 10 ^ 70 +
        0243661061775176010288841598063915229280703989238375935020490683460912) * 10 ^ 70 +
        8983769880502432682921488507881084756202147000704291578788538774832612) * 10 ^ 70 +
        5494059009814436437969256627555874135269540005186308583282049275527353) * 10 ^ 70 +
        4291959379962129929939970834006649078103082109794699496160239256995111) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 31 +
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
    rw [show 218 = 27 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (345 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_345 :
    recurrence5Scalar0Main.coeff 345 =
      (((((7541807321178365365552515665946004264542122140401 * 10 ^ 70 +
        3767422017245795064243151106182905344725070791766978343340012200473850) * 10 ^ 70 +
        1896792635638540515923728402913662337382297121864148174563659534393328) * 10 ^ 70 +
        5376589518640663630883087632855896582785525604700509696621147895158073) * 10 ^ 70 +
        7559732202506880530612087286755075925111214046119664638969379551345398) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 32 +
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
    rw [show 218 = 26 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (346 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_346 :
    recurrence5Scalar0Main.coeff 346 =
      -(((((2613968617029313797429993472780248232207423295706 * 10 ^ 70 +
        2348823473497993947865069047562269077263530781414300859475455739834814) * 10 ^ 70 +
        8809961827692486204749082262538030815704780963500266046582902278358290) * 10 ^ 70 +
        6541893722139710353671760015691952868239447085337946923791726978900332) * 10 ^ 70 +
        1129238511750199063804642970268372332945957667297923004792553932852928) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 33 +
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
    rw [show 218 = 25 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (347 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_347 :
    recurrence5Scalar0Main.coeff 347 =
      (((((882900013131906372030113835408277389698106501619 * 10 ^ 70 +
        7881287970146205121758166108920389585064735822528056396741997210596653) * 10 ^ 70 +
        9416730190804445513444354400175620144606318677692395220012865810146456) * 10 ^ 70 +
        5939124319053969597483022201346519085484978320458309819075619296252319) * 10 ^ 70 +
        7645421336404721700643872454687579424335777685982865555203306198916195) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 34 +
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
    rw [show 218 = 24 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (348 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_348 :
    recurrence5Scalar0Main.coeff 348 =
      -(((((290153530169998064731747449877791111073942102817 * 10 ^ 70 +
        9717014674366660890304181840010068343294326611919262478440005187151738) * 10 ^ 70 +
        3873634491769555637709919201854205361666097070229668403721871019517848) * 10 ^ 70 +
        9405070151869146957955313510546138509026202984212941127833838054381541) * 10 ^ 70 +
        9373668628761999958159490754354629715649184661732844183523925163423435) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 35 +
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
    rw [show 218 = 23 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (349 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_349 :
    recurrence5Scalar0Main.coeff 349 =
      (((((92577052133871547668790349602065173814220948371 * 10 ^ 70 +
        2997078516662588993182929085364042226543377395775479038657279143561721) * 10 ^ 70 +
        7252967805019256406729805014890645901311801643679600027434065445036813) * 10 ^ 70 +
        9161315233084397112423937703659936498163912308417666136030448193765577) * 10 ^ 70 +
        7712969448409425094505518731545662805416700720819480512394411508856224) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 36 +
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
    rw [show 218 = 22 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (350 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_350 :
    recurrence5Scalar0Main.coeff 350 =
      -(((((28584861005342224097261074285594851541693611666 * 10 ^ 70 +
        8542784118859072268580506206160718117036911742972625902596254986030379) * 10 ^ 70 +
        0517120771686307260028654710926515527476483224720615642347151738943060) * 10 ^ 70 +
        6359878786793024953839939668648099693618693201180312627289172880888848) * 10 ^ 70 +
        2149906164620786066318667522025403408350208564083562287721829358814403) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 37 +
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
    rw [show 218 = 21 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (351 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_351 :
    recurrence5Scalar0Main.coeff 351 =
      (((((8497995653686911286880609445215429096817931015 * 10 ^ 70 +
        0087607117800142041002867462812588104131526290392331536122442971308212) * 10 ^ 70 +
        7949670689102781687562599935288814332750082052627872519422685632261815) * 10 ^ 70 +
        1188938318102690464588425656535529872795338585648113713967196281851442) * 10 ^ 70 +
        5420218728300856248128389178050872895021949954965875051573744332848952) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 38 +
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
    rw [show 218 = 20 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (352 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_352 :
    recurrence5Scalar0Main.coeff 352 =
      -(((((2411671151680648316712715883645330650528471209 * 10 ^ 70 +
        6419807883745864910951149715983738575392431218829733225883724657700925) * 10 ^ 70 +
        5086599066983374037298935369915258869354023674971192805043234504833908) * 10 ^ 70 +
        4907067320491816109259530273621940920328398743054723214887038528006685) * 10 ^ 70 +
        8896500805853605807024735483592098516542690675298275512229234851979394) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 39 +
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
    rw [show 218 = 19 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (353 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_353 :
    recurrence5Scalar0Main.coeff 353 =
      (((((643104981430192337720450924061267886952096764 * 10 ^ 70 +
        7214043412023067951394621140190366444294233389788836483974248799512283) * 10 ^ 70 +
        5482144124768874365324904885795733646870781538218251108104675862077529) * 10 ^ 70 +
        1073557300099449767724776880072697381447904141241800699788463052629288) * 10 ^ 70 +
        1664174958404519067951853126055303742311401453157847489887239082949773) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 40 +
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
    rw [show 218 = 18 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (354 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_354 :
    recurrence5Scalar0Main.coeff 354 =
      -(((((155889296192914221670387699287256197642352541 * 10 ^ 70 +
        0347281105497207367690554491079222572483945158810739674124078234488819) * 10 ^ 70 +
        2375477019356485275475893129794532322912293746282111038431515892684827) * 10 ^ 70 +
        9515436932686770345348971367992523553528859467888639670842818982692898) * 10 ^ 70 +
        1039387229191554757763027786567978414067784916562143264895741650434891) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 41 +
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
    rw [show 218 = 17 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (355 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_355 :
    recurrence5Scalar0Main.coeff 355 =
      (((((31466082230723548792126647010414872970415677 * 10 ^ 70 +
        6658468964691010408138434471508206632960000115736379102709400485780395) * 10 ^ 70 +
        3665343552025719145262449006588293014606750556652488031715217662718870) * 10 ^ 70 +
        8726230084211166913000656465964198102961747915005481609041605824308874) * 10 ^ 70 +
        7070457771727406643212191081208632400688081875606280041947758051930497) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 42 +
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
    rw [show 218 = 16 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (356 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_356 :
    recurrence5Scalar0Main.coeff 356 =
      -(((((3504658466625329799962385636280659610350655 * 10 ^ 70 +
        2893556412664629592505110634208218985549789307333880586149531669145491) * 10 ^ 70 +
        7498843613602489016277709982569693877557709852365584269593706802592900) * 10 ^ 70 +
        0491832414839233224126002292956149446196918552017085776979213309535511) * 10 ^ 70 +
        2629029010024061013444558604944886839149712032417732185991806179424671) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 43 +
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
    rw [show 218 = 15 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (357 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_357 :
    recurrence5Scalar0Main.coeff 357 =
      -(((((1161687644433421417556988157405784685736816 * 10 ^ 70 +
        7460314231176602246798653502760713394906021771877468817183137020256337) * 10 ^ 70 +
        4188161347512674112559610469008694929507132544240233241689008356886650) * 10 ^ 70 +
        9443693328864391815500391599939605174769216439250922473400735772182025) * 10 ^ 70 +
        0411343622994416723338190774278182514328741321863611234235605731332752) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 44 +
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
    rw [show 218 = 14 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (358 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_358 :
    recurrence5Scalar0Main.coeff 358 =
      (((((1152860365448186011844101538180976396125895 * 10 ^ 70 +
        6295227307324304911954750905998186070871703497263532798353410069823402) * 10 ^ 70 +
        9946555883975417695107126015400802144722208413007575192567658659637527) * 10 ^ 70 +
        7283600538083587949957234818221754775359412667384509373498809677424674) * 10 ^ 70 +
        0012634130195725558871866437190305468957488293584767994895700032401462) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 45 +
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
    rw [show 218 = 13 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (359 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_359 :
    recurrence5Scalar0Main.coeff 359 =
      -(((((633346122229111887427306086903589046895582 * 10 ^ 70 +
        9773683112093155188963359638500936959627363511925919054297496462291667) * 10 ^ 70 +
        2258837758629532904859586823115358692663910835791551555780848418406704) * 10 ^ 70 +
        7850718549597907612395487647431051773205625263712690953724001434801633) * 10 ^ 70 +
        2809195712845565105931048785466214136540077822965980890771993582443498) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 46 +
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
    rw [show 218 = 12 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (360 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_360 :
    recurrence5Scalar0Main.coeff 360 =
      (((((291591997527274660733073155593569535067494 * 10 ^ 70 +
        9280876470524607996693817677210912879992611035850157368620597413731168) * 10 ^ 70 +
        9005209868933650328886007154923800164480418077018621723374802731976504) * 10 ^ 70 +
        9272028360549822116770601829968504273775445117964824500720969302371877) * 10 ^ 70 +
        4881210676224664743031006849078124170682166200100638878860590892109375) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 47 +
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
    rw [show 218 = 11 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (361 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_361 :
    recurrence5Scalar0Main.coeff 361 =
      -(((((123058870246476339003122077118940589701292 * 10 ^ 70 +
        6710642952241946738160239882093003524090891369260876617921213576818941) * 10 ^ 70 +
        5362000803018241198031405212594746400590289311062126867139750495561064) * 10 ^ 70 +
        3149757336934527788597089456584553351757878111516309510553469702556127) * 10 ^ 70 +
        3467806611926069605297870903530447623726733243449284921697847741936379) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 48 +
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
    rw [show 218 = 10 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (362 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_362 :
    recurrence5Scalar0Main.coeff 362 =
      (((((49272167326149971273234548828355645898603 * 10 ^ 70 +
        3466972568350037756719181225939422381830489025971740856340925632329742) * 10 ^ 70 +
        8168919330295318781943074783433125040316858081310229072403456550386704) * 10 ^ 70 +
        5540092553194064937862755178144191687377242473013430998550073235641576) * 10 ^ 70 +
        2591606438175671916973218684402330564238494413739094430559294601812989) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 49 +
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
    rw [show 218 = 9 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (363 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_363 :
    recurrence5Scalar0Main.coeff 363 =
      -(((((19026785410374987774805671900645965871412 * 10 ^ 70 +
        0853058229733565807898689788659862816294435433781247856505566479075354) * 10 ^ 70 +
        3432280628858943556983487198884008345161589061607901474499196136074129) * 10 ^ 70 +
        9118616641760656160970309113207754075145948724668070230428079720222277) * 10 ^ 70 +
        4821758499748885089216526516888252814220501915273128247317884401621639) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 50 +
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
    rw [show 218 = 8 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
