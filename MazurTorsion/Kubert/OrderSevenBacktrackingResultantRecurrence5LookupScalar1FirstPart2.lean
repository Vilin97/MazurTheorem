/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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
  recurrence5B2A3_coeff_0
  recurrence5B2A3_coeff_1
  recurrence5B2A3_coeff_2
  recurrence5B2A3_coeff_3
  recurrence5B2A3_coeff_4
  recurrence5B2A3_coeff_5
  recurrence5B2A3_coeff_6
  recurrence5B2A3_coeff_7
  recurrence5B2A3_coeff_8
  recurrence5B2A3_coeff_9
  recurrence5B2A3_coeff_10
  recurrence5B2A3_coeff_11
  recurrence5B2A3_coeff_12
  recurrence5B2A3_coeff_13
  recurrence5B2A3_coeff_14
  recurrence5B2A3_coeff_15
  recurrence5B2A3_coeff_16
  recurrence5B2A3_coeff_17
  recurrence5B2A3_coeff_18
  recurrence5B2A3_coeff_19
  recurrence5B2A3_coeff_20
  recurrence5B2A3_coeff_21
  recurrence5B2A3_coeff_22
  recurrence5B2A3_coeff_23
  recurrence5B2A3_coeff_24
  recurrence5B2A3_coeff_25
  recurrence5B2A3_coeff_26
  recurrence5B2A3_coeff_27
  recurrence5B2A3_coeff_28
  recurrence5B2A3_coeff_29
  recurrence5B2A3_coeff_30
  recurrence5B2A3_coeff_31
  recurrence5B2A3_coeff_32
  recurrence5B2A3_coeff_33
  recurrence5B2A3_coeff_34
  recurrence5B2A3_coeff_35
  recurrence5B2A3_coeff_36
  recurrence5B2A3_coeff_37

attribute [local simp]
  recurrence5B2A3_coeff_38
  recurrence5B2A3_coeff_39
  recurrence5B2A3_coeff_40
  recurrence5B2A3_coeff_41
  recurrence5B2A3_coeff_42
  recurrence5B2A3_coeff_43
  recurrence5B2A3_coeff_44
  recurrence5B2A3_coeff_45
  recurrence5B2A3_coeff_46
  recurrence5B2A3_coeff_47
  recurrence5B2A3_coeff_48
  recurrence5B2A3_coeff_49
  recurrence5B2A3_coeff_50
  recurrence5B2A3_coeff_51
  recurrence5B2A3_coeff_52
  recurrence5B2A3_coeff_53
  recurrence5B2A3_coeff_54
  recurrence5B2A3_coeff_55
  recurrence5B2A3_coeff_56
  recurrence5B2A3_coeff_57
  recurrence5B2A3_coeff_58
  recurrence5B2A3_coeff_59
  recurrence5B2A3_coeff_60
  recurrence5B2A3_coeff_61
  recurrence5B2A3_coeff_62
  recurrence5B2A3_coeff_63
  recurrence5B2A3_coeff_64
  recurrence5B2A3_coeff_65
  recurrence5B2A3_coeff_66
  recurrence5B2A3_coeff_67
  recurrence5B2A3_coeff_68
  recurrence5B2A3_coeff_69
  recurrence5B2A3_coeff_70
  recurrence5B2A3_coeff_71
  recurrence5B2A3_coeff_72
  recurrence5B2A3_coeff_73
  recurrence5B2A3_coeff_74
  recurrence5B2A3_coeff_75
  recurrence5B2A3_coeff_76
  recurrence5B2A3_coeff_77
  recurrence5B2A3_coeff_78
  recurrence5B2A3_coeff_79
  recurrence5B2A3_coeff_80
  recurrence5B2A3_coeff_81
  recurrence5B2A3_coeff_82
  recurrence5B2A3_coeff_83
  recurrence5B2A3_coeff_84
  recurrence5B2A3_coeff_85
  recurrence5B2A3_coeff_86
  recurrence5B2A3_coeff_87
  recurrence5B2A3_coeff_88
  recurrence5B2A3_coeff_89
  recurrence5B2A3_coeff_90
  recurrence5B2A3_coeff_91
  recurrence5B2A3_coeff_92
  recurrence5B2A3_coeff_93
  recurrence5B2A3_coeff_94
  recurrence5B2A3_coeff_95
  recurrence5B2A3_coeff_96
  recurrence5B2A3_coeff_97
  recurrence5B2A3_coeff_98
  recurrence5B2A3_coeff_99
  recurrence5B2A3_coeff_100
  recurrence5B2A3_coeff_101

attribute [local simp]
  recurrence5B2A3_coeff_102
  recurrence5B2A3_coeff_103
  recurrence5B2A3_coeff_104
  recurrence5B2A3_coeff_105
  recurrence5B2A3_coeff_106
  recurrence5B2A3_coeff_107
  recurrence5B2A3_coeff_108
  recurrence5B2A3_coeff_109
  recurrence5B2A3_coeff_110
  recurrence5B2A3_coeff_111
  recurrence5B2A3_coeff_112
  recurrence5B2A3_coeff_113
  recurrence5B2A3_coeff_114
  recurrence5B2A3_coeff_115
  recurrence5B2A3_coeff_116
  recurrence5B2A3_coeff_117
  recurrence5B2A3_coeff_118
  recurrence5B2A3_coeff_119
  recurrence5B2A3_coeff_120
  recurrence5B2A3_coeff_121
  recurrence5B2A3_coeff_122
  recurrence5B2A3_coeff_123
  recurrence5B2A3_coeff_124
  recurrence5B2A3_coeff_125
  recurrence5B2A3_coeff_126
  recurrence5B2A3_coeff_127
  recurrence5B2A3_coeff_128
  recurrence5B2A3_coeff_129
  recurrence5B2A3_coeff_130
  recurrence5B2A3_coeff_131
  recurrence5B2A3_coeff_132
  recurrence5B2A3_coeff_133
  recurrence5B2A3_coeff_134
  recurrence5B2A3_coeff_135
  recurrence5B2A3_coeff_136
  recurrence5B2A3_coeff_137
  recurrence5B2A3_coeff_138
  recurrence5B2A3_coeff_139
  recurrence5B2A3_coeff_140
  recurrence5B2A3_coeff_141
  recurrence5B2A3_coeff_142
  recurrence5B2A3_coeff_143
  recurrence5B2A3_coeff_144
  recurrence5B2A3_coeff_145
  recurrence5B2A3_coeff_146
  recurrence5B2A3_coeff_147
  recurrence5B2A3_coeff_148
  recurrence5B2A3_coeff_149
  recurrence5B2A3_coeff_150
  recurrence5B2A3_coeff_151
  recurrence5B2A3_coeff_152
  recurrence5B2A3_coeff_153
  recurrence5B2A3_coeff_154
  recurrence5B2A3_coeff_155
  recurrence5B2A3_coeff_156
  recurrence5B2A3_coeff_157
  recurrence5B2A3_coeff_158
  recurrence5B2A3_coeff_159
  recurrence5B2A3_coeff_160
  recurrence5B2A3_coeff_161
  recurrence5B2A3_coeff_162
  recurrence5B2A3_coeff_163
  recurrence5B2A3_coeff_164
  recurrence5B2A3_coeff_165

attribute [local simp]
  recurrence5B2A3_coeff_166
  recurrence5B2A3_coeff_167
  recurrence5B2A3_coeff_168
  recurrence5B2A3_coeff_169
  recurrence5B2A3_coeff_170
  recurrence5B2A3_coeff_171
  recurrence5B2A3_coeff_172
  recurrence5B2A3_coeff_173
  recurrence5B2A3_coeff_174
  recurrence5B2A3_coeff_175
  recurrence5B2A3_coeff_176
  recurrence5B2A3_coeff_177
  recurrence5B2A3_coeff_178
  recurrence5B2A3_coeff_179
  recurrence5B2A3_coeff_180
  recurrence5B2A3_coeff_181
  recurrence5B2A3_coeff_182
  recurrence5B2A3_coeff_183
  recurrence5B2A3_coeff_184
  recurrence5B2A3_coeff_185
  recurrence5B2A3_coeff_186
  recurrence5B2A3_coeff_187
  recurrence5B2A3_coeff_188
  recurrence5B2A3_coeff_189
  recurrence5B2A3_coeff_190
  recurrence5B2A3_coeff_191
  recurrence5B2A3_coeff_192
  recurrence5B2A3_coeff_193
  recurrence5B2A3_coeff_194
  recurrence5B2A3_coeff_195
  recurrence5B2A3_coeff_196
  recurrence5B2A3_coeff_197
  recurrence5B2A3_coeff_198
  recurrence5B2A3_coeff_199
  recurrence5B2A3_coeff_200
  recurrence5B2A3_coeff_201
  recurrence5B2A3_coeff_202
  recurrence5B2A3_coeff_203
  recurrence5B2A3_coeff_204
  recurrence5B2A3_coeff_205
  recurrence5B2A3_coeff_206
  recurrence5B2A3_coeff_207
  recurrence5B2A3_coeff_208
  recurrence5B2A3_coeff_209
  recurrence5B2A3_coeff_210
  recurrence5B2A3_coeff_211
  recurrence5B2A3_coeff_212
  recurrence5B2A3_coeff_213
  recurrence5B2A3_coeff_214
  recurrence5B2A3_coeff_215
  recurrence5B2A3_coeff_216
  recurrence5B2A3_coeff_217
  recurrence5B2A3_coeff_218
  recurrence5B2A3_coeff_219
  recurrence5B2A3_coeff_220
  recurrence5B2A3_coeff_221
  recurrence5B2A3_coeff_222
  recurrence5B2A3_coeff_223
  recurrence5B2A3_coeff_224
  recurrence5B2A3_coeff_225
  recurrence5B2A3_coeff_226
  recurrence5B2A3_coeff_227
  recurrence5B2A3_coeff_228
  recurrence5B2A3_coeff_229

attribute [local simp]
  recurrence5B2A3_coeff_230
  recurrence5B2A3_coeff_231
  recurrence5B2A3_coeff_232
  recurrence5B2A3_coeff_233
  recurrence5B2A3_coeff_234
  recurrence5B2A3_coeff_235
  recurrence5B2A3_coeff_236
  recurrence5B2A3_coeff_237
  recurrence5B2A3_coeff_238
  recurrence5B2A3_coeff_239
  recurrence5B2A3_coeff_240
  recurrence5B2A3_coeff_241
  recurrence5B2A3_coeff_242
  recurrence5B2A3_coeff_243
  recurrence5B2A3_coeff_244
  recurrence5B2A3_coeff_245
  recurrence5B2A3_coeff_246
  recurrence5B2A3_coeff_247
  recurrence5B2A3_coeff_248
  recurrence5B2A3_coeff_249
  recurrence5B2A3_coeff_250
  recurrence5B2A3_coeff_251
  recurrence5B2A3_coeff_252
  recurrence5B2A3_coeff_253
  recurrence5B2A3_coeff_254
  recurrence5B2A3_coeff_255
  recurrence5B2A3_coeff_256
  recurrence5B2A3_coeff_257
  recurrence5B2A3_coeff_258
  recurrence5B2A3_coeff_259
  recurrence5B2A3_coeff_260
  recurrence5B2A3_coeff_261
  recurrence5B2A3_coeff_262
  recurrence5B2A3_coeff_263
  recurrence5B2A3_coeff_264
  recurrence5B2A3_coeff_265
  recurrence5B2A3_coeff_266
  recurrence5B2A3_coeff_267
  recurrence5B2A3_coeff_268
  recurrence5B2A3_coeff_269
  recurrence5B2A3_coeff_270
  recurrence5B2A3_coeff_271
  recurrence5B2A3_coeff_272
  recurrence5B2A3_coeff_273
  recurrence5B2A3_coeff_274
  recurrence5B2A3_coeff_275
  recurrence5B2A3_coeff_276
  recurrence5B2A3_coeff_277
  recurrence5B2A3_coeff_278
  recurrence5B2A3_coeff_279
  recurrence5B2A3_coeff_280
  recurrence5B2A3_coeff_281
  recurrence5B2A3_coeff_282
  recurrence5B2A3_coeff_283
  recurrence5B2A3_coeff_284
  recurrence5B2A3_coeff_285
  recurrence5B2A3_coeff_286
  recurrence5B2A3_coeff_287
  recurrence5B2A3_coeff_288
  recurrence5B2A3_coeff_289
  recurrence5B2A3_coeff_290
  recurrence5B2A3_coeff_291
  recurrence5B2A3_coeff_292
  recurrence5B2A3_coeff_293

attribute [local simp]
  recurrence5B2A3_coeff_294
  recurrence5B2A3_coeff_295
  recurrence5B2A3_coeff_296
  recurrence5B2A3_coeff_297
  recurrence5B2A3_coeff_298
  recurrence5B2A3_coeff_299
  recurrence5B2A3_coeff_300
  recurrence5B2A3_coeff_301
  recurrence5B2A3_coeff_302
  recurrence5B2A3_coeff_303
  recurrence5B2A3_coeff_304
  recurrence5B2A3_coeff_305
  recurrence5B2A3_coeff_306
  recurrence5B2A3_coeff_307
  recurrence5B2A3_coeff_308
  recurrence5B2A3_coeff_309

private theorem recurrence5Scalar1First_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (363 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_363 :
    recurrence5Scalar1First.coeff 363 =
      (((((130228831781422852342532007513893742798 * 10 ^ 70 +
        9111658660054404015783536567082233074621452570830486053678359617044356) * 10 ^ 70 +
        4498823570702353567154261053901431628008124224874670996114099700127208) * 10 ^ 70 +
        3693238921674778232065730981498994463258780873550666209901199204006964) * 10 ^ 70 +
        8676478602103847127479495963683873117215665914117061868701159699402644) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 54 +
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
    rw [show 214 = 4 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (364 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_364 :
    recurrence5Scalar1First.coeff 364 =
      -(((((50015860451403049793181038082958491765 * 10 ^ 70 +
        2378187572192225087080234738530056344275621964233940146486120707862569) * 10 ^ 70 +
        8499335010449575917725946454070703891441136501389457654152298803135805) * 10 ^ 70 +
        7616109559543005901529400147504304795681226981948177125142526295151876) * 10 ^ 70 +
        8198352687948240184036523031688442534107361103052966892277187816962522) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 55 +
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
    rw [show 214 = 3 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (365 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_365 :
    recurrence5Scalar1First.coeff 365 =
      (((((18506044205434117809099244555523369534 * 10 ^ 70 +
        0704601787339176152902365024413268628217856045154525259358365341917704) * 10 ^ 70 +
        9244322552922611625927077324851291193320635266879225489604782951251370) * 10 ^ 70 +
        4263746089556531644971297165885131385103427282645087231326290280621274) * 10 ^ 70 +
        8101354571219894607035741173406452908819370045603296441695141744727665) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 56 +
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
    rw [show 214 = 2 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (366 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_366 :
    recurrence5Scalar1First.coeff 366 =
      -(((((6625295074418750412180011969039914776 * 10 ^ 70 +
        5280610651224927836725574276627788696526674952155265031261378145929787) * 10 ^ 70 +
        5266953923382264482793480268716603593737779047909167221791237854707485) * 10 ^ 70 +
        7680428765456505026980215460809922901646584914115269288645212551396272) * 10 ^ 70 +
        3031324679872872009953778146758291841840263530473035538298051193770878) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 57 +
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
    rw [show 214 = 1 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (367 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_367 :
    recurrence5Scalar1First.coeff 367 =
      (((((2301620458213330697987041236874129240 * 10 ^ 70 +
        2975927575368155062058440804312594664854930679990581674350380560133772) * 10 ^ 70 +
        5926656513635636089225209840094130562126205636568529229769856897601395) * 10 ^ 70 +
        5685990349388429754949431727380248435291127389583549287977083287168631) * 10 ^ 70 +
        1560528749296032739511338936742641685663186090413712718571812911208711) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 58 +
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
  rw [recurrence5Scalar1First_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (368 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_368 :
    recurrence5Scalar1First.coeff 368 =
      -(((((777377654955696693390226704256878308 * 10 ^ 70 +
        4945789284167259598851657769009145805435885883820101669731343028608061) * 10 ^ 70 +
        5592959798095899203450978934995286285736711710403162372978163348478711) * 10 ^ 70 +
        6621662504089169782389999446343851712163777975605526378480144634720308) * 10 ^ 70 +
        6045547480336059132374293020721405088920626172599272480207847551333978) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 59 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 31 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (369 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_369 :
    recurrence5Scalar1First.coeff 369 =
      (((((255587165204946644950887514746534621 * 10 ^ 70 +
        2433088167581612388178385224898319421997673739032208145472650703549494) * 10 ^ 70 +
        4651451316017276625301372557393684366044403740913848975348147109430447) * 10 ^ 70 +
        8739421796204367520053168313788223493241716360137209532841060329939767) * 10 ^ 70 +
        2165717957933840011936569692110412387502358410452166331321600566447960) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 60 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 30 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (370 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_370 :
    recurrence5Scalar1First.coeff 370 =
      -(((((81860637605627872631131891250546834 * 10 ^ 70 +
        6823972563717394388242798620942067747342215915770942639856420843215948) * 10 ^ 70 +
        2538990817407465806395394959655355426894637091197385603172873720411314) * 10 ^ 70 +
        6922835048843572689315701241705703868700122801353081470500130409390849) * 10 ^ 70 +
        9242908113829429459537747804210888338401163147891337177375670529888373) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 61 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 29 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (371 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_371 :
    recurrence5Scalar1First.coeff 371 =
      (((((25549932824200060097805476698500133 * 10 ^ 70 +
        4218487751080688382590815681959036062213333203684706053067413529517911) * 10 ^ 70 +
        9292397778258695959537493599341417258884317214839380208025120525761131) * 10 ^ 70 +
        1259765073477544760101289606218811888174724192231258015635363631645133) * 10 ^ 70 +
        1912893520095573698354816833267127625455343671961299283778183970919579) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 62 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 28 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (372 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_372 :
    recurrence5Scalar1First.coeff 372 =
      -(((((7771236574751800757594287858476811 * 10 ^ 70 +
        6624103812585252914698910739990085344424724328121384004195374723121401) * 10 ^ 70 +
        1356223144638064378664459729225795756831357527836658461385811447687734) * 10 ^ 70 +
        4589734678341062972571030262058198655389806258416091095462168759126944) * 10 ^ 70 +
        9069543149001810357472520539616588433917319698461515774177817734000967) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 63 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 27 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (373 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_373 :
    recurrence5Scalar1First.coeff 373 =
      (((((2302799649611869962043794294180506 * 10 ^ 70 +
        3102206447343807602526277136995550703697794680636486277136674839885694) * 10 ^ 70 +
        2878436346119830493779414608353412564978732043726355999094525907527240) * 10 ^ 70 +
        7956287931319951560361224785649446063844290615284507135289855299723571) * 10 ^ 70 +
        2498701741051131450822976412832003215614174457020919233409853963878667) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 64 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 26 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (374 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_374 :
    recurrence5Scalar1First.coeff 374 =
      -(((((664422582334773082919737255962355 * 10 ^ 70 +
        1325792333558716823992879508606709463767722651696918717793676196960699) * 10 ^ 70 +
        9275937145304242966472686210760083279044762016179776855879247978869522) * 10 ^ 70 +
        8662073380682428441898123178035294450381215027684276499009298217220263) * 10 ^ 70 +
        9398828209668169218496897337723647130401283478480244640746200096168225) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 65 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 25 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (375 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_375 :
    recurrence5Scalar1First.coeff 375 =
      (((((186501311117250833459249018975303 * 10 ^ 70 +
        6634880919953329532192439768558493187633685245531097076041112372921178) * 10 ^ 70 +
        1832190711490858941150248792883750004898969308441028636420348896953448) * 10 ^ 70 +
        4135733153921807310248290897205640675889037931917623908823513985178070) * 10 ^ 70 +
        8021250315332926331650150373033017395091926703915869471413495500750535) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 66 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 24 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (376 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_376 :
    recurrence5Scalar1First.coeff 376 =
      -(((((50868770887676503479636127191413 * 10 ^ 70 +
        6824379623030563255861433377536190951295214535738770887585133440908593) * 10 ^ 70 +
        1340186843460229813485787814191863905695377943995950875120792388018565) * 10 ^ 70 +
        0180105132666621071659399568487305427133881042132678565908213725265361) * 10 ^ 70 +
        6972587788581822396118687691927822358242420434946745321166658098041643) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 67 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 23 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (377 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_377 :
    recurrence5Scalar1First.coeff 377 =
      (((((13460720658047785690639561628165 * 10 ^ 70 +
        6424830795578447132675490979830233462517497858309447270387344529523854) * 10 ^ 70 +
        5828773297337871113700370914550052508758540738562692008136065389198255) * 10 ^ 70 +
        8780238546018953045352131166742379379341890266055109306171728363905402) * 10 ^ 70 +
        1603273512770121644557325043516976907507026360437145927146246396707796) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 68 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 22 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (378 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_378 :
    recurrence5Scalar1First.coeff 378 =
      -(((((3448702657648910717759966212916 * 10 ^ 70 +
        0948171339595737864861743777123694039111214466562772314926945468126103) * 10 ^ 70 +
        5344434585723592184390484998584455716924933598796914988572275756772302) * 10 ^ 70 +
        3830689152657253564769001173669308974815038016636279234076363867751613) * 10 ^ 70 +
        7986785891034790268725725967102640130553205163008055586406980065990542) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 69 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 21 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (379 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_379 :
    recurrence5Scalar1First.coeff 379 =
      (((((853328862698686586656647604761 * 10 ^ 70 +
        5302210898951581756920255179683270376259265577756767105970474370727844) * 10 ^ 70 +
        4230236416563541963992679051590137364357674070813991504348612885592507) * 10 ^ 70 +
        7157300049387588282352878403519807325947869300261936043154613932063864) * 10 ^ 70 +
        7601842893554574568212919771713548058706418102352843955539602059986634) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 70 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 20 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (380 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_380 :
    recurrence5Scalar1First.coeff 380 =
      -(((((203287808023288764673747987076 * 10 ^ 70 +
        5462369763547682837070192453528242109669036974227941673868157749994076) * 10 ^ 70 +
        4778307642213141642502898147453542337905316303788390866767821037983899) * 10 ^ 70 +
        6839304910050063962685750950391379248063157925902332641901246289182518) * 10 ^ 70 +
        5544558909690141292101526182125318816488499237653348872394462882359093) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 71 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 19 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (381 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_381 :
    recurrence5Scalar1First.coeff 381 =
      (((((46456367459661177385663507032 * 10 ^ 70 +
        9677411948217055359910934198835263896982374753522929304838393786152214) * 10 ^ 70 +
        9621785683329136907375330593803587920452502120665280470195038360934628) * 10 ^ 70 +
        5835416995885089091753596915097165955914501007413185143630665010553129) * 10 ^ 70 +
        7852850239165870069206435144768088031704432937323497361271642749257862) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 72 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 18 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (382 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_382 :
    recurrence5Scalar1First.coeff 382 =
      -(((((10140539734052824895639526278 * 10 ^ 70 +
        9573388430821864000181207008319896867364579227057978751750655751043180) * 10 ^ 70 +
        5968547918397521640478767860681569382470996569301144176757094369956952) * 10 ^ 70 +
        1479309657222894499025148777492735213467354108108848190211270139608534) * 10 ^ 70 +
        3714432211699640019514139590326169936245343957353223463119865715002160) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 73 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 17 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (383 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_383 :
    recurrence5Scalar1First.coeff 383 =
      (((((2103984295550559112497722192 * 10 ^ 70 +
        3980613129107532897920681963635299059113384763653422074931044093764698) * 10 ^ 70 +
        1082641733233455856681248701698715073656794898446914844107649833358437) * 10 ^ 70 +
        4361670151155819716791810809182400540423118365756679995136681941154019) * 10 ^ 70 +
        7223810196092735152025782954450486137265767222385663555400214835292737) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 74 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 16 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (384 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_384 :
    recurrence5Scalar1First.coeff 384 =
      -(((((412707429014008512637226297 * 10 ^ 70 +
        3743411504274201331370202464282106431286170430178804980658265112863413) * 10 ^ 70 +
        8158476236146511702079566494266603450043776939335400342532448572728020) * 10 ^ 70 +
        3056186802345888464883294575061221236145918973198742395296575801968226) * 10 ^ 70 +
        3037072407351192529797628093387136997932897711329572723703204900520498) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 75 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 15 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (385 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_385 :
    recurrence5Scalar1First.coeff 385 =
      (((((76111850485655795164184489 * 10 ^ 70 +
        5007113086203222690251137237106556716478569603315948426271967982197979) * 10 ^ 70 +
        9995994336336425018089232955424108797766250282138993190562167310297676) * 10 ^ 70 +
        8517029661603707872300404614101110348663212486673306781333070409387691) * 10 ^ 70 +
        2983561861874056764477216678701523685113233044990430368819700887659677) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 76 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 14 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (386 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_386 :
    recurrence5Scalar1First.coeff 386 =
      -(((((13147937527159838741207635 * 10 ^ 70 +
        5478217377188696495940349377783703776814936987962670134616946609383269) * 10 ^ 70 +
        1798933639727347011408461329956240375217529085710144395546768334961788) * 10 ^ 70 +
        1594710752450195576136703449762721361679330021561857725534231193782379) * 10 ^ 70 +
        1136370827197924515538962928447225067413143946986822123797956186212632) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 77 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 13 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (387 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_387 :
    recurrence5Scalar1First.coeff 387 =
      (((((2141554636748593715432241 * 10 ^ 70 +
        8891798384520628910852311736136214002673747646758835007656533323392018) * 10 ^ 70 +
        8091503334046813311790033922496688995951741565097197323986670072793515) * 10 ^ 70 +
        5477958961628175284959620312439544865798002308710867598084592306954033) * 10 ^ 70 +
        5814120416334732467937171292014750636582794450979806360945444249066170) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 78 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 12 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (388 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_388 :
    recurrence5Scalar1First.coeff 388 =
      -(((((344874864362827267389579 * 10 ^ 70 +
        8788327969680680266833932463225331365185471412712296663053801358756096) * 10 ^ 70 +
        2897965282570183419171285178614277799803119031078135189311193787661481) * 10 ^ 70 +
        3749100822008834938910443780646591999873222396383005220497697356412670) * 10 ^ 70 +
        2891759809183900154625695960178249303158583982813497849769304320950254) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 79 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 11 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (389 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_389 :
    recurrence5Scalar1First.coeff 389 =
      (((((63905558054075490974135 * 10 ^ 70 +
        2264747889628864170310279332591876390558162814200459878018874052305385) * 10 ^ 70 +
        4572240368290660138288058892671105698139128253107177124911779472477914) * 10 ^ 70 +
        7305503238025546973673204161830715879097314082045581417568771442078909) * 10 ^ 70 +
        2375504469648800234841385778605789538048443728723793493671969268654305) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 80 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 10 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (390 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_390 :
    recurrence5Scalar1First.coeff 390 =
      -(((((16600734539622296644540 * 10 ^ 70 +
        2378197667765722724702637860218383406208911110792014993099897838461002) * 10 ^ 70 +
        4300637449797308630966316993806798932846087183605471126986848135573255) * 10 ^ 70 +
        1605696758761736879127106826508286377612497115542974740275296682650759) * 10 ^ 70 +
        5394941028462660823809460909634490565019962789677598561861857622949379) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 81 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 9 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (391 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_391 :
    recurrence5Scalar1First.coeff 391 =
      (((((5693052440255664114652 * 10 ^ 70 +
        7333911239546770378677813247263247722219794184833773485949503130574584) * 10 ^ 70 +
        3527782832689358830728405087944582134682644664905522304854786176113034) * 10 ^ 70 +
        0632554419030261203176145982241871694103973378368314699651287697538548) * 10 ^ 70 +
        6770323701929268372093943276032162618224191580474262913056826166800335) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 82 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 8 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (392 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_392 :
    recurrence5Scalar1First.coeff 392 =
      -(((((2064731189953531156540 * 10 ^ 70 +
        2551366719652907395303807500367558745740208253617957084160460505035552) * 10 ^ 70 +
        6366483513419647675202615325249987982292545853942320667973804706291310) * 10 ^ 70 +
        5118685739846271646076893439961023515717567396662912231630183117242769) * 10 ^ 70 +
        9479556767835141428991711693442188964387818853154522066919149148975347) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 83 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 7 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (393 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_393 :
    recurrence5Scalar1First.coeff 393 =
      (((((701273315599162058393 * 10 ^ 70 +
        8014609457427436594572371413157895979700804638809282152962749119659039) * 10 ^ 70 +
        2481893885522088950784579047209429598475011001835232286180481923199308) * 10 ^ 70 +
        7657540122874114135630242718214720317444556287827770446519967549608070) * 10 ^ 70 +
        5667052377540308543887430739268733007421860692329404751670744593669077) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 84 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 6 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (394 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_394 :
    recurrence5Scalar1First.coeff 394 =
      -(((((214340280363597508398 * 10 ^ 70 +
        9413385569602451306154020741584315267976671763890979580563805372592899) * 10 ^ 70 +
        2849887614677901314980386583870193234033110091646777628881394112881706) * 10 ^ 70 +
        8846853345693129038566872526868659386192183068769352465843286913231017) * 10 ^ 70 +
        2049025228868549646752792127602901729566655777809235769454531821275887) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 395 = 85 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 5 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (395 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_395 :
    recurrence5Scalar1First.coeff 395 =
      (((((57994778093371687979 * 10 ^ 70 +
        7051138483861799789251784858430053866789701049520256741046795451304805) * 10 ^ 70 +
        3222599939102524060438781850878800115874652331922469147184899129392518) * 10 ^ 70 +
        0842148030739907382572186868759297682500332816505721253596052700718495) * 10 ^ 70 +
        2414306312132051107994790221419437228062473085754205053762194160965489) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 396 = 86 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 4 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (396 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_396 :
    recurrence5Scalar1First.coeff 396 =
      -(((((13640177785473823463 * 10 ^ 70 +
        7891949618365825026847646116452877037072845098924017377149027745012193) * 10 ^ 70 +
        4968279238098199190291674869394823126045951291438817809134524265907188) * 10 ^ 70 +
        3698195741004417102098132376320555703663044835084194246135340995325681) * 10 ^ 70 +
        0824397229486270570795934271127218832222038880164921007296435466880548) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 397 = 87 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 3 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (397 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_397 :
    recurrence5Scalar1First.coeff 397 =
      (((((2686432163038793902 * 10 ^ 70 +
        8482475547826184336075379752661058982389848757156881669730822851890114) * 10 ^ 70 +
        4515773787114489370246608906389921408302945866715874998742424964042315) * 10 ^ 70 +
        8041826666997505746464928356044836444458451878308314373025262608018684) * 10 ^ 70 +
        8754145576121062132344834555776150782565400472856551503769428832634261) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 398 = 88 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 2 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (398 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_398 :
    recurrence5Scalar1First.coeff 398 =
      -(((((400209534863887034 * 10 ^ 70 +
        1370552008472767033963763602209213457153448189223779961542647800692654) * 10 ^ 70 +
        9138913094975769090316367766699468776973795569070578934940182214177417) * 10 ^ 70 +
        2187253562017579484061153761948651546828379936653659181865274778491840) * 10 ^ 70 +
        3897706391083313455802819571693853744639724917842099532559395125156807) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 399 = 89 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 1 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (399 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_399 :
    recurrence5Scalar1First.coeff 399 =
      (((((26601959173978393 * 10 ^ 70 +
        1498122463743461759448581467887389169846179452899069215906513074899737) * 10 ^ 70 +
        6484865232865399754628588751674034392300785155219096259364958217279423) * 10 ^ 70 +
        4063142159520634748095158981054206434983815788136667535467497295645565) * 10 ^ 70 +
        8486258668633615290686061877878656047892769769857089080318373286481673) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 400 = 90 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (400 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_400 :
    recurrence5Scalar1First.coeff 400 =
      (((((8439376669473111 * 10 ^ 70 +
        0491739929492375830757557989892805951308439399821658235182672376876649) * 10 ^ 70 +
        9014163788320626689961969068132416927574879348228917336184028620519205) * 10 ^ 70 +
        6155050477822889921684643705336596628830104331909926373852869470099200) * 10 ^ 70 +
        3995872395127497774628451169970921647711110546815537877198341505259371) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 401 = 91 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 31 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (401 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_401 :
    recurrence5Scalar1First.coeff 401 =
      -(((((4235457816773579 * 10 ^ 70 +
        4006549330263259545932052966264504943386711651341959736859566671888718) * 10 ^ 70 +
        5729003567809745674183625586610590379140769731762996216929011422045506) * 10 ^ 70 +
        8183657569944825660425130527657921962393282156906515802380553802656369) * 10 ^ 70 +
        5957104235665929315255246608363969228190792211334809403302831683643409) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 402 = 92 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 30 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (402 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_402 :
    recurrence5Scalar1First.coeff 402 =
      (((((1129146083449234 * 10 ^ 70 +
        2680476410888676047359923887076963512430798688886578607588367723385091) * 10 ^ 70 +
        2835696954851687314979553645446354476660745897209393299573951682677156) * 10 ^ 70 +
        3155701088896816700695826594468377526230905212121838584687649036804545) * 10 ^ 70 +
        4547878807728119012053290489511468552055861500500032377411469530564596) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 403 = 93 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 29 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (403 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_403 :
    recurrence5Scalar1First.coeff 403 =
      -(((((211863163324265 * 10 ^ 70 +
        2124114584817142382605282214827216997109404776355345143035438203352522) * 10 ^ 70 +
        0074776912234132434938023711894517332789937710600224192375089912830941) * 10 ^ 70 +
        1417534488950185242888362799494188548114101859943641526667979389853909) * 10 ^ 70 +
        1968493856822042987167971898148499841911385091232055104061661599123685) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 404 = 94 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 28 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (404 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_404 :
    recurrence5Scalar1First.coeff 404 =
      (((((25885788241129 * 10 ^ 70 +
        6732685619337941002409695908934759344534702154201502032772732772944931) * 10 ^ 70 +
        6346268780014402758670355647546739819279197662718847744341454800261056) * 10 ^ 70 +
        5601315407683517610777764791616705607627130865243069507349433760859749) * 10 ^ 70 +
        3055178611490298180690443568703876288204372315073298295797556571128748) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 405 = 95 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 27 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (405 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_405 :
    recurrence5Scalar1First.coeff 405 =
      -(((((383783390232 * 10 ^ 70 +
        3122614605499324989065334656247225794336578778580717864270180415148059) * 10 ^ 70 +
        0829512282630200003392143438853387208504212105899432582189069816608409) * 10 ^ 70 +
        3495753424640916190999357072224398807593620502366148146101769906242126) * 10 ^ 70 +
        2160817388969872184275068337563730461115437627962060732713911033439158) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 406 = 96 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 26 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (406 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_406 :
    recurrence5Scalar1First.coeff 406 =
      -(((((805656728340 * 10 ^ 70 +
        2642086327962740980640791264972250697308462201318405241593832081109732) * 10 ^ 70 +
        9539242107222943897572391630405764940628830761927976976563318752386351) * 10 ^ 70 +
        5202927472932384353410670473035918441385034348907979468231294244318065) * 10 ^ 70 +
        4851268182355552683847190955014475240808168175876950562186135888963858) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 407 = 97 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 25 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (407 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_407 :
    recurrence5Scalar1First.coeff 407 =
      (((((258442414135 * 10 ^ 70 +
        6497184290776273069450837078791953925987714257851743195458820800490389) * 10 ^ 70 +
        7329957978745524798879521146156819446882569442551975750563109991074203) * 10 ^ 70 +
        3827554400554044816009923485004442897024662448498404205273684138511341) * 10 ^ 70 +
        5626477526370836180249537991869917305431794697715703027875995327788335) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 408 = 98 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 24 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (408 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_408 :
    recurrence5Scalar1First.coeff 408 =
      -(((((50887673803 * 10 ^ 70 +
        3622053724105228211078190768033141587341862076893924061498529732752834) * 10 ^ 70 +
        0388188931466834350065086649419598102689213758570699048533974279851024) * 10 ^ 70 +
        2115836859162507326215027054051085170454671441686158432211397919203137) * 10 ^ 70 +
        5602917349248275046529216928935103128861435089267036769461672202321791) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 409 = 99 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 23 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (409 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_409 :
    recurrence5Scalar1First.coeff 409 =
      (((((6989534292 * 10 ^ 70 +
        8616977994171224642476943419756333546455874228629268451232274295361147) * 10 ^ 70 +
        4438886293930451154982901168604736447743753817049404788485403862570430) * 10 ^ 70 +
        6616608204885307709894597792442657479885862889209009270013324090012658) * 10 ^ 70 +
        2417019568501235078530074649826484380501509259825436844975708600878433) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 410 = 100 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 22 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (410 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_410 :
    recurrence5Scalar1First.coeff 410 =
      -(((((574323606 * 10 ^ 70 +
        6732789564175756449295120300158528212471872733889246190563689593334706) * 10 ^ 70 +
        9404361222964754704973734377323085949431691501999139279584250605152708) * 10 ^ 70 +
        9735982481356966541160144105144659532182275270856136418564923984504735) * 10 ^ 70 +
        6448613609013904425257630406645500265250485852134586129496736763875819) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 411 = 101 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 21 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (411 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_411 :
    recurrence5Scalar1First.coeff 411 =
      -(((((11527617 * 10 ^ 70 +
        5037517080533797341267580766039125642733688181423542594513881380153877) * 10 ^ 70 +
        2099965681351607469453323305483854354344561071534774627970946296399603) * 10 ^ 70 +
        9669390995363935389189642960656977734565830723711786763737971226587518) * 10 ^ 70 +
        4450877643792379179988443274123597083006091630551147422254457374196132) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 412 = 102 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 20 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (412 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_412 :
    recurrence5Scalar1First.coeff 412 =
      (((((13481705 * 10 ^ 70 +
        5025072317530348304858215730392752274358014544787111031635545313993281) * 10 ^ 70 +
        2779216264945734759300238308250397755241676859741208353087784516157920) * 10 ^ 70 +
        9116273720206166775076420019619195230621884510746111887663979891886802) * 10 ^ 70 +
        4568451008164041734988776360412023873230673362833945495723639762673704) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 413 = 103 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 19 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (413 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_413 :
    recurrence5Scalar1First.coeff 413 =
      -(((((2600901 * 10 ^ 70 +
        8198618711368405124730181745813903986719827135037887624200974273469705) * 10 ^ 70 +
        8227715484942109963701886345011990919723356168752604881823862690373502) * 10 ^ 70 +
        0494199392231625550905749982712214551313260864447818436286476749714171) * 10 ^ 70 +
        7100475761684766477607430603193378495742575954013956191482931215963850) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 414 = 104 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 18 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (414 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_414 :
    recurrence5Scalar1First.coeff 414 =
      (((((297676 * 10 ^ 70 +
        2731145769864593598284846161148119435234619951752584053738617024819533) * 10 ^ 70 +
        5990420835824358283412393674480564402609256570069716924671084289163217) * 10 ^ 70 +
        4159484132393380347797140462930015489176382608978525284274918876301735) * 10 ^ 70 +
        9321377581609711792734833848725789764816788941818001897512912730114845) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 415 = 105 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 17 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (415 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_415 :
    recurrence5Scalar1First.coeff 415 =
      -(((((18362 * 10 ^ 70 +
        3621537104287181086159722287828707870002206377604312755629271168688727) * 10 ^ 70 +
        1789762678462868099439594646970580230421165756516797964627276299862801) * 10 ^ 70 +
        2372731955350529440314418142736011318069751768338288690564942674534158) * 10 ^ 70 +
        9265112177164098770876575039249407734077642051948224515842737631964518) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 416 = 106 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 16 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (416 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_416 :
    recurrence5Scalar1First.coeff 416 =
      -(((((463 * 10 ^ 70 +
        5165870193893116261886297659305067381931858353936677548103450902730220) * 10 ^ 70 +
        9647063986047253395207717530338240178656434280687375442094635400470260) * 10 ^ 70 +
        4934653744669910401648926983195602011707630430505010836521012005170915) * 10 ^ 70 +
        7085407193151916045444916231830362166147759485885577837827345334337758) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 417 = 107 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 15 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (417 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_417 :
    recurrence5Scalar1First.coeff 417 =
      (((((251 * 10 ^ 70 +
        8435498801759532381501182041333280141449726807541069686016459021244721) * 10 ^ 70 +
        3284291691778686887612117520028729408625344052012160566670707863151331) * 10 ^ 70 +
        7491534984976039485568143506359555473353058890964037717973678522588816) * 10 ^ 70 +
        3102191656321158362350236020695921958556879316118173632987451098613974) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 418 = 108 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 14 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (418 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_418 :
    recurrence5Scalar1First.coeff 418 =
      -(((((28 * 10 ^ 70 +
        9700435561730367821557140295254344302434914791149148423061068578837828) * 10 ^ 70 +
        3314154529215451518635577064178924886494867712513308766605097215416393) * 10 ^ 70 +
        3362391686801869021003665428452350406386360632801957258221392154992539) * 10 ^ 70 +
        8638152138084861441837721387623377962155791508675141613481262553424018) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 419 = 109 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 13 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (419 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_419 :
    recurrence5Scalar1First.coeff 419 =
      (((((1 * 10 ^ 70 +
        4531131618277512279403761616038314464554143702095043550646661734784496) * 10 ^ 70 +
        1430486930020590692696786961606408502718469576122658320644082785542945) * 10 ^ 70 +
        5636429721560847912524141477239438930346996864176203837876542018886388) * 10 ^ 70 +
        0226356604578966457926774320022315064803064945808561335582723819887412) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 420 = 110 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 12 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (420 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_420 :
    recurrence5Scalar1First.coeff 420 =
      ((((472252831576884848271945347368232646153942235363596912807979563303500 * 10 ^ 70 +
        5936201819645101999203864550178823696036056866871151327365272506653145) * 10 ^ 70 +
        9180465406131121195821035059248892216497442650837198902680514707518698) * 10 ^ 70 +
        0312468958980947029309881022379647971266198148897473423570492409715142) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 421 = 111 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 11 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (421 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_421 :
    recurrence5Scalar1First.coeff 421 =
      -((((135164287606560089931178762794512018876583280170840042868554325944744 * 10 ^ 70 +
        0550649388581702145152656735677363624177714678594124071498588195384398) * 10 ^ 70 +
        4927030439289374255044726678275347959681434302284810473874989730368971) * 10 ^ 70 +
        5210389178681491419343796427798876300318812184784431036267308073072834) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 422 = 112 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 10 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (422 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_422 :
    recurrence5Scalar1First.coeff 422 =
      ((((9025355694893894555141931760383769335922165740348068253716836777981 * 10 ^ 70 +
        5227787760093144540301837764625243453038215857921786092475166199006923) * 10 ^ 70 +
        5541471056985914770945755556067986139713145650923093813594334517711213) * 10 ^ 70 +
        2172615846102820455079230426428512252321666256112402631985740560823858) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 423 = 113 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 9 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (423 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_423 :
    recurrence5Scalar1First.coeff 423 =
      -((((54370975051346613025030603938306279422880678015116699362545972809 * 10 ^ 70 +
        8635554465513352592842674789459913014671253962368175947367269365048513) * 10 ^ 70 +
        7535667870153955493207844420749577853019645252553531910847556220363840) * 10 ^ 70 +
        8586059958427060121846731128890380156067063996719417467565044385369611) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 424 = 114 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 8 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (424 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_424 :
    recurrence5Scalar1First.coeff 424 =
      -((((31340692655894316509676096716773173769352600734589622240466957121 * 10 ^ 70 +
        4835248210948394093032791462448693411609601182822256666296654765792720) * 10 ^ 70 +
        3087536051080109402712111114416712783805032005345003722496956497800872) * 10 ^ 70 +
        4374915215503208151303177431620667948029884251782455520886394480289667) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 425 = 115 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 7 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (425 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_425 :
    recurrence5Scalar1First.coeff 425 =
      ((((1837415783155364423362646627149448933681438275887097537056260320 * 10 ^ 70 +
        8847900662827033966392601971796759682723965840024100773009772936649752) * 10 ^ 70 +
        0896605917377058207979434156033408543130246032527795816821244365353895) * 10 ^ 70 +
        1790900758593541138896733610977722807027835338264576364780086084654589) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 426 = 116 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 6 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (426 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_426 :
    recurrence5Scalar1First.coeff 426 =
      ((((2545870972257130057779321872311671593532271869694210379388758 * 10 ^ 70 +
        9302995546215230679952076740689069974296365276611080257455613518442251) * 10 ^ 70 +
        8047673236181393477439492741800664973129998258684298834705787432155058) * 10 ^ 70 +
        0076604128466311961899774670421487030106434943993702350005004866466777) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 427 = 117 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 5 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (427 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_427 :
    recurrence5Scalar1First.coeff 427 =
      -((((3748676463093299984293544593357620305556234770858980607524199 * 10 ^ 70 +
        7448307005142527264707638644708240629861206338804450192620449038058168) * 10 ^ 70 +
        2373503090591866608519193208565121455522228692119044326987404100848799) * 10 ^ 70 +
        6339549548512201442951941564480118224606817049800651554902478575159365) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 428 = 118 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 4 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (428 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_428 :
    recurrence5Scalar1First.coeff 428 =
      ((((69901344031728961291306400300172674148649703795647778581968 * 10 ^ 70 +
        6222679278006464795042254851320122506736276493037313349281459782628661) * 10 ^ 70 +
        7775595253554418444445356909193311098537790660231300265085919370448114) * 10 ^ 70 +
        9888576025877611702072394340440669779692604593775479480341344166384524) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 429 = 119 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 3 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (429 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_429 :
    recurrence5Scalar1First.coeff 429 =
      ((((3828344087211655483280413233089137802921353174871741009657 * 10 ^ 70 +
        9493537223314005047728772258122300114022008585205862329361483928604587) * 10 ^ 70 +
        8281191973352746545722195561091794513181144073032982148651557296719118) * 10 ^ 70 +
        8490746316904425878346613829091574657591414897207778540426008149608447) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 430 = 120 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 2 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (430 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_430 :
    recurrence5Scalar1First.coeff 430 =
      -((((66672167825644118377171313976095593764232257498600387576 * 10 ^ 70 +
        4119675593025863714802943590859894622762241443030073071041884764712410) * 10 ^ 70 +
        0651446404216881840841372700148667390839345717364967640183402341288991) * 10 ^ 70 +
        7050774886245670223294732662321156715644585378988621263029915561225584) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 431 = 121 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 1 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (431 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_431 :
    recurrence5Scalar1First.coeff 431 =
      -((((2902403768011569363751866786042639791571594428778676791 * 10 ^ 70 +
        9706042311957238732938937887815122292116052058752122265912481177787167) * 10 ^ 70 +
        3735674159450727773993671368492894157526392407249772103999067789072253) * 10 ^ 70 +
        0834571242942686373028773364184612213591911975761907268770528567832037) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 122 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (432 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_432 :
    recurrence5Scalar1First.coeff 432 =
      -((((11184104622148940575213221649949505879285759963151864 * 10 ^ 70 +
        9845691446025936378017892919504519978697877876099217327561250919338057) * 10 ^ 70 +
        0244839412163259346139620053767912352013632064567124844448561271872968) * 10 ^ 70 +
        9324587892577026912308804949163909621434474404033301511305024847488882) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 123 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 31 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (433 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_433 :
    recurrence5Scalar1First.coeff 433 =
      ((((481156428427813080392714193554808349268069617898455 * 10 ^ 70 +
        5298852025203235511095846512103604670894756570011719282703660805203497) * 10 ^ 70 +
        6838425205386467176840391803728811246494168843973354922452071829438244) * 10 ^ 70 +
        5402990348361373792764864814797763454239220935005419475959648055596356) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 124 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 30 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (434 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_434 :
    recurrence5Scalar1First.coeff 434 =
      ((((6634498151625330617922825202978451234879318820816 * 10 ^ 70 +
        5222647018824278362779244797864304664128821235627116923493162693950931) * 10 ^ 70 +
        2104778463700239715179336310453649956678976245260328311345097064022774) * 10 ^ 70 +
        0206771404018604352079443918614533280397095407201740633114489660721724) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 125 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 29 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (435 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_435 :
    recurrence5Scalar1First.coeff 435 =
      ((((24317181000384976704531927824315010547045239387 * 10 ^ 70 +
        2868506332312160529878161860525196225175872459571075608785612467001131) * 10 ^ 70 +
        9806313328085505129388869157422958752133604881775534347914853899980888) * 10 ^ 70 +
        0738198200907548868498638741292639544636692543717761660227869856618028) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 126 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 28 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (436 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_436 :
    recurrence5Scalar1First.coeff 436 =
      -((((118564850472949426673334282781176998211592627 * 10 ^ 70 +
        1535775598378172879561533684468263235376226616057359641266514790880607) * 10 ^ 70 +
        5926771891155790162841394876463927703759763745281098726496022919454374) * 10 ^ 70 +
        4026809433592531152626620972262056036813779852143519911062933330322040) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 127 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 27 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (437 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_437 :
    recurrence5Scalar1First.coeff 437 =
      -((((1275572767306142388277044445321975310618523 * 10 ^ 70 +
        3394262775821375240630122560591641822025246289652594208992266271948691) * 10 ^ 70 +
        4414923441361611481028235228613334711178259917587035031400624334211267) * 10 ^ 70 +
        3688429488744437958264252683536162450295940072788333945322966760814972) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 128 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 26 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (438 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_438 :
    recurrence5Scalar1First.coeff 438 =
      -((((2781852380422489185650887773432617668779 * 10 ^ 70 +
        2587471832046773063353230121839881871324667674810542905333094570758284) * 10 ^ 70 +
        2496144601660350109810790919051160508422308057739805564529319548496950) * 10 ^ 70 +
        9101467753704310767979178893627758898340165158359478598537147459003758) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 129 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 25 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (439 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_439 :
    recurrence5Scalar1First.coeff 439 =
      ((((8459886969837855492296257000231380954 * 10 ^ 70 +
        9626630001291978409644561960771707950635368616485166901837155706825160) * 10 ^ 70 +
        8035902963445965081619342204337406784085633577385364576459541801221225) * 10 ^ 70 +
        8640255145684228115607632115411236709650950604765358554248994221161832) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 130 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 24 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (440 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_440 :
    recurrence5Scalar1First.coeff 440 =
      ((((45110536853480661937966533396409406 * 10 ^ 70 +
        9779248826872408825381408449130544953757626639637962390164729737511465) * 10 ^ 70 +
        9607093519602974952569311000898388316076989702569843763932153544617047) * 10 ^ 70 +
        7090999884854667484046918352993481551240316212325930584083074378744555) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 131 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 23 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (441 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_441 :
    recurrence5Scalar1First.coeff 441 =
      ((((12698740469275680251829998198911 * 10 ^ 70 +
        1377026600390237807751090299320157731524222963648375442598297821161420) * 10 ^ 70 +
        0056801290109008395914584296371817072924608819645038369379834913617192) * 10 ^ 70 +
        1295086466489226992285287283205138163265031307102394232119266269860988) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 132 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 22 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (442 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_442 :
    recurrence5Scalar1First.coeff 442 =
      -((((234808972905709987052154517924 * 10 ^ 70 +
        9916900054749400996446171011456974853510543229950547470023655927884581) * 10 ^ 70 +
        2899546873327454093551119662487238845394611644412921056634628107125559) * 10 ^ 70 +
        7151129209187698845633482789840287461373077317002437247956105562433144) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 133 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 21 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (443 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_443 :
    recurrence5Scalar1First.coeff 443 =
      -((((274908282810085993895046898 * 10 ^ 70 +
        7160372889271065837606954485122700189392803621196636358133380176895496) * 10 ^ 70 +
        3248212729627632517383971810232507663396535619630289530852050751729942) * 10 ^ 70 +
        9817408237659604329135031952069802163948623722888910809107453360707172) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 134 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 20 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (444 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_444 :
    recurrence5Scalar1First.coeff 444 =
      ((((538948504151812540014841 * 10 ^ 70 +
        0869262516178269429142790766333739218184945830267120056118976365233653) * 10 ^ 70 +
        6756566171351625195861306206861950269117163338942672604427147729416581) * 10 ^ 70 +
        8865840536490231414630873515204944626997781000969928890539401939681171) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 135 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 19 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (445 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_445 :
    recurrence5Scalar1First.coeff 445 =
      ((((891168916449430228552 * 10 ^ 70 +
        0889042940933258179187126430217526189281003640787326237299949520303274) * 10 ^ 70 +
        6805780340251963115579761273565258209431874747605033005338456920056553) * 10 ^ 70 +
        6973072790347118737726881171881099804024590589904662611971328198343299) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 136 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 18 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (446 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_446 :
    recurrence5Scalar1First.coeff 446 =
      -((((487961651115542800 * 10 ^ 70 +
        9360042863018008773333045389649907225512196861356098099612649149570253) * 10 ^ 70 +
        6699332857313310427602594447330907066800445345484559207617313946404297) * 10 ^ 70 +
        8858486597885769144325088070480698665507807809412414845041914953910066) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 137 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 17 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (447 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_447 :
    recurrence5Scalar1First.coeff 447 =
      -((((991384488399288 * 10 ^ 70 +
        5766327204768841494325860169590342995586900865738386154878357562950986) * 10 ^ 70 +
        8279233723418518538956869829011873138310898451638527194138625683225459) * 10 ^ 70 +
        0640918784177214522157400918229212259932999798395677491815173000840217) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 138 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 16 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (448 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_448 :
    recurrence5Scalar1First.coeff 448 =
      -((((13861998210 * 10 ^ 70 +
        9345373730972955608247097008212992633667298491227106688713928786576472) * 10 ^ 70 +
        9952559167340613681138149309785029913798872980105180018430769128959174) * 10 ^ 70 +
        6679842211672856184878482617060626141034277268242082518066975100341018) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 139 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 15 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (449 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_449 :
    recurrence5Scalar1First.coeff 449 =
      ((((254713654 * 10 ^ 70 +
        8141042682882626106326237507448794834677019851640814511811013951419508) * 10 ^ 70 +
        3174429743411661834352276461320438970509336932311370258547513121510624) * 10 ^ 70 +
        9291350421482618636660723108148813691998462321077743797950316453870956) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 140 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 14 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (450 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_450 :
    recurrence5Scalar1First.coeff 450 =
      ((((32081 * 10 ^ 70 +
        0506056010038488238439314882152692781176428938448104841108458629867778) * 10 ^ 70 +
        0156871017792527641990972290238358904832652599917403352146852661943683) * 10 ^ 70 +
        9672114854968205175532839163286765059895043503517528326096523345312304) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 141 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 13 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (451 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_451 :
    recurrence5Scalar1First.coeff 451 =
      -((((5 * 10 ^ 70 +
        7916173446473636983047293028778772049046597567700313609820951131294463) * 10 ^ 70 +
        2488484793665686305549794401998332483827980954327089429897614871934623) * 10 ^ 70 +
        4391396337554450200326326477827905778120860125661876384943534045492023) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 142 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 12 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (452 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_452 :
    recurrence5Scalar1First.coeff 452 =
      -(((7680969707241534898047575861496462294605952005163567454821021937012 * 10 ^ 70 +
        2542756664393950883906517415342889987119804318947529996515236398743261) * 10 ^ 70 +
        8368530476008548146816614008080138014337951590845201467122235803712123) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 143 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 11 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (453 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_453 :
    recurrence5Scalar1First.coeff 453 =
      (((49041009014711000830654059142411779696660593113376674376948484 * 10 ^ 70 +
        8142708842783927186107055837355079553605496050189328596533420382335174) * 10 ^ 70 +
        6524124814046699425090239054645954244395383206826830836305470831610137) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 144 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 10 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (454 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_454 :
    recurrence5Scalar1First.coeff 454 =
      (((8521163611044084538566697909216171963312172172826978896097 * 10 ^ 70 +
        7760054896912431545246368689431648548021783905872088248013503680384624) * 10 ^ 70 +
        6233385853031354996440954010254417955242379003722111039973282313014896) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 145 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 9 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (455 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_455 :
    recurrence5Scalar1First.coeff 455 =
      (((70155605612738480266150420383016805581208057921919891 * 10 ^ 70 +
        0357802345987321071822788399856784439332352573553697616027305221759254) * 10 ^ 70 +
        9830258636966256503925865872406656241660378596842174757542870430747632) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 146 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 8 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (456 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_456 :
    recurrence5Scalar1First.coeff 456 =
      -(((516495102308805854918776742754027602613464000946 * 10 ^ 70 +
        4437862169051797394566207737467440243360998990683049042226491881340341) * 10 ^ 70 +
        4457244308208553276611470094477898041990095028190653105000703352233165) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 147 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 7 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (457 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_457 :
    recurrence5Scalar1First.coeff 457 =
      -(((1485528387702119814413912852601714893743022 * 10 ^ 70 +
        0171762729614574812801422078432213764142768015954606263686317461628551) * 10 ^ 70 +
        7742660034103325336957689538617382217528645902366362877206896184525274) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 148 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 6 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (458 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_458 :
    recurrence5Scalar1First.coeff 458 =
      -(((145817521960573837914808371193785448 * 10 ^ 70 +
        1989324207614317648925203661893345137618131517772450748310365909900413) * 10 ^ 70 +
        6485447253028792009127484367617767399299973344528393675304169969905680) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 149 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 5 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (459 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_459 :
    recurrence5Scalar1First.coeff 459 =
      (((792522897257759744008041117671 * 10 ^ 70 +
        5464885160428330702723568906201884446326270805107956373901309604580235) * 10 ^ 70 +
        2928657560654332097613666357794459824591507958534342299316605543729857) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 150 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 4 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (460 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_460 :
    recurrence5Scalar1First.coeff 460 =
      (((55701155651468000559349 * 10 ^ 70 +
        4435579482258595462453373917391986694010257084618813039192344586967006) * 10 ^ 70 +
        9862428426367921313542118511690942175490887429695501533078863121298002) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 151 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 3 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (461 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_461 :
    recurrence5Scalar1First.coeff 461 =
      -(((702918900741405 * 10 ^ 70 +
        3584614625329394388215330164757408293324769643742539620672173502653737) * 10 ^ 70 +
        4921900967990138907150093723561945430706805088129531600710284158757211) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 152 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 2 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (462 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_462 :
    recurrence5Scalar1First.coeff 462 =
      -(((41280594 * 10 ^ 70 +
        2200647120801031177856229056947758002358174952954919084169730100543802) * 10 ^ 70 +
        1006954075536957280704837621614921683127870124327041246077816518827130) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 153 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 1 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
