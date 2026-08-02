/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

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
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115

attribute [local simp]
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
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
  recurrence4B3A4_coeff_13
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
  recurrence4B3A4_coeff_14
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
  recurrence4B3A4_coeff_15
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
  recurrence4B3A4_coeff_16
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
  recurrence4B3A4_coeff_17
  recurrence4B3A4_coeff_170
  recurrence4B3A4_coeff_171
  recurrence4B3A4_coeff_172
  recurrence4B3A4_coeff_173

attribute [local simp]
  recurrence4B3A4_coeff_174
  recurrence4B3A4_coeff_175
  recurrence4B3A4_coeff_176
  recurrence4B3A4_coeff_177
  recurrence4B3A4_coeff_178
  recurrence4B3A4_coeff_179
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_180
  recurrence4B3A4_coeff_181
  recurrence4B3A4_coeff_182
  recurrence4B3A4_coeff_183
  recurrence4B3A4_coeff_184
  recurrence4B3A4_coeff_185
  recurrence4B3A4_coeff_186
  recurrence4B3A4_coeff_187
  recurrence4B3A4_coeff_188
  recurrence4B3A4_coeff_189
  recurrence4B3A4_coeff_19
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
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
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
  recurrence4B3A4_coeff_21
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
  recurrence4B3A4_coeff_22
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
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_230

attribute [local simp]
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_24
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
  recurrence4B3A4_coeff_25
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
  recurrence4B3A4_coeff_26
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
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41

attribute [local simp]
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar2First_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (171 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_171 :
    recurrence4Scalar2First.coeff 171 =
      -(((((241079209 * 10 ^ 70 +
        9381030105053601149449731200938843776488175225285764839573571733877051) * 10 ^ 70 +
        0869378571345891739344836394863873122581514367850998498086776962891516) * 10 ^ 70 +
        7267920684986803734863033023644669144765535209383512840000963608995273) * 10 ^ 70 +
        6524924455526068106865218144070266540976213677751705668284023928912282) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (171 - x)) = _
  rw [show 172 = 1 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (172 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_172 :
    recurrence4Scalar2First.coeff 172 =
      (((((737593409 * 10 ^ 70 +
        5773800110745300170212888060703209762583476881150713367297462478011814) * 10 ^ 70 +
        4462210830952338790997132055518640952996710030609752119217228279893992) * 10 ^ 70 +
        6421035358026931505127433029168577822512098578840389477853745935611155) * 10 ^ 70 +
        1282562391150544937446598356297343919287055027539927217310839434856419) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (172 - x)) = _
  rw [show 173 = 1 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (173 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (173 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_173 :
    recurrence4Scalar2First.coeff 173 =
      -(((((2222911756 * 10 ^ 70 +
        4187699473442366043418865197064618661937699826773778335746516163887710) * 10 ^ 70 +
        0138742471988491538657542291090500867331237556693335136142972159226789) * 10 ^ 70 +
        3471485880077124332794717591084575504009979205430957168534017809813238) * 10 ^ 70 +
        2895808652672387400357766084668569727630813926165809166794724538031947) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (173 - x)) = _
  rw [show 174 = 1 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (174 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (174 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_174 :
    recurrence4Scalar2First.coeff 174 =
      (((((6599330389 * 10 ^ 70 +
        3495945544027281891016073009056218423266039104646174469058103086194845) * 10 ^ 70 +
        3369232764256985484731683078615263886657356864950321201319404777988459) * 10 ^ 70 +
        3494159243143734884358204142069466602651408255395945346524025440215420) * 10 ^ 70 +
        6704504829380914565694817405930927535514956056400673844729933412312393) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (174 - x)) = _
  rw [show 175 = 1 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 12 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (175 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (175 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_175 :
    recurrence4Scalar2First.coeff 175 =
      -(((((19300731266 * 10 ^ 70 +
        7310835759145566160745815989630900819475401991192630548507962016456669) * 10 ^ 70 +
        3011765450926358623052009312898219025814388857174258165712249865377157) * 10 ^ 70 +
        7277202361586505342378005538056122792677058133439491304521624131993220) * 10 ^ 70 +
        8144384455857393655004215359702384820370681683147875933931367118394229) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (175 - x)) = _
  rw [show 176 = 1 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 12 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (176 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (176 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_176 :
    recurrence4Scalar2First.coeff 176 =
      (((((55611801887 * 10 ^ 70 +
        6947610307497093433194125762156053800750696058348888536399982263271349) * 10 ^ 70 +
        7490738371286997676095293389877364959359730952136135064455624381324383) * 10 ^ 70 +
        6591812522122683879547336717816971916940178999449115247496357129030722) * 10 ^ 70 +
        5056118988920061276254024376811230661452687808040359232602031561555899) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (176 - x)) = _
  rw [show 177 = 1 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 12 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (177 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (177 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_177 :
    recurrence4Scalar2First.coeff 177 =
      -(((((157870810029 * 10 ^ 70 +
        7307067922524107190654116568348765660573129709887863402745757674600633) * 10 ^ 70 +
        1691763281460415259552410763761123971308309952225386374727097014691567) * 10 ^ 70 +
        4555634195274004953040376891213239566291611344254177319166822025241534) * 10 ^ 70 +
        7861717025602298536287495864925680652611706600921280428422153060173839) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (177 - x)) = _
  rw [show 178 = 1 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 12 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (178 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (178 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_178 :
    recurrence4Scalar2First.coeff 178 =
      (((((441570481406 * 10 ^ 70 +
        2522227689140765206405951047194541841937087562523568381694000922245650) * 10 ^ 70 +
        1944342415183742333854987240459634654510274331517919211134789406132584) * 10 ^ 70 +
        6653841705431619514900983990778386678824365435742492305774190417068481) * 10 ^ 70 +
        5732001211851683950617893088295385500398215494564313941642322809469228) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (178 - x)) = _
  rw [show 179 = 1 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 12 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (179 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (179 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_179 :
    recurrence4Scalar2First.coeff 179 =
      -(((((1216977439645 * 10 ^ 70 +
        5243839027997053670059817198293458838473476894321533185707771924206761) * 10 ^ 70 +
        4939232857579554418637088161704390583417098418158844397038152379868042) * 10 ^ 70 +
        8140111853859234249941087014816752653226324062000542546424506231597460) * 10 ^ 70 +
        6969007224226846501380558445586717862551038455960986157604564794136769) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (179 - x)) = _
  rw [show 180 = 1 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 12 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (180 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (180 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_180 :
    recurrence4Scalar2First.coeff 180 =
      (((((3304985930460 * 10 ^ 70 +
        6928809673796225910619795646817356104571011799174477478400062574758190) * 10 ^ 70 +
        8237651788283101157170081724599457251539849156576188872261760585900991) * 10 ^ 70 +
        9985846081225998513061623576657873992838892116597362748094292578322115) * 10 ^ 70 +
        3064492200406854673452374179111833202200799276495659645756887788139460) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (180 - x)) = _
  rw [show 181 = 1 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 12 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (181 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (181 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_181 :
    recurrence4Scalar2First.coeff 181 =
      -(((((8844655607596 * 10 ^ 70 +
        5318281309700019213364584485452093609292664686970126110872136328117075) * 10 ^ 70 +
        8702015821478119344709385703477103761370234088613810326085652575537631) * 10 ^ 70 +
        6438618170748649195290583992228237866480297353968332557980182326346265) * 10 ^ 70 +
        7685436698398295748196404679094215909293615089733891053602798012797835) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (181 - x)) = _
  rw [show 182 = 1 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 12 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (182 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (182 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_182 :
    recurrence4Scalar2First.coeff 182 =
      (((((23325740408793 * 10 ^ 70 +
        7594099256754098626449209084634365735572840959556672793256010514200820) * 10 ^ 70 +
        5204882134129129130682840357970766071449790036358435638748915255672249) * 10 ^ 70 +
        7101582098378375110042207437746499098635139552573288694410378765073819) * 10 ^ 70 +
        5151621285005506072830453332550368451993558334533532196307977015859945) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (182 - x)) = _
  rw [show 183 = 1 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 12 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (183 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (183 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_183 :
    recurrence4Scalar2First.coeff 183 =
      -(((((60624961457440 * 10 ^ 70 +
        4963834766430232402961137348711543060844410846855263380216364168604376) * 10 ^ 70 +
        9918206358947204739651237088824941782148324016837017518528397532181358) * 10 ^ 70 +
        7451135053972781952817453264761814741656573962618005437276282695009574) * 10 ^ 70 +
        7523093066970800702259217271627272775601793529381114353236247327194499) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (183 - x)) = _
  rw [show 184 = 1 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 12 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (184 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (184 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_184 :
    recurrence4Scalar2First.coeff 184 =
      (((((155291157784187 * 10 ^ 70 +
        4544780764725475732405744093625772266990748188116773455457636396140970) * 10 ^ 70 +
        3694592304061184403155603844956071721243737749497326227449164900024092) * 10 ^ 70 +
        3485671500022760634695014205974043499699664158165209868381719263503975) * 10 ^ 70 +
        1592222361121353927956790956704658773232379696903698557061166850271792) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (184 - x)) = _
  rw [show 185 = 1 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 12 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (185 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (185 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_185 :
    recurrence4Scalar2First.coeff 185 =
      -(((((392047105942178 * 10 ^ 70 +
        0395426612813609522725426840468881050348408208261300370832375794615971) * 10 ^ 70 +
        1088512509043124102337963792832518550643010656988999755006398591389257) * 10 ^ 70 +
        1598053122936816096557222696546503852985342363719131630693565719113907) * 10 ^ 70 +
        9230144854491581746880193796800073439257774471274266884411299350547398) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (185 - x)) = _
  rw [show 186 = 1 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 12 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (186 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (186 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_186 :
    recurrence4Scalar2First.coeff 186 =
      (((((975534159064079 * 10 ^ 70 +
        4959396778396677078583870727045084629106975609247830031413050025059146) * 10 ^ 70 +
        6782499945662050761007702103062506008406014359188513052149404068506536) * 10 ^ 70 +
        0279680266231875251915053373647399296099962014548595008144181055527714) * 10 ^ 70 +
        8083659413601152710881075008032931293312306047468340771715276962507603) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (186 - x)) = _
  rw [show 187 = 1 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 12 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (187 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (187 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_187 :
    recurrence4Scalar2First.coeff 187 =
      -(((((2392628261836013 * 10 ^ 70 +
        7623090773876025342524437974913711316226890723141930513524614539451822) * 10 ^ 70 +
        1513554665964531304152461253301551036329009663780435561845049165919301) * 10 ^ 70 +
        1770628203515130674560515618328498248325937850385117285404465452375018) * 10 ^ 70 +
        8264890779637394460699829062670032819329330553425669092379256227285388) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (187 - x)) = _
  rw [show 188 = 1 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 12 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (188 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (188 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_188 :
    recurrence4Scalar2First.coeff 188 =
      (((((5784311788478297 * 10 ^ 70 +
        1690801766450052672183496657122004079591048412592785529790744117402896) * 10 ^ 70 +
        0230972719401433777188999038273520623643394973293947062033984350497726) * 10 ^ 70 +
        0276314309791883733664952067204673156059582010061680719225788987330950) * 10 ^ 70 +
        3608799108740181011257400077937424441374046493296155610833508220790487) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (188 - x)) = _
  rw [show 189 = 1 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 12 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (189 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (189 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_189 :
    recurrence4Scalar2First.coeff 189 =
      -(((((13784355699294081 * 10 ^ 70 +
        7098034837858080183907528213773588034844922483177616616336842764405600) * 10 ^ 70 +
        4792473673412787525395519003744757828263161929859648069437067056516569) * 10 ^ 70 +
        0049818726413331496666726111082654799703577859762493622188051709278936) * 10 ^ 70 +
        8807023765411246781820134590315649429056614422309864156294020359381281) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (189 - x)) = _
  rw [show 190 = 1 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 12 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (190 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (190 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_190 :
    recurrence4Scalar2First.coeff 190 =
      (((((32381245257927927 * 10 ^ 70 +
        1442431716195842442647604874945403360262631911182250542828693290345601) * 10 ^ 70 +
        9991093779441766926384830028332564654334709369376191182589353419475948) * 10 ^ 70 +
        3588080426032654336749846338795794257425438641782933786020397728178427) * 10 ^ 70 +
        4934090647519218347144556405981244608082034062014734241561042189895177) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (190 - x)) = _
  rw [show 191 = 1 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 12 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (191 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (191 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_191 :
    recurrence4Scalar2First.coeff 191 =
      -(((((74987055983252408 * 10 ^ 70 +
        1131905462800670697582743445084531651551889311916703998462830086331789) * 10 ^ 70 +
        9703752717968123514954868346716178719303441591969887683137112650894854) * 10 ^ 70 +
        3355495131088718369508634288791924264834591299853431226425446742106530) * 10 ^ 70 +
        2861542584453833769206849149066729315347774416620992984392614148663635) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (191 - x)) = _
  rw [show 192 = 1 +
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
    rw [show 31 = 12 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (192 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (192 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_192 :
    recurrence4Scalar2First.coeff 192 =
      (((((171189659646209543 * 10 ^ 70 +
        3982270515015781570735378270264308397407631126718213676955567786481124) * 10 ^ 70 +
        6024990305988771905653409808231902678648129206667467611693599167257415) * 10 ^ 70 +
        4552773585463754586849360977724343485932899202492637307011133865356852) * 10 ^ 70 +
        6035235044798203897402349728058178327403714734546725696481680122765035) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (192 - x)) = _
  rw [show 193 = 1 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 12 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (193 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (193 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_193 :
    recurrence4Scalar2First.coeff 193 =
      -(((((385282610356699744 * 10 ^ 70 +
        6894919657586028442132660137071710017695726301402184091196585566407978) * 10 ^ 70 +
        6137156854058748564208989861621485670526017592437866449800163521985082) * 10 ^ 70 +
        3953086457224612905464057537779855473045095169674371094700432563882758) * 10 ^ 70 +
        5694466841624597864227978546765351716953251217848853734012850278682423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (193 - x)) = _
  rw [show 194 = 1 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 12 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (194 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (194 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_194 :
    recurrence4Scalar2First.coeff 194 =
      (((((854876795581158144 * 10 ^ 70 +
        4071526780779400870511258587126754126843932531848527850424670667258355) * 10 ^ 70 +
        1369771757563277422912051366675587967576550648825356830408429843113477) * 10 ^ 70 +
        1263838793786150158285163401124519678336092895380482969569545583521801) * 10 ^ 70 +
        3940616591358084991380754134942431153553338838423086546854416325442673) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (194 - x)) = _
  rw [show 195 = 1 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 12 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (195 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (195 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_195 :
    recurrence4Scalar2First.coeff 195 =
      -(((((1870082995272205631 * 10 ^ 70 +
        4056800262556395233124358886959906183591321268586836450794939013041065) * 10 ^ 70 +
        9754457871881064652705922238097529852889006594086415143445124902985971) * 10 ^ 70 +
        2763837261621533550328668675371623119332246763445941089670947664847082) * 10 ^ 70 +
        2188517084700853122879775248593147000748350478930512110995328152615616) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (195 - x)) = _
  rw [show 196 = 1 +
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
  rw [recurrence4Scalar2First_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (196 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (196 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_196 :
    recurrence4Scalar2First.coeff 196 =
      (((((4033312316734543360 * 10 ^ 70 +
        5603151527714262748869151652945642430456970406899161962680316279671863) * 10 ^ 70 +
        9478942711152633874691493792963581176588931009681242019951093400348503) * 10 ^ 70 +
        9734371260777055012840473972177555928474272296721296170515224191096581) * 10 ^ 70 +
        2858557915258548796236059204922375882658092892213263549898288497490698) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (196 - x)) = _
  rw [show 197 = 1 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 12 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (197 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (197 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_197 :
    recurrence4Scalar2First.coeff 197 =
      -(((((8576621173821210402 * 10 ^ 70 +
        5445189167835915356057430683265476239156453547696800039138965402619066) * 10 ^ 70 +
        5748183803729365226157079944704499829714099543567048352954836018410025) * 10 ^ 70 +
        0499387089506555317886574175441460961487830635144347084984099702890876) * 10 ^ 70 +
        0258004804830938869717738962959945228346476078938146848069972945812109) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (197 - x)) = _
  rw [show 198 = 1 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (198 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (198 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_198 :
    recurrence4Scalar2First.coeff 198 =
      (((((17981800883634325917 * 10 ^ 70 +
        5597837219831737644581508983296334184295008773452243104907952456108251) * 10 ^ 70 +
        3178407149561320417904694653886577304347087886997404659742078500900972) * 10 ^ 70 +
        5045356571734003913173992252506307292394662247439279837375262108552853) * 10 ^ 70 +
        6715164874295896769698289554635764218698128662084433092173659711468074) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (198 - x)) = _
  rw [show 199 = 1 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 12 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (199 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (199 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_199 :
    recurrence4Scalar2First.coeff 199 =
      -(((((37172458629946459862 * 10 ^ 70 +
        3874746709755947164233195566730674376435335321414921907215222139058379) * 10 ^ 70 +
        9699053525727588531069174676820844730073885374540263146484886265255699) * 10 ^ 70 +
        9370216485702678250542505380179545628002111520374490651642469268481104) * 10 ^ 70 +
        5730320196947465600442561396809514614079317487632381302066592040951762) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (199 - x)) = _
  rw [show 200 = 1 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 12 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (200 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (200 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_200 :
    recurrence4Scalar2First.coeff 200 =
      (((((75768463674414466377 * 10 ^ 70 +
        1177534146027818680017935282648983912952387072823995010469239028200047) * 10 ^ 70 +
        0313334460873391990874644126272781698087741715417601565140932322835510) * 10 ^ 70 +
        6783675141106409097526178914052769010934522513910005985365987566495808) * 10 ^ 70 +
        6210370921492968555189147908799439495594837840651363142051126795488218) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (200 - x)) = _
  rw [show 201 = 1 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 12 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (201 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (201 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_201 :
    recurrence4Scalar2First.coeff 201 =
      -(((((152279726252937940591 * 10 ^ 70 +
        7139258558591258740732161949221464960031158468804670387632582207009758) * 10 ^ 70 +
        8176352855993746017069265838371558249414283862206363315566326611581289) * 10 ^ 70 +
        4319009448348153225238362910298318812931779544980968413266449813703657) * 10 ^ 70 +
        2240075478563194328914282197216884726527771568563367309541930677687196) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (201 - x)) = _
  rw [show 202 = 1 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 12 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (202 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (202 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_202 :
    recurrence4Scalar2First.coeff 202 =
      (((((301778842787117668334 * 10 ^ 70 +
        6209149473179599613952114836602458901334113952320600239569875181355671) * 10 ^ 70 +
        7762917365260796740934869748388027927137699466758423253646565228999036) * 10 ^ 70 +
        8056582331066139214069463096764261449839098776784124593883891452945569) * 10 ^ 70 +
        3248916124961193115948099421398915620958987670313735787627642465889302) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (202 - x)) = _
  rw [show 203 = 1 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 12 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (203 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (203 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_203 :
    recurrence4Scalar2First.coeff 203 =
      -(((((589704745700436225499 * 10 ^ 70 +
        8916843706277633828753412748318102020193459180657722322356541711678719) * 10 ^ 70 +
        3005214416631780874118136060505856761493144149092810649198068074293650) * 10 ^ 70 +
        3746577329802613832084399105211823221000526655268151770924317363232871) * 10 ^ 70 +
        3289657423228482511751689136137318708436752043144265441626973510867216) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (203 - x)) = _
  rw [show 204 = 1 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 12 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (204 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (204 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_204 :
    recurrence4Scalar2First.coeff 204 =
      (((((1136278966547240786560 * 10 ^ 70 +
        5751916421942941370857499635852082764782996059090262373928888941378639) * 10 ^ 70 +
        0679505686596104281307613179847351543921746591792917262503603569563269) * 10 ^ 70 +
        3355320283671240019450592544293179129437403921522183395050347249379337) * 10 ^ 70 +
        0486100562487008833549940523184745498684499962566937050120110373253007) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (204 - x)) = _
  rw [show 205 = 1 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 12 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (205 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (205 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_205 :
    recurrence4Scalar2First.coeff 205 =
      -(((((2158959662621271113350 * 10 ^ 70 +
        6550319745176940943565737540365195448306171092884714715454079239235422) * 10 ^ 70 +
        0342026788912890260291799941745162364135079062985963611136783797808951) * 10 ^ 70 +
        8254395944062540018774293027597804444801458654872905133809549402015952) * 10 ^ 70 +
        4944696961354604287479733137796955601941153901661746078765029202949790) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (205 - x)) = _
  rw [show 206 = 1 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 12 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (206 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (206 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_206 :
    recurrence4Scalar2First.coeff 206 =
      (((((4044988766566391573057 * 10 ^ 70 +
        3409754119631711876232308493673772547853916194372924898125039693313920) * 10 ^ 70 +
        3382721452037831919355435448299366178876780879750567545070174551930842) * 10 ^ 70 +
        0533959590994752307940284947891121868933249137112893497779932775980506) * 10 ^ 70 +
        3411272102117879728444419673756290441097749711346590967931959380449237) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (206 - x)) = _
  rw [show 207 = 1 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 12 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (207 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (207 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_207 :
    recurrence4Scalar2First.coeff 207 =
      -(((((7473200769485924971257 * 10 ^ 70 +
        9112942971196124214984095353589889496265841916940384519161112266083349) * 10 ^ 70 +
        8135429077399843810439665217744606601037390851169945372621696246877015) * 10 ^ 70 +
        2678203610981629460100391002814253167030584661489906514459017664634875) * 10 ^ 70 +
        7825096069133829463081147504844729997320701084829033904884727295497722) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (207 - x)) = _
  rw [show 208 = 1 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 12 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (208 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (208 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_208 :
    recurrence4Scalar2First.coeff 208 =
      (((((13614920077391491170262 * 10 ^ 70 +
        7926170818151656479564573445154108949985488479788244685009415817118067) * 10 ^ 70 +
        1711396761041619483857858419776955443731045721400427082779874893582104) * 10 ^ 70 +
        4199431651150430714531045706909427829535931471256654084771367230607441) * 10 ^ 70 +
        8381384110978199836684267516572680817663116205566561891483247167077303) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (208 - x)) = _
  rw [show 209 = 1 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 12 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (209 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (209 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_209 :
    recurrence4Scalar2First.coeff 209 =
      -(((((24459325956868675701067 * 10 ^ 70 +
        8707978723596833597132404403808509872231630351605821295470340552376991) * 10 ^ 70 +
        3512405702866753071176069386526645784562509048614857823717217755112033) * 10 ^ 70 +
        1273571692385627868876477946612903303643946406523796208397729110910468) * 10 ^ 70 +
        2450937152427759641558566695520356395728405018910863287933882732614440) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (209 - x)) = _
  rw [show 210 = 1 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 12 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (210 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (210 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_210 :
    recurrence4Scalar2First.coeff 210 =
      (((((43330715623304941128575 * 10 ^ 70 +
        8174122254909542825262708772626554582706042683564617604236727525963484) * 10 ^ 70 +
        8134068746948832225539257299268158273759344087488162703777964783551987) * 10 ^ 70 +
        5564860903344986520547954823931492478035528505177484751082526838099252) * 10 ^ 70 +
        6348840640779873392171661747316774527780779894497694624314459820664247) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (210 - x)) = _
  rw [show 211 = 1 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 12 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (211 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (211 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_211 :
    recurrence4Scalar2First.coeff 211 =
      -(((((75695395926241056621948 * 10 ^ 70 +
        4679899215521235573715962238582800704340218294755795081223293952049527) * 10 ^ 70 +
        1411534319657067862762664646640060950634141558003328221036714653217699) * 10 ^ 70 +
        0066359916697198503308450257842462715341313269034252669734434688614486) * 10 ^ 70 +
        3310333422722086159950577976318159612698222913484465583984797204484550) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (211 - x)) = _
  rw [show 212 = 1 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (212 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (212 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_212 :
    recurrence4Scalar2First.coeff 212 =
      (((((130396126466926827388243 * 10 ^ 70 +
        9033918841559550878415962284800095479272621071544632708244742989620557) * 10 ^ 70 +
        9783811100644915709790327749363020569583182507430035292069524746727002) * 10 ^ 70 +
        4061559202339075390250359534698402893759050751170605139685559257542738) * 10 ^ 70 +
        0966113351967678758135884586119181628838177327892583699509103092814719) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (212 - x)) = _
  rw [show 213 = 1 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 12 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (213 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (213 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_213 :
    recurrence4Scalar2First.coeff 213 =
      -(((((221503225772764221502861 * 10 ^ 70 +
        4672086535330222425780579537320533093942921668272815081861120304851049) * 10 ^ 70 +
        9235516925811839819736809854083483124937402802939446117777186342031017) * 10 ^ 70 +
        6473052591345935328836085498854910760436208871902111403872544109330251) * 10 ^ 70 +
        7793582146416987416733774718406899653971253847898313546286937773406944) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (213 - x)) = _
  rw [show 214 = 1 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 12 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (214 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (214 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_214 :
    recurrence4Scalar2First.coeff 214 =
      (((((371033527751041197518677 * 10 ^ 70 +
        5322596729602391977620289232941704585637035649241998523434743092147527) * 10 ^ 70 +
        7526414200195868821285190147408560760463765517006675950794377041268308) * 10 ^ 70 +
        7301179560178224868548770335222677189144738976980275840893944029576034) * 10 ^ 70 +
        0426731706917512996073141121742660214768939278226636275302934205523430) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (214 - x)) = _
  rw [show 215 = 1 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 12 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (215 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (215 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_215 :
    recurrence4Scalar2First.coeff 215 =
      -(((((612859073946950802176481 * 10 ^ 70 +
        4017405209681113248505824826173442890502434621952856014173066231733405) * 10 ^ 70 +
        3282070556980793734827084147135515075048592910710851376973754690616511) * 10 ^ 70 +
        9500613753535340544975985523999642238202275437354097942987691257434014) * 10 ^ 70 +
        0665977210641141831077897001677826992645008006066671294363915529342293) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (215 - x)) = _
  rw [show 216 = 1 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 12 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (216 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (216 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_216 :
    recurrence4Scalar2First.coeff 216 =
      (((((998201137153705229323591 * 10 ^ 70 +
        6367016644669083499933647766354656571423963089581645315865053289303566) * 10 ^ 70 +
        6224308716601301528707314082896239309559187798863941372445188030461894) * 10 ^ 70 +
        8474009816277827455239212670725806740729342368598095202094201445064435) * 10 ^ 70 +
        6782277976214501957729717363813002319061215731201529992092204378497627) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (216 - x)) = _
  rw [show 217 = 1 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 12 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (217 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (217 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_217 :
    recurrence4Scalar2First.coeff 217 =
      -(((((1603171585948136767583266 * 10 ^ 70 +
        9870158947676006095304655808151779270130305072652034942920599637991994) * 10 ^ 70 +
        9527742153403666848690831091146481309587800844679505312585998945616546) * 10 ^ 70 +
        2078736951407937061669014372205731611897555364027942971118802230631498) * 10 ^ 70 +
        7699755695344374002783249718050010777316645717611447503229116248484267) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (217 - x)) = _
  rw [show 218 = 1 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 12 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (218 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (218 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_218 :
    recurrence4Scalar2First.coeff 218 =
      (((((2538866411499086330260692 * 10 ^ 70 +
        6694778556095126737110273065382522472738828416742817512746659599816606) * 10 ^ 70 +
        8757002389505999325176545099362174413845927333245199152825986867549513) * 10 ^ 70 +
        4104387554121144153952237969957601211793851419440057075985618978736880) * 10 ^ 70 +
        3681831809183666509568932628399917503055134556012072217093285705227150) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (218 - x)) = _
  rw [show 219 = 1 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 12 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (219 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (219 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_219 :
    recurrence4Scalar2First.coeff 219 =
      -(((((3964512233143580857074480 * 10 ^ 70 +
        5689306122604809189653582538364754240481163213565079970494222601257835) * 10 ^ 70 +
        6982148174830836269110226461983446642636360295724653399121162902233618) * 10 ^ 70 +
        0013650568289338999291784982898381602106880280971860771854382441458101) * 10 ^ 70 +
        9563266133788526737864321396672264476748196496546520598951930210284800) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (219 - x)) = _
  rw [show 220 = 1 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 12 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (220 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (220 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_220 :
    recurrence4Scalar2First.coeff 220 =
      (((((6104085627669237854129247 * 10 ^ 70 +
        2429996712571950999301238569036991821369067925604701442642812784914646) * 10 ^ 70 +
        5302986894978785549720015668612649928781607647745859284919404597160270) * 10 ^ 70 +
        4285620390705116888699075505383018256905908390897985780465446435251377) * 10 ^ 70 +
        3486398509300654129883147737071726918217766540231984299401469675753022) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (220 - x)) = _
  rw [show 221 = 1 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 12 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (221 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (221 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_221 :
    recurrence4Scalar2First.coeff 221 =
      -(((((9266631563220101755744247 * 10 ^ 70 +
        3390932299398648263878200613877670546572172165262444190833603621860490) * 10 ^ 70 +
        2911666505344401393044291469934627160510265129749472795531842536016266) * 10 ^ 70 +
        2504240393620584272770549685043661775961843444793441502195848245160156) * 10 ^ 70 +
        4863930629307816507156689059281342422405841756884014147904427971226558) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (221 - x)) = _
  rw [show 222 = 1 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 12 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (222 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (222 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_222 :
    recurrence4Scalar2First.coeff 222 =
      (((((13870163546674461713521455 * 10 ^ 70 +
        1639151535790779271802110704419698528445558826952052275853956441943642) * 10 ^ 70 +
        0309653722925783480386785676503252838173322751697268177720297959099019) * 10 ^ 70 +
        1057658916143710246719612470044199350191191787459475392624789014652827) * 10 ^ 70 +
        5526921089756000719889770377193701570171495688218026323140425272487242) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (222 - x)) = _
  rw [show 223 = 1 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 12 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (223 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (223 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_223 :
    recurrence4Scalar2First.coeff 223 =
      -(((((20468501142502867527110461 * 10 ^ 70 +
        3814984279308184411288014955187465350116572044767631306244556308749138) * 10 ^ 70 +
        0186165951897968798447672823696173237533066601370178836532723892774952) * 10 ^ 70 +
        1544119750448488559372497831737684588604106058324867209396625930557996) * 10 ^ 70 +
        8499238239141576819397283133866445711911899407092094528076466909098735) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (223 - x)) = _
  rw [show 224 = 1 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 12 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (224 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (224 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_224 :
    recurrence4Scalar2First.coeff 224 =
      (((((29779670545848756549524873 * 10 ^ 70 +
        9486535928457399151725290212775034765462419143820543724222144791963051) * 10 ^ 70 +
        4170898506202786533018580513862731413649669269367376241870295125228831) * 10 ^ 70 +
        1489115152082784709983547529763785766571781742549681073050235161302075) * 10 ^ 70 +
        1029783705751015677914777242033256333193289452041714641409290220801050) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (224 - x)) = _
  rw [show 225 = 1 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 12 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (225 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (225 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_225 :
    recurrence4Scalar2First.coeff 225 =
      -(((((42713566116555600745441056 * 10 ^ 70 +
        1046522700109605050784673291534885199144021204113206389808786659921210) * 10 ^ 70 +
        5640007263592535623274143804653257058466763855007617468658189688708742) * 10 ^ 70 +
        6885688744386906446875987123457454785773003181530734453521861799042741) * 10 ^ 70 +
        6467805654117793798577947442346322698222872879947255760220025236567085) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (225 - x)) = _
  rw [show 226 = 1 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 12 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (226 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (226 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_226 :
    recurrence4Scalar2First.coeff 226 =
      (((((60395488201633375156740613 * 10 ^ 70 +
        3735595892424475782493236241017265447211859258675294433756779704129879) * 10 ^ 70 +
        3680268390022895102079025259422305952059935005183282539117697119352543) * 10 ^ 70 +
        1769878827907047829768001978671989100092631340233744869141685680430427) * 10 ^ 70 +
        4215694173777142610635380789397233316144529750511434634622024222897517) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (226 - x)) = _
  rw [show 227 = 1 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 12 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (227 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (227 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_227 :
    recurrence4Scalar2First.coeff 227 =
      -(((((84181027840910637881844599 * 10 ^ 70 +
        1292775877765901764679433570745485508430717599890776973473820086482019) * 10 ^ 70 +
        0842122537701048485077871075333396139479920465006703730824498397510515) * 10 ^ 70 +
        1692802234765999634183810139010032935909855289643645795913922013819727) * 10 ^ 70 +
        6385595733882945278461198911891679995148708525969492900526052405952176) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (227 - x)) = _
  rw [show 228 = 1 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 12 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (228 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (228 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_228 :
    recurrence4Scalar2First.coeff 228 =
      (((((115656712166275357445617125 * 10 ^ 70 +
        9279293702105091934189425617051165719756692560276845103921320896324876) * 10 ^ 70 +
        8674868344330368978416645763617355075705823076578605293431740024963506) * 10 ^ 70 +
        6611898140365364250895713977346796466488104793893510195542642982973378) * 10 ^ 70 +
        7180055105924045521843757598045594788085315702888303912977581153271968) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (228 - x)) = _
  rw [show 229 = 1 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 12 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (229 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (229 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_229 :
    recurrence4Scalar2First.coeff 229 =
      -(((((156620062915992876864164357 * 10 ^ 70 +
        5321527077818792035419211472803600337106511835498971566979021759002202) * 10 ^ 70 +
        4650548587008875730323975620815924879592018118747403194146266725877976) * 10 ^ 70 +
        9371682164144374349654875988062685912842372738346027947118097989222520) * 10 ^ 70 +
        4336625168926428732226541785198550218503852718865305252962777540881986) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (229 - x)) = _
  rw [show 230 = 1 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (230 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (230 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_230 :
    recurrence4Scalar2First.coeff 230 =
      (((((209032507385703260322899197 * 10 ^ 70 +
        5916513711022549577124911040072186420261449789395386440959441936004657) * 10 ^ 70 +
        0838403014519629064505536947793843744480865758266640502522432536791058) * 10 ^ 70 +
        4296623705257329838895477621667644646743899027403427892044174181581387) * 10 ^ 70 +
        2222223605468285977744022951368062695838207013677482071603537361168784) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (230 - x)) = _
  rw [show 231 = 1 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 12 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (231 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (231 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_231 :
    recurrence4Scalar2First.coeff 231 =
      -(((((274939187987268097577134605 * 10 ^ 70 +
        9061339435967021827220790679095649267890297447073554826005610425807726) * 10 ^ 70 +
        3932932053934581244281892419622031641850173178700489508114775641020034) * 10 ^ 70 +
        4245632599680862341141996702604989600879951054392603865304437487193797) * 10 ^ 70 +
        6629755427427240379078162812537242863653210171823092816503513312138042) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (231 - x)) = _
  rw [show 232 = 1 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 12 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (232 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (232 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_232 :
    recurrence4Scalar2First.coeff 232 =
      (((((356351391428846571829383708 * 10 ^ 70 +
        0085247423630771696833899162458628839871168427675876620635224224226539) * 10 ^ 70 +
        1561967019486428274141328685992701069950953176155405690705348149760432) * 10 ^ 70 +
        7296533166116420102612496459114078393108121734050246798812961949923220) * 10 ^ 70 +
        5306107546022854578748523474934766451464328062073482511548839391207663) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (232 - x)) = _
  rw [show 233 = 1 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 12 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (233 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (233 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_233 :
    recurrence4Scalar2First.coeff 233 =
      -(((((455090230018128916212706796 * 10 ^ 70 +
        0314141608666961469059860691149883176546452698873373257761902807295970) * 10 ^ 70 +
        7723752128589139813165736419718253568226276913087270142996196637103167) * 10 ^ 70 +
        5241280874817025428507595812284099242899192835430316541694889973469064) * 10 ^ 70 +
        9168139025941792450243129440868527721952417202032401078771566393524995) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (233 - x)) = _
  rw [show 234 = 1 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 12 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (234 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (234 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_234 :
    recurrence4Scalar2First.coeff 234 =
      (((((572594382231456766588969514 * 10 ^ 70 +
        0153753253937416025121508919709331280352736449852724614339935537645982) * 10 ^ 70 +
        5846909286734347429684561628061130274713286773341459625961693040363618) * 10 ^ 70 +
        3498082931675780704991821435456457072761061314821776682471962469092227) * 10 ^ 70 +
        5851327525824927911358804416629806453746541574159644410947681423807514) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (234 - x)) = _
  rw [show 235 = 1 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 12 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (235 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (235 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_235 :
    recurrence4Scalar2First.coeff 235 =
      -(((((709699962731139355198373666 * 10 ^ 70 +
        3125479108718790874114030031047846870252873966567107136749143843150482) * 10 ^ 70 +
        4522281264799554815110567238616591364308744010617496855862416901229606) * 10 ^ 70 +
        8918726703654774469275759468376460926515505577437349397164135070429436) * 10 ^ 70 +
        8393179719531458334590496912406775610124298029897133783299491081209777) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (235 - x)) = _
  rw [show 236 = 1 +
    235 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 12 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (236 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (236 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_236 :
    recurrence4Scalar2First.coeff 236 =
      (((((866406525944924555177135901 * 10 ^ 70 +
        0412639311150970936021038688798939601847369786457296156649369616939379) * 10 ^ 70 +
        6002431172609203683838262832547185222585862600940829587672783454932633) * 10 ^ 70 +
        4282027949688132492789259180287085741927433503649544956977608519174159) * 10 ^ 70 +
        8124335865867481971379243482321942459176868909261296141741204424255720) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (236 - x)) = _
  rw [show 237 = 1 +
    236 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 12 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (237 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (237 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_237 :
    recurrence4Scalar2First.coeff 237 =
      -(((((1041649143216617533601874208 * 10 ^ 70 +
        7702958943315884287647323199190574121420343005926607217551991906654606) * 10 ^ 70 +
        4753889387699237932822395356894064638916161359587641618796736897046587) * 10 ^ 70 +
        2168176497689440870349083583570931323067287334197690414681588026422119) * 10 ^ 70 +
        2516851428031015191179549494000261042837981263280770096099805048105504) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (237 - x)) = _
  rw [show 238 = 1 +
    237 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 12 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (238 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (238 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_238 :
    recurrence4Scalar2First.coeff 238 =
      (((((1233101548437668503738407164 * 10 ^ 70 +
        0856595564905061631232750733481286768256665407617723266291194918838372) * 10 ^ 70 +
        1121227197340350716737908677431862654523488438420316089009492211007661) * 10 ^ 70 +
        0728133156963652650173430135335523483149970777428384862680308766650497) * 10 ^ 70 +
        6459561584405393416707513185303832331622270331986051218033460846932570) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (238 - x)) = _
  rw [show 239 = 1 +
    238 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 12 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (239 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (239 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_239 :
    recurrence4Scalar2First.coeff 239 =
      -(((((1437038514858019344040235686 * 10 ^ 70 +
        2443545431832096053222024954832593826592657188819315423534063139715782) * 10 ^ 70 +
        2387127192999081692620430469904886828666049066921112988355646868160385) * 10 ^ 70 +
        0164195937017975109896157198041696262637827054105116247129794518846280) * 10 ^ 70 +
        6079356825465060833454105378935727591533697011034444297387716709945275) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (239 - x)) = _
  rw [show 240 = 1 +
    239 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 12 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (240 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (240 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_240 :
    recurrence4Scalar2First.coeff 240 =
      (((((1648285919412869266047619925 * 10 ^ 70 +
        8713805443643998466536052095015221999252773934643131937816753523651535) * 10 ^ 70 +
        9741606837053493237035167431010627931164822452679014879002036548884933) * 10 ^ 70 +
        8802280797620478109263413309733166338990688107774640232481158201893410) * 10 ^ 70 +
        9318589225896097163301683485302316226540619797204593562297773769528153) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (240 - x)) = _
  rw [show 241 = 1 +
    240 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 12 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (241 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (241 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_241 :
    recurrence4Scalar2First.coeff 241 =
      -(((((1860283581930751958362105194 * 10 ^ 70 +
        1501750838419572023727319581560023899866562103907698676163086314901273) * 10 ^ 70 +
        9340823512159671842726402647813430474776257299585712780583994340655464) * 10 ^ 70 +
        8863040808419628518586626647158251282717537186366847295002915654005564) * 10 ^ 70 +
        5819890424551424673592897260972314605479459535600179130535805265440776) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (241 - x)) = _
  rw [show 242 = 1 +
    241 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 12 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (242 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (242 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_242 :
    recurrence4Scalar2First.coeff 242 =
      (((((2065278535487233381859692151 * 10 ^ 70 +
        5017057060762204499562477059454482430148587967483623822045544254620835) * 10 ^ 70 +
        0971689083141721030381805039562302450061876899532193930579599468081752) * 10 ^ 70 +
        6944288861157130265106167190444256946576074839334759937122294335289808) * 10 ^ 70 +
        8629653884386916434986260574806826462319669918206786629260762388375193) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (242 - x)) = _
  rw [show 243 = 1 +
    242 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 12 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (243 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (243 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_243 :
    recurrence4Scalar2First.coeff 243 =
      -(((((2254655045615650545996717367 * 10 ^ 70 +
        5767094324580463008548474553439456171010702724188247515605433799449411) * 10 ^ 70 +
        4840097494437139345429756051802270117650895882478365720399697084641244) * 10 ^ 70 +
        5757190698876543973195589151899776187255230090544006876109180867906778) * 10 ^ 70 +
        9993431461085122928184461197706367203862845118183595580139614406083991) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (243 - x)) = _
  rw [show 244 = 1 +
    243 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (244 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (244 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_244 :
    recurrence4Scalar2First.coeff 244 =
      (((((2419393259382966163679188345 * 10 ^ 70 +
        3532044659263427359434533706998934004071859363393027238846242904769604) * 10 ^ 70 +
        0278706173860328651786494680505487316553604560257272335180162106344637) * 10 ^ 70 +
        1538716237027858293091301935748217978931003883240578876245355911899967) * 10 ^ 70 +
        5968978931808557721284596328250244943102714278768412336149874549960557) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (244 - x)) = _
  rw [show 245 = 1 +
    244 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 12 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (245 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (245 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_245 :
    recurrence4Scalar2First.coeff 245 =
      -(((((2550632294730470008007678171 * 10 ^ 70 +
        2728500684706056088049090816739060856124848267667403872408079075680108) * 10 ^ 70 +
        6126771487072964214226304224388031108150926048685738364199173075186361) * 10 ^ 70 +
        1973516142456010248201467567299744574356462407357092018831170890966537) * 10 ^ 70 +
        9391099394408064214277270525282210012499798768400885292022624282779870) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (245 - x)) = _
  rw [show 246 = 1 +
    245 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 12 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (246 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (246 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_246 :
    recurrence4Scalar2First.coeff 246 =
      (((((2640297873689708097729878250 * 10 ^ 70 +
        2802901634950504742474564321658498876239799102674611144302119948406176) * 10 ^ 70 +
        4273998695475590961249909033116573646534889472638838048747141438710297) * 10 ^ 70 +
        0644032437126068223785554018488194348564037565573549231813128152940896) * 10 ^ 70 +
        3412225997576160179636436661462794192746442809031749114615685134124464) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (246 - x)) = _
  rw [show 247 = 1 +
    246 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 12 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (247 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (247 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_247 :
    recurrence4Scalar2First.coeff 247 =
      -(((((2681741547870752980950100706 * 10 ^ 70 +
        9265158976811070124928729764553514243352657005159872565077381779096428) * 10 ^ 70 +
        9187020581600595217352631738539873953291321832044264019372660185069667) * 10 ^ 70 +
        1167113908864913801811476215999402174316457898509112317843680500541127) * 10 ^ 70 +
        3100757351882069350891506018259773223985665840383612089948425905839320) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (247 - x)) = _
  rw [show 248 = 1 +
    247 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (248 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (248 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_248 :
    recurrence4Scalar2First.coeff 248 =
      (((((2670330399030223936246806548 * 10 ^ 70 +
        5206830888257802689744677207977916387766754915922916379245445573923012) * 10 ^ 70 +
        3652841184800831963242122932264554551350313172996613169885699241316647) * 10 ^ 70 +
        6114908964549017402971133832026769901983657189830004729982515221762519) * 10 ^ 70 +
        4837629758531480092399603147363753917343387313191582187060344603651731) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (248 - x)) = _
  rw [show 249 = 1 +
    248 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 12 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (249 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (249 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_249 :
    recurrence4Scalar2First.coeff 249 =
      -(((((2603924624465504293563147265 * 10 ^ 70 +
        9829421029659085340931753409733351444592887749786916963063713908407196) * 10 ^ 70 +
        9912960673575216087217004003337812241647032386427579341528272767697533) * 10 ^ 70 +
        8045624586772618898696327654746772005497544390175363212255992839325281) * 10 ^ 70 +
        3022871026695349534587627003438372040604073019314033823363271587875906) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (249 - x)) = _
  rw [show 250 = 1 +
    249 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 12 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (250 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (250 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_250 :
    recurrence4Scalar2First.coeff 250 =
      (((((2483186641565147251715274383 * 10 ^ 70 +
        9904652045556734189150878180599517190429163029614959459219162518506732) * 10 ^ 70 +
        2187222333976480949183726816109739911813132472688029023670898391607515) * 10 ^ 70 +
        0180784745912936916869859999740409278030332378103039760082716400160369) * 10 ^ 70 +
        2670425594672462901875340292861405710033506987828824160459376709889807) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (250 - x)) = _
  rw [show 251 = 1 +
    250 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 12 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (251 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (251 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_251 :
    recurrence4Scalar2First.coeff 251 =
      -(((((2311679209431065293336093060 * 10 ^ 70 +
        3250186585865798096520242617543834145677146877113665335171051733500839) * 10 ^ 70 +
        7811935272843574702842944288673455145428474215243158742598253724529426) * 10 ^ 70 +
        7428545781597662959497485267561424554011643110625651359250428826086804) * 10 ^ 70 +
        6813749522905959921678187969158523021695624511697877170201564151021769) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (251 - x)) = _
  rw [show 252 = 1 +
    251 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 12 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (252 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (252 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_252 :
    recurrence4Scalar2First.coeff 252 =
      (((((2095730340095507393796124505 * 10 ^ 70 +
        4743195381469383184825652124673983105949236828538796866302731498209747) * 10 ^ 70 +
        6051942398160894904742857688731082434163111080074189995013935185713048) * 10 ^ 70 +
        3866594944279616430554948060038730538767621542554076782500255723608517) * 10 ^ 70 +
        1656576895273498330702273439294691787963634970492833824459736200825529) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (252 - x)) = _
  rw [show 253 = 1 +
    252 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 12 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (253 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (253 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_253 :
    recurrence4Scalar2First.coeff 253 =
      -(((((1844067153169890630149986244 * 10 ^ 70 +
        3882389629325284405237432254342048040953471082710431432019237376324286) * 10 ^ 70 +
        4264661755048081387075882463297573653630694232989756671639905075820221) * 10 ^ 70 +
        2038388352176552651213224066915122318027494521141431607230865896052752) * 10 ^ 70 +
        3286445789471343574874122864923488197566455974071799123252503798257252) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (253 - x)) = _
  rw [show 254 = 1 +
    253 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 12 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (254 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (254 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_254 :
    recurrence4Scalar2First.coeff 254 =
      (((((1567246228133543003919100022 * 10 ^ 70 +
        2149691799500093545038359447090036928911593850557929887771274718051956) * 10 ^ 70 +
        5149723275903267106903829600722775326722236836743822973692583306719276) * 10 ^ 70 +
        2965658119846440000484045756161682361285468769803764659686019111823114) * 10 ^ 70 +
        1649912637625772309365832878085736664967403291484195679428629677097640) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (254 - x)) = _
  rw [show 255 = 1 +
    254 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 12 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (255 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (255 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_255 :
    recurrence4Scalar2First.coeff 255 =
      -(((((1276931010589789651842055236 * 10 ^ 70 +
        0479171070472380623539051295802912923653620999827970185435970744468860) * 10 ^ 70 +
        1702210696080037554196436192916095504510812394609304397055039731063850) * 10 ^ 70 +
        5713897234770260176339959242222689554989175607945148544983088633991979) * 10 ^ 70 +
        4536962601718283450383902603489720244883240018033538014804416544386703) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (255 - x)) = _
  rw [show 256 = 1 +
    255 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 12 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (256 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (256 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_256 :
    recurrence4Scalar2First.coeff 256 =
      (((((985084225056024638520809231 * 10 ^ 70 +
        2271313158450585411568152651007592594944982717989905132584355080427544) * 10 ^ 70 +
        6477261432977793328539984053469419129097685147299545719305552838676167) * 10 ^ 70 +
        7825299447719078677447434543133072960609397495481232684495877824867338) * 10 ^ 70 +
        3282043018438369482713134628192571149950258800293818384722244647745606) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (256 - x)) = _
  rw [show 257 = 1 +
    256 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 12 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (257 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (257 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_257 :
    recurrence4Scalar2First.coeff 257 =
      -(((((703152567178671372170052520 * 10 ^ 70 +
        4855970971986099519014209350868145685740120599581528974751650894619152) * 10 ^ 70 +
        0472576597729582865008267687525211583519245720313067140831879906644425) * 10 ^ 70 +
        4292893682985752864659989063115946317874406131964197821898911720070469) * 10 ^ 70 +
        0526839742840883426587459996391837294027101537658338431323223058851349) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (257 - x)) = _
  rw [show 258 = 1 +
    257 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 12 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (258 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (258 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_258 :
    recurrence4Scalar2First.coeff 258 =
      (((((441320877090571090823466739 * 10 ^ 70 +
        7283248875338307746020096168600395147635385316139474933660417960696260) * 10 ^ 70 +
        9158777421000283158243644236984040645812184484388346629085066413619296) * 10 ^ 70 +
        5174343603625133461036290231777443530364924299062345685170638257722803) * 10 ^ 70 +
        8223977702804683131258590324109893614250642067811064436670706921498781) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (258 - x)) = _
  rw [show 259 = 1 +
    258 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 12 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (259 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (259 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_259 :
    recurrence4Scalar2First.coeff 259 =
      -(((((207903596584931773244845848 * 10 ^ 70 +
        0034263824408122562781847949342104827256964898316977197263447986354345) * 10 ^ 70 +
        8460767313914204763785447000777222587301515279329909470248829229017510) * 10 ^ 70 +
        4631116890410086162790160054234910781972294036387067410143329059695266) * 10 ^ 70 +
        2370921002355630898000401719694673902851201750377325555955543007381513) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (259 - x)) = _
  rw [show 260 = 1 +
    259 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 12 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (260 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (260 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_260 :
    recurrence4Scalar2First.coeff 260 =
      (((((8924016666771971420191081 * 10 ^ 70 +
        7137954762097077093677822276618799824980942557727533883656241706614709) * 10 ^ 70 +
        5852148346008852495337475157423361121394112222594116820650314021035939) * 10 ^ 70 +
        1712263178979595328746458451558037209731840697522714880200386476825157) * 10 ^ 70 +
        7363979060110780695997086994945476164115953777187908580410599440937423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (260 - x)) = _
  rw [show 261 = 1 +
    260 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 12 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (261 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (261 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_261 :
    recurrence4Scalar2First.coeff 261 =
      (((((152090820268225549849004529 * 10 ^ 70 +
        6726532402529188667788982445573339314880143701972103340955281069739625) * 10 ^ 70 +
        2815308410436165158687651151286941849103487485895518948829278544453024) * 10 ^ 70 +
        1299060813816299547152612396720683606732719522895485446658840800936954) * 10 ^ 70 +
        7037640242448620049689230301104024976499558055381315569502205594478569) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (261 - x)) = _
  rw [show 262 = 1 +
    261 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 12 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (262 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (262 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_262 :
    recurrence4Scalar2First.coeff 262 =
      -(((((274096451083074214639733928 * 10 ^ 70 +
        4166825390383653713105714577495273120639472471612484215843625966474442) * 10 ^ 70 +
        3303072789863600752188528004197811712433503139935052371269767843232452) * 10 ^ 70 +
        2980015833828475919906477090853769351742781122585058611044553975859187) * 10 ^ 70 +
        5886440040245304797481770750573440766342966148546712642984116703879410) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (262 - x)) = _
  rw [show 263 = 1 +
    262 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 12 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (263 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (263 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_263 :
    recurrence4Scalar2First.coeff 263 =
      (((((358318918455762389255792023 * 10 ^ 70 +
        5290490223238527911852845246343538449535018641684111184146961816038855) * 10 ^ 70 +
        1006825993840960108921351396674246098924833448787479754495140306731864) * 10 ^ 70 +
        0548048042312035182144628015092753388028041624690373824641285336194955) * 10 ^ 70 +
        5707492464751418814646915243939416634076317962285876562809486041183855) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (263 - x)) = _
  rw [show 264 = 1 +
    263 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 12 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (264 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (264 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_264 :
    recurrence4Scalar2First.coeff 264 =
      -(((((407883860536276594621680266 * 10 ^ 70 +
        4348481691464602895704891711274500892931187729976816091925255577812164) * 10 ^ 70 +
        0084900497858759073238493533511106139962988484423120716944525378508966) * 10 ^ 70 +
        1371425567072772799430270012311424342899737021315155922324156925771910) * 10 ^ 70 +
        4237935112365267709798658825138389165905595614892782272300879123842351) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (264 - x)) = _
  rw [show 265 = 1 +
    264 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 12 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (265 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (265 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_265 :
    recurrence4Scalar2First.coeff 265 =
      (((((427339100539127896299195705 * 10 ^ 70 +
        9575294044806053290530341030997302685131202968398737358010922046007120) * 10 ^ 70 +
        1488727090173753812633764470255134108165735259202863763703654669964467) * 10 ^ 70 +
        5510753139631858173321302292192288583348214551676118297709683654414559) * 10 ^ 70 +
        9325149516290828235838794173285047167072064069536130271668323118274627) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (265 - x)) = _
  rw [show 266 = 1 +
    265 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 12 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (266 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (266 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_266 :
    recurrence4Scalar2First.coeff 266 =
      -(((((422128349864709602868525470 * 10 ^ 70 +
        5515488201775807504171423476240498481215128020056176420065451620874315) * 10 ^ 70 +
        5303896544954828949100039542145003387208325443233255256984014256962200) * 10 ^ 70 +
        6066453712303901507296435178316791711755953035429522981038929856437800) * 10 ^ 70 +
        7052244052917899147869466054329538297852382644498546607944935463040447) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (266 - x)) = _
  rw [show 267 = 1 +
    266 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 12 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (267 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (267 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_267 :
    recurrence4Scalar2First.coeff 267 =
      (((((398071533721996033718153759 * 10 ^ 70 +
        0270625684209545003269848419954806190597805827309445653992366427481373) * 10 ^ 70 +
        5329934155198310308533033783618293874253763316291824584814305860541332) * 10 ^ 70 +
        7637435452327428058478765930678782172661316258759164307980592731657439) * 10 ^ 70 +
        0079975076915958621238880224398534578024890368330994871213315716805077) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (267 - x)) = _
  rw [show 268 = 1 +
    267 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 12 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (268 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (268 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_268 :
    recurrence4Scalar2First.coeff 268 =
      -(((((360898908157625218893483134 * 10 ^ 70 +
        9696248284724285988968666813806181572197534111447199780019008878920878) * 10 ^ 70 +
        6568780022390875125036842544845597619601074559130967917562685349938626) * 10 ^ 70 +
        7977357455469704397013772136967028914603995189355291203015424633809253) * 10 ^ 70 +
        8744329407949443582950939141377535611595997837618206759814299939424880) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (268 - x)) = _
  rw [show 269 = 1 +
    268 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 12 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (269 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (269 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_269 :
    recurrence4Scalar2First.coeff 269 =
      (((((315873449525649452155514331 * 10 ^ 70 +
        1514558668117401006669506474645456407857468898069741588034665307668500) * 10 ^ 70 +
        0031009771355904396400487947865333985546226459997486440508286393666494) * 10 ^ 70 +
        5322028019480101193321205756509621207268278912766736333989663014594030) * 10 ^ 70 +
        0148948306266678827967263014530837032888948078260579818822163631187025) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (269 - x)) = _
  rw [show 270 = 1 +
    269 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 12 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (270 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (270 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_270 :
    recurrence4Scalar2First.coeff 270 =
      -(((((267521210120792349324739268 * 10 ^ 70 +
        2451499573355673207751544452837510108464690253876295105960260247977669) * 10 ^ 70 +
        4964555846791288703500417815475535729026911898537225570201976833569956) * 10 ^ 70 +
        2566629217999244376327367071103328445461769547448897619694374644638386) * 10 ^ 70 +
        5563276550321518473935289381856852529410308027292669954842319663485509) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (270 - x)) = _
  rw [show 271 = 1 +
    270 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 12 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (271 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (271 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_271 :
    recurrence4Scalar2First.coeff 271 =
      (((((219474664592162343969963845 * 10 ^ 70 +
        8163541154821863823655001490527271338223130515997227750161036260241011) * 10 ^ 70 +
        3528478573007941710673215337467670450782597636575228205337540237958100) * 10 ^ 70 +
        9283300663276587912303334959493383016929248084213747764386670368256756) * 10 ^ 70 +
        4664860429992197303560706985303811121466159173754572548883900251015434) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (271 - x)) = _
  rw [show 272 = 1 +
    271 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 12 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (272 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (272 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_272 :
    recurrence4Scalar2First.coeff 272 =
      -(((((174421376020690542791212217 * 10 ^ 70 +
        2186485599690701989380790538939755555270311548836881922125141354809017) * 10 ^ 70 +
        7583542656882667492471968222708975866931935636952881184431463501370814) * 10 ^ 70 +
        6539153874046500630462764587993462797330372714448459063117155008989265) * 10 ^ 70 +
        9941217355454440085516412306237284658365780954772150249253138669606833) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (272 - x)) = _
  rw [show 273 = 1 +
    272 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 12 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (273 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (273 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_273 :
    recurrence4Scalar2First.coeff 273 =
      (((((134140858240025304817836588 * 10 ^ 70 +
        3504939025743809285005745259365150683606487612341040528593363593249876) * 10 ^ 70 +
        2978751330365749367620708774755821221700999185784310182331363067254267) * 10 ^ 70 +
        1268087727669151100983006600252711133914548202279485978415234173415256) * 10 ^ 70 +
        1664891880084667830211846028305697481277514346870741371998693999936219) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (273 - x)) = _
  rw [show 274 = 1 +
    273 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 12 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (274 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (274 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_274 :
    recurrence4Scalar2First.coeff 274 =
      -(((((99606895467935773612379328 * 10 ^ 70 +
        3564835048529717650266468633694884179217672284229908872399522657045800) * 10 ^ 70 +
        7207139847157655906462649541033674180673377173721450930099284318561682) * 10 ^ 70 +
        9669099742560586324506903188518024689960184283682617609364303477447109) * 10 ^ 70 +
        4235916538258175657196289707206389139301204628030223747589684525752574) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (274 - x)) = _
  rw [show 275 = 1 +
    274 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 12 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (275 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (275 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_275 :
    recurrence4Scalar2First.coeff 275 =
      (((((71130751899777849175712749 * 10 ^ 70 +
        5908150399524763153230841258029962421148261967122996660915012272614746) * 10 ^ 70 +
        6070867259794324552002262313490933318914141579749326699680230940512821) * 10 ^ 70 +
        1879780190020929182825363819352051559852004597408301189266688439423754) * 10 ^ 70 +
        3457449704130554139880668464580099009831970813242787907068629638904909) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (275 - x)) = _
  rw [show 276 = 1 +
    275 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
