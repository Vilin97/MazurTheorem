/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart1Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
