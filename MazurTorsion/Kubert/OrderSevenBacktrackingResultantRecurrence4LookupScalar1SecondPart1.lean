/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

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
  recurrence4QuotientConstant_coeff_0
  recurrence4QuotientConstant_coeff_1
  recurrence4QuotientConstant_coeff_10
  recurrence4QuotientConstant_coeff_100
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_11
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115

attribute [local simp]
  recurrence4QuotientConstant_coeff_116
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_12
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
  recurrence4QuotientConstant_coeff_13
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
  recurrence4QuotientConstant_coeff_14
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
  recurrence4QuotientConstant_coeff_15
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
  recurrence4QuotientConstant_coeff_16
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
  recurrence4QuotientConstant_coeff_17
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173

attribute [local simp]
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_18
  recurrence4QuotientConstant_coeff_180
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_19
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
  recurrence4QuotientConstant_coeff_2
  recurrence4QuotientConstant_coeff_20
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
  recurrence4QuotientConstant_coeff_21
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
  recurrence4QuotientConstant_coeff_22
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
  recurrence4QuotientConstant_coeff_23
  recurrence4QuotientConstant_coeff_230

attribute [local simp]
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_24
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
  recurrence4QuotientConstant_coeff_25
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
  recurrence4QuotientConstant_coeff_26
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
  recurrence4QuotientConstant_coeff_27
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_28
  recurrence4QuotientConstant_coeff_29
  recurrence4QuotientConstant_coeff_3
  recurrence4QuotientConstant_coeff_30
  recurrence4QuotientConstant_coeff_31
  recurrence4QuotientConstant_coeff_32
  recurrence4QuotientConstant_coeff_33
  recurrence4QuotientConstant_coeff_34
  recurrence4QuotientConstant_coeff_35
  recurrence4QuotientConstant_coeff_36
  recurrence4QuotientConstant_coeff_37
  recurrence4QuotientConstant_coeff_38
  recurrence4QuotientConstant_coeff_39
  recurrence4QuotientConstant_coeff_4
  recurrence4QuotientConstant_coeff_40
  recurrence4QuotientConstant_coeff_41

attribute [local simp]
  recurrence4QuotientConstant_coeff_42
  recurrence4QuotientConstant_coeff_43
  recurrence4QuotientConstant_coeff_44
  recurrence4QuotientConstant_coeff_45
  recurrence4QuotientConstant_coeff_46
  recurrence4QuotientConstant_coeff_47
  recurrence4QuotientConstant_coeff_48
  recurrence4QuotientConstant_coeff_49
  recurrence4QuotientConstant_coeff_5
  recurrence4QuotientConstant_coeff_50
  recurrence4QuotientConstant_coeff_51
  recurrence4QuotientConstant_coeff_52
  recurrence4QuotientConstant_coeff_53
  recurrence4QuotientConstant_coeff_54
  recurrence4QuotientConstant_coeff_55
  recurrence4QuotientConstant_coeff_56
  recurrence4QuotientConstant_coeff_57
  recurrence4QuotientConstant_coeff_58
  recurrence4QuotientConstant_coeff_59
  recurrence4QuotientConstant_coeff_6
  recurrence4QuotientConstant_coeff_60
  recurrence4QuotientConstant_coeff_61
  recurrence4QuotientConstant_coeff_62
  recurrence4QuotientConstant_coeff_63
  recurrence4QuotientConstant_coeff_64
  recurrence4QuotientConstant_coeff_65
  recurrence4QuotientConstant_coeff_66
  recurrence4QuotientConstant_coeff_67
  recurrence4QuotientConstant_coeff_68
  recurrence4QuotientConstant_coeff_69
  recurrence4QuotientConstant_coeff_7
  recurrence4QuotientConstant_coeff_70
  recurrence4QuotientConstant_coeff_71
  recurrence4QuotientConstant_coeff_72
  recurrence4QuotientConstant_coeff_73
  recurrence4QuotientConstant_coeff_74
  recurrence4QuotientConstant_coeff_75
  recurrence4QuotientConstant_coeff_76
  recurrence4QuotientConstant_coeff_77
  recurrence4QuotientConstant_coeff_78
  recurrence4QuotientConstant_coeff_79
  recurrence4QuotientConstant_coeff_8
  recurrence4QuotientConstant_coeff_80
  recurrence4QuotientConstant_coeff_81
  recurrence4QuotientConstant_coeff_82
  recurrence4QuotientConstant_coeff_83
  recurrence4QuotientConstant_coeff_84
  recurrence4QuotientConstant_coeff_85
  recurrence4QuotientConstant_coeff_86
  recurrence4QuotientConstant_coeff_87
  recurrence4QuotientConstant_coeff_88
  recurrence4QuotientConstant_coeff_89
  recurrence4QuotientConstant_coeff_9
  recurrence4QuotientConstant_coeff_90
  recurrence4QuotientConstant_coeff_91
  recurrence4QuotientConstant_coeff_92
  recurrence4QuotientConstant_coeff_93
  recurrence4QuotientConstant_coeff_94
  recurrence4QuotientConstant_coeff_95
  recurrence4QuotientConstant_coeff_96
  recurrence4QuotientConstant_coeff_97
  recurrence4QuotientConstant_coeff_98
  recurrence4QuotientConstant_coeff_99

private theorem recurrence4Scalar1Second_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (171 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_171 :
    recurrence4Scalar1Second.coeff 171 =
      -(((((379331340 * 10 ^ 70 +
        2025519456421791050442361403180932549200610431124297876494272567796854) * 10 ^ 70 +
        1669010838322683408253580561409906206451679956344938848570204021562357) * 10 ^ 70 +
        4351742156269382736513391341109883248150482859686816421867923281186682) * 10 ^ 70 +
        9663955970881482448801929099123676128677776974511684137450006817079245) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (171 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (172 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_172 :
    recurrence4Scalar1Second.coeff 172 =
      (((((1174667779 * 10 ^ 70 +
        6045500313201050980514617689719967240497350605171971795863702906474501) * 10 ^ 70 +
        3193590787583793335287131221179874839872063879249355212192740300188770) * 10 ^ 70 +
        6381144274580847876344235790035592606824412842484236312834303302162137) * 10 ^ 70 +
        0675708267941046533893403023441627402892402678359927371566207314276430) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (172 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (173 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (173 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_173 :
    recurrence4Scalar1Second.coeff 173 =
      -(((((3582752430 * 10 ^ 70 +
        9260400994081662052051910489366107099144139061542410419427294253911987) * 10 ^ 70 +
        4886572409242860749992232105846592130183287278444208277823823027692775) * 10 ^ 70 +
        9943538069731813594401841438478653016305337088490399499352261397471431) * 10 ^ 70 +
        8308667859504557448901013841272009432158265608154085173226315777494551) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (173 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (174 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (174 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_174 :
    recurrence4Scalar1Second.coeff 174 =
      (((((10763347471 * 10 ^ 70 +
        5765655602825958454805056482042911316509295493350990576715062019214611) * 10 ^ 70 +
        8555953272969314884092184348885381704893327613222290382149489801695916) * 10 ^ 70 +
        9930704826322530389279341946318557743935203795964302161761735249999213) * 10 ^ 70 +
        4393829119992655695972129698478594947392861958905685825254936261859117) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (174 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (175 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (175 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_175 :
    recurrence4Scalar1Second.coeff 175 =
      -(((((31851458979 * 10 ^ 70 +
        6466041617621558988358458821670357051478936824630066330692119584787079) * 10 ^ 70 +
        7664598258385067892979669078665347604776549519876877435973444656179891) * 10 ^ 70 +
        9193905781500177010928352939651012287708857691018792158069912102517565) * 10 ^ 70 +
        6657636882290283379436159267615854571284127622489995701349770944182252) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (175 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (176 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (176 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_176 :
    recurrence4Scalar1Second.coeff 176 =
      (((((92850552179 * 10 ^ 70 +
        0362983368620642076727993887486240474490239291714674366356396446644672) * 10 ^ 70 +
        3621209832922228552502400193261982997407996467976716526746416296229501) * 10 ^ 70 +
        1171499050029813202921726752392326285291337364113256258346705192927052) * 10 ^ 70 +
        9627314440404112667143365935327775133805691703263602557032951745531778) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (176 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (177 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (177 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_177 :
    recurrence4Scalar1Second.coeff 177 =
      -(((((266645235468 * 10 ^ 70 +
        2663928539905993581389914872605663139677121598715616399975150823245565) * 10 ^ 70 +
        8192302930664078084874497236167333578759521591595994291375882967324317) * 10 ^ 70 +
        4001899142478251556844728515471906157982145527271446457170344360785286) * 10 ^ 70 +
        3123327579975484768421571834551326457679358546268906895360299067860123) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (177 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (178 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (178 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_178 :
    recurrence4Scalar1Second.coeff 178 =
      (((((754392806335 * 10 ^ 70 +
        1722478670385838825466443731962785203964540436700112329624909827515013) * 10 ^ 70 +
        0987737565360265267857916185280322175428582317290839363176150781762372) * 10 ^ 70 +
        6102906134297343927137200364201056824235468622463099811912300350908873) * 10 ^ 70 +
        3307005790017800032334005754707682577224393216404347610884904238613047) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (178 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (179 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (179 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_179 :
    recurrence4Scalar1Second.coeff 179 =
      -(((((2102785810000 * 10 ^ 70 +
        7347328044101422810567723229063045870366668564111693929959431248946013) * 10 ^ 70 +
        0355040989261090970817874423898092343163275601223336625798902641020511) * 10 ^ 70 +
        5501028485561669013374094692469079106881422398109273440535938028003743) * 10 ^ 70 +
        7760475087452057996917470433474763562614432572131417104817578938642438) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (179 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (180 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (180 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_180 :
    recurrence4Scalar1Second.coeff 180 =
      (((((5774906611160 * 10 ^ 70 +
        2903596263216448156557652070681638141836886604454795708270988623923992) * 10 ^ 70 +
        7437405546995954872429414490859131249126495772920269339730685978526774) * 10 ^ 70 +
        9519712776532907545119673906504457088561198983172622849024230491083146) * 10 ^ 70 +
        1489351438060032664966259443864236121356805624524102184587859774098146) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (180 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (181 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (181 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_181 :
    recurrence4Scalar1Second.coeff 181 =
      -(((((15626625031903 * 10 ^ 70 +
        0974058772322289586704097429792469653630571007459620701651034745832807) * 10 ^ 70 +
        3856913854930053479913778809252766975896458324552447991848677186824972) * 10 ^ 70 +
        9543712156353026714162271092350235738705797340765079920847127609242838) * 10 ^ 70 +
        8325986563068960344341848401723804369371249165102360634523057580982904) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (181 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (182 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (182 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_182 :
    recurrence4Scalar1Second.coeff 182 =
      (((((41665137315683 * 10 ^ 70 +
        8970722784344337674015223979515473963127573043809937860221950924114715) * 10 ^ 70 +
        1680408363660627555179241196188128138855816665657405231826109527397659) * 10 ^ 70 +
        6215124902765075078463008961138291341206527248278817207349062979590963) * 10 ^ 70 +
        0821731680116217177961222802577510155786020097571202388385433246117706) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (182 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (183 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (183 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_183 :
    recurrence4Scalar1Second.coeff 183 =
      -(((((109467243529294 * 10 ^ 70 +
        1079966462664216603459997011778365905432095330884012518934778494937516) * 10 ^ 70 +
        2666487469934542233658264693624108437394595719457697981477498575334036) * 10 ^ 70 +
        2368807397712093272152123020564615673375122215015427618671576642544643) * 10 ^ 70 +
        3399428141027525470258060573542690394421946440523580555945927523834674) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (183 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (184 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (184 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_184 :
    recurrence4Scalar1Second.coeff 184 =
      (((((283409797828383 * 10 ^ 70 +
        9792899914098023284908964259658522329295594229473304018537653652250553) * 10 ^ 70 +
        7090889768262429216027463415296515827473269213394672398493996838954073) * 10 ^ 70 +
        8953117397690903470374249484609006271835161802965896627335948032189106) * 10 ^ 70 +
        2674048286524621543071773326370301141410178683440666689454612383975477) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (184 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (185 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (185 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_185 :
    recurrence4Scalar1Second.coeff 185 =
      -(((((723068865114584 * 10 ^ 70 +
        2064816794054115495681274184444270411104187261340778998652126318534889) * 10 ^ 70 +
        9939340802673472694051436287360401681507913052680749976977050807062730) * 10 ^ 70 +
        0451292034080660559056119632945655727090675131971669321244611216723496) * 10 ^ 70 +
        6332480486379089858312397984554292956547045072000634439587238174874252) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (185 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (186 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (186 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_186 :
    recurrence4Scalar1Second.coeff 186 =
      (((((1817994771669666 * 10 ^ 70 +
        2979674519524668033737642381883102266868432744098689245039559380389402) * 10 ^ 70 +
        2392500199768059091069678752667751387262647745668482431618706975509220) * 10 ^ 70 +
        2670744402208539858187272245833034633898845414220086855437508161574623) * 10 ^ 70 +
        1057180581814110817727533624466387902466614908360826224884852840840419) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (186 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (187 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (187 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_187 :
    recurrence4Scalar1Second.coeff 187 =
      -(((((4504712090868252 * 10 ^ 70 +
        2064640706180803333698628747418796952321535811784418146854632104547099) * 10 ^ 70 +
        8946030747755242151636881782129139517661434452514282173247012855206663) * 10 ^ 70 +
        0249267387936074878651234750698472726357565284599291214860850707619611) * 10 ^ 70 +
        5886747439252685271821942405124648748923381654578320604872631888149893) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (187 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (188 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (188 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_188 :
    recurrence4Scalar1Second.coeff 188 =
      (((((11000575019393155 * 10 ^ 70 +
        3619247022841401780699622181932462490705451907960629429737571244594566) * 10 ^ 70 +
        9135196409389413291744811233044159289344187738617545409354672816974807) * 10 ^ 70 +
        5119668889516189936133358146018830053394241689159400145401449069953781) * 10 ^ 70 +
        4024994682871581126867375600116450259815740656623936231174110153933310) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (188 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (189 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (189 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_189 :
    recurrence4Scalar1Second.coeff 189 =
      -(((((26475818049102666 * 10 ^ 70 +
        1250262391288337662775116726538819882148335543749095366626298478422713) * 10 ^ 70 +
        3541385814148952396065832691105098148394197301579420315855393775711885) * 10 ^ 70 +
        3872609677290620983273246376711395165248655031884374963695935655819133) * 10 ^ 70 +
        9390358502714950221814746169304347300912062869116295856584801323193556) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (189 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (190 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (190 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_190 :
    recurrence4Scalar1Second.coeff 190 =
      (((((62802938172764783 * 10 ^ 70 +
        2693323810119720817824163753239628499184999887638999735945730319856325) * 10 ^ 70 +
        4755503096861328428207075545937915807649009557969031253493298382253012) * 10 ^ 70 +
        2552007277566528596199428751397084587000058103153785098805730609385715) * 10 ^ 70 +
        4935767672483599580554678471323976143355942431672163686387286868409930) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (190 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (191 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (191 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_191 :
    recurrence4Scalar1Second.coeff 191 =
      -(((((146830820602003694 * 10 ^ 70 +
        6063438165185514805852654489850894677898384341351382772320329036701449) * 10 ^ 70 +
        8242650149428993802797720404612900921892671616353153637980246569990134) * 10 ^ 70 +
        8166652636105912252455605731868386397544279312890011070636009956885161) * 10 ^ 70 +
        7793919985299261848928664405887538888792945920896536892628207418861530) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (191 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (192 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (192 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_192 :
    recurrence4Scalar1Second.coeff 192 =
      (((((338353345240546592 * 10 ^ 70 +
        2080817492023757257373367679586169291134074479751636357790468836182999) * 10 ^ 70 +
        6423687920521624862697861184272255854531867638567098819933824945252512) * 10 ^ 70 +
        3377798361728039003190183519547192927049243591479851825987170137198482) * 10 ^ 70 +
        9775028037370858546207158696081790258617808353467075432634620222149926) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (192 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (193 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (193 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_193 :
    recurrence4Scalar1Second.coeff 193 =
      -(((((768507600102419829 * 10 ^ 70 +
        8281822655664984210997357959586611344242693420132654001185120804790555) * 10 ^ 70 +
        5667124428727750481810344881534531700113552535392820562765628795835754) * 10 ^ 70 +
        2151348443547091025745482871554044427041119961435005138810021081623939) * 10 ^ 70 +
        5961113918393741395915107237191637880088903688877798209770586250251615) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (193 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (194 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (194 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_194 :
    recurrence4Scalar1Second.coeff 194 =
      (((((1720512782426828484 * 10 ^ 70 +
        2036756300248512896118508991241999757669865025927749696797889639558214) * 10 ^ 70 +
        0354207396058004831327882713249776723907076789420325662229959709574797) * 10 ^ 70 +
        9191748987483240333464553111222393964680669006531817928744473712479126) * 10 ^ 70 +
        0859573839631000830539038159553198042436923876440445255382540670054559) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (194 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (195 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (195 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_195 :
    recurrence4Scalar1Second.coeff 195 =
      -(((((3796701073098758401 * 10 ^ 70 +
        5530489665608467793486913082848897077381713258725648771207347492766336) * 10 ^ 70 +
        8570463160287785523097915566270443459284888299406635573596118197911227) * 10 ^ 70 +
        2778201227281572801375757947653013314073961236030965894726098791831134) * 10 ^ 70 +
        9384257340322516492004872472037043768488741690507646820758740073769510) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (195 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (196 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (196 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_196 :
    recurrence4Scalar1Second.coeff 196 =
      (((((8258467866741681784 * 10 ^ 70 +
        5498300858414679169848258501422969102144773335905950472003036149469154) * 10 ^ 70 +
        3373889866695213112800154739339516556562625388457036208074591664185250) * 10 ^ 70 +
        6776703323225252491959838255867121984613768781959711279525048529110736) * 10 ^ 70 +
        2107629024858118765431970716046412860475385107367209025632534589713010) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (196 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (197 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (197 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_197 :
    recurrence4Scalar1Second.coeff 197 =
      -(((((17706878648860989564 * 10 ^ 70 +
        5026718431596830531292803008817457185564316104036607285416703633419753) * 10 ^ 70 +
        3837779775547620748848616243179800602887960579459735758671568974932820) * 10 ^ 70 +
        5906377309494960484605151801839665094616879040846167207992269484320337) * 10 ^ 70 +
        8419965459545553781889105604040020778886482889260456005358247014466361) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (197 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (198 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (198 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_198 :
    recurrence4Scalar1Second.coeff 198 =
      (((((37422938450915169542 * 10 ^ 70 +
        2833262428062816476131558171572364782596007480043533091726725672576854) * 10 ^ 70 +
        9527769793397522849277616834037765541573097861704407072146263260637127) * 10 ^ 70 +
        4053153072914641567148954980737368581134642008458976823682666965266058) * 10 ^ 70 +
        8083532063046714005950235803676750382586306602088303016378888987893627) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (198 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (199 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (199 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_199 :
    recurrence4Scalar1Second.coeff 199 =
      -(((((77963259506617868427 * 10 ^ 70 +
        2525571222302356986573907250150330087174741182063558584110483077148372) * 10 ^ 70 +
        9008150238184767494957495103688712902437625706282294755840851108646920) * 10 ^ 70 +
        9184844887576612061737349317899193869374954367677296835978643371204211) * 10 ^ 70 +
        1415371134811127948871622889360273447668856502101783712049305407076382) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (199 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (200 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (200 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_200 :
    recurrence4Scalar1Second.coeff 200 =
      (((((160103246207659170753 * 10 ^ 70 +
        4921973009266894299764406024722191935208804299484088723284442403767757) * 10 ^ 70 +
        7341478209618045689161943218470159749096620478449001267149435321050847) * 10 ^ 70 +
        7030898662672861637796341013832023651851860144806925828047272081695703) * 10 ^ 70 +
        6276849504178032283809344902614755554649004681896417246622400145311277) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (200 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (201 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (201 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_201 :
    recurrence4Scalar1Second.coeff 201 =
      -(((((324092542672220263719 * 10 ^ 70 +
        3285354751894727120171765972776732300656257206719663021484338566797940) * 10 ^ 70 +
        0215058710567484754261379046779680243560536544223242792558532588650908) * 10 ^ 70 +
        6475963337294381488220500209298511155323417444959160895515172082891892) * 10 ^ 70 +
        7375665065433266197372603069164149372654218555779554459462621343294871) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (201 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (202 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (202 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_202 :
    recurrence4Scalar1Second.coeff 202 =
      (((((646690107198466847848 * 10 ^ 70 +
        2553189390656480586607043845466688376866496754098823129434433136327029) * 10 ^ 70 +
        5270048519034338148494630391416388632119519025197125927764625190436183) * 10 ^ 70 +
        1308453292296718261183233846125278895597566651489364755242872836417504) * 10 ^ 70 +
        6532486003332020996824365214287793082874324243999036620988489261199263) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (202 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (203 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (203 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_203 :
    recurrence4Scalar1Second.coeff 203 =
      -(((((1271979053627219613741 * 10 ^ 70 +
        4369005518687683269565425648829939393946010079584506082215523320108461) * 10 ^ 70 +
        3825392637610305572540257248231618751017338149951554826488950632680741) * 10 ^ 70 +
        6501426819165067293277265246217980271398614754661093359866055383683797) * 10 ^ 70 +
        7334316644893378169780614097963263639668260832676240421504809861562181) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (203 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (204 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (204 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_204 :
    recurrence4Scalar1Second.coeff 204 =
      (((((2466137161318618181173 * 10 ^ 70 +
        9803324902410508285630629880548305768670290406044338472052547350954511) * 10 ^ 70 +
        8258026297499724522756361827332360796108515346894329466886898889095629) * 10 ^ 70 +
        8732768413988822603122399147539453482142036173880856383080230060125116) * 10 ^ 70 +
        2665389606799873169032238885535651312803188004889563932072664061388150) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (204 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (205 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (205 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_205 :
    recurrence4Scalar1Second.coeff 205 =
      -(((((4713066562309776372899 * 10 ^ 70 +
        3108466711290792005640280170097816136146212219887070620885393293209099) * 10 ^ 70 +
        8861528022057829275334431998690202069281702159208370865522376185959012) * 10 ^ 70 +
        9260544261773032810363396520116763736933987441756702474839022195762677) * 10 ^ 70 +
        2551143776607451467170780292793908443984415750804081037573844845261788) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (205 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (206 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (206 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_206 :
    recurrence4Scalar1Second.coeff 206 =
      (((((8878365878648172262810 * 10 ^ 70 +
        7550731536136459375286347097537242284129667334817125421396794844698891) * 10 ^ 70 +
        8825779976327207348400048091681916767306094825863222358067561024204876) * 10 ^ 70 +
        4115050899589136234176956672338471743707585195114179525315676687971047) * 10 ^ 70 +
        5052232090028512005752987691252682327635592878750894412520839574471421) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (206 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (207 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (207 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_207 :
    recurrence4Scalar1Second.coeff 207 =
      -(((((16485344893113825714149 * 10 ^ 70 +
        9306959079572200039778654859586915394332402558587321665244539919223585) * 10 ^ 70 +
        5138263219585266695330573872690837156610089078321871919884970402613020) * 10 ^ 70 +
        9527780230710517795065422056478834598328720656647731286338836137374094) * 10 ^ 70 +
        4500373512167540293080510826217988555833028171558196032783621423952811) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (207 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (208 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (208 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_208 :
    recurrence4Scalar1Second.coeff 208 =
      (((((30170966817933990214246 * 10 ^ 70 +
        3245253836254632021235694926747864399455462140676108688287717670377838) * 10 ^ 70 +
        3848489280025607234695004157149937812403308127448648900568846873858313) * 10 ^ 70 +
        9314267570521927930424821466290380557418009974261135771225671474407904) * 10 ^ 70 +
        9993148948327535398891130691061515855935087612459393204726888433539197) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (208 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (209 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (209 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_209 :
    recurrence4Scalar1Second.coeff 209 =
      -(((((54424613579265150538590 * 10 ^ 70 +
        6760911471348355088485880479204739843782416749046753823754946276458135) * 10 ^ 70 +
        6676567298944291958956453878266472864658438201143080432029368537211987) * 10 ^ 70 +
        2423678573180961575713897181953554069201804398585761761765965744693508) * 10 ^ 70 +
        7347835592779979189110364609103899676152410356540085891324545872097162) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (209 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (210 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (210 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_210 :
    recurrence4Scalar1Second.coeff 210 =
      (((((96761608997644540549178 * 10 ^ 70 +
        0370065899416129953274854855653505863753141220873449838197026616999179) * 10 ^ 70 +
        5185638231972937048214538658552072801874298229388826147701357937602656) * 10 ^ 70 +
        1934136817761451033803985461186745625941651814649339383221260144918648) * 10 ^ 70 +
        8373220584991347004579671147434499368163385180792013357166961178497041) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (210 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (211 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (211 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_211 :
    recurrence4Scalar1Second.coeff 211 =
      -(((((169549606850309855499497 * 10 ^ 70 +
        9851713152791101871381586839908055259535063221779093395910064503669299) * 10 ^ 70 +
        8728369271040726339359976158695034454971242962811215650362237603338263) * 10 ^ 70 +
        7934213209768769555698474962649185767751526195912435806071787811053585) * 10 ^ 70 +
        2309547120548605179365954908334027758540523921682966876838777379191436) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (211 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (212 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (212 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_212 :
    recurrence4Scalar1Second.coeff 212 =
      (((((292791410630463690266925 * 10 ^ 70 +
        3790027740649269610845429664230032488918228221602646220365705097798890) * 10 ^ 70 +
        9532836214203580771138500399424966873988404816858497224031782868157365) * 10 ^ 70 +
        8713986478569265047111964107156720159815172985445219830506510057851888) * 10 ^ 70 +
        7266592118465012526885053051235245822077294663668748937167334193416034) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (212 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (213 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (213 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_213 :
    recurrence4Scalar1Second.coeff 213 =
      -(((((498272351474138854473957 * 10 ^ 70 +
        9841150313714949107726058627347150451198112209655888628458554404043125) * 10 ^ 70 +
        3755229496049881034384615570530197138553710735212576628551466375414209) * 10 ^ 70 +
        0439176562935448454987122314416896232201690822903011071761465486364767) * 10 ^ 70 +
        4655925102279701796113676324286636597754182018406675541308479009593255) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (213 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (214 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (214 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_214 :
    recurrence4Scalar1Second.coeff 214 =
      (((((835599417696704153853730 * 10 ^ 70 +
        4667072488670110228609818847084603984838855658904167697022476480340480) * 10 ^ 70 +
        6474690141254703370009401576207225165658331314458811636416656442187339) * 10 ^ 70 +
        3837751255096625466250034407593934087832872406040834106365594221906275) * 10 ^ 70 +
        2019410712445450216634723919652224659156522768676720888618095659507574) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (214 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (215 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (215 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_215 :
    recurrence4Scalar1Second.coeff 215 =
      -(((((1380781138898603703916715 * 10 ^ 70 +
        0393793604643249838029069787547806504373018686202724043539781456176250) * 10 ^ 70 +
        4284085335977515794782192168673856185850860206967073249130151782541651) * 10 ^ 70 +
        1896331456212253072875305717318351563516529823014969673632012700829217) * 10 ^ 70 +
        0462519495306504128337237039910512321670387947071464835813711407739938) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (215 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (216 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (216 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_216 :
    recurrence4Scalar1Second.coeff 216 =
      (((((2248099495450758345282116 * 10 ^ 70 +
        9332664619974377431794580638326807506177524309377987215203419655577649) * 10 ^ 70 +
        0986795675658638518361013766029105129392695325178358580940882252423168) * 10 ^ 70 +
        9546553592396079432567486255549341217497051676471278584541642593920571) * 10 ^ 70 +
        0317763191191292679787432130414389196354965197016322239252813844240053) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (216 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (217 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (217 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_217 :
    recurrence4Scalar1Second.coeff 217 =
      -(((((3606071515107691254026500 * 10 ^ 70 +
        3984020246051846844895669269463974145682662013875126522042122820438176) * 10 ^ 70 +
        0774455874134455298134016385311864955384901528130336190436991068392144) * 10 ^ 70 +
        3656462331260011580271993085151892796283591139491326934213174563969703) * 10 ^ 70 +
        7859425346993405980888661948311490510241086353067521761538799689108596) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (217 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (218 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (218 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_218 :
    recurrence4Scalar1Second.coeff 218 =
      (((((5698235400084143946783086 * 10 ^ 70 +
        9624958729918925171960555942188309000554932345084811191719218032170353) * 10 ^ 70 +
        6356258310958351892576378686007609445586944075029994695031944658782896) * 10 ^ 70 +
        9553089834674615613710499469777951183691109271485691998233302607841052) * 10 ^ 70 +
        9000677984516245322576234913188382817566594513149282143168533039127325) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (218 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (219 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (219 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_219 :
    recurrence4Scalar1Second.coeff 219 =
      -(((((8869252530898424501171691 * 10 ^ 70 +
        2758949992689369553615206375636300549317056385150434283728545498254084) * 10 ^ 70 +
        8771614788609053246533045104985181387783474937305301659323727145132734) * 10 ^ 70 +
        0385182957374877436121339087944352908483952579350505183759136091425850) * 10 ^ 70 +
        1043966428788944646415611217843840035894794697230141436481218038552746) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (219 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (220 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (220 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_220 :
    recurrence4Scalar1Second.coeff 220 =
      (((((13596305249509478974293590 * 10 ^ 70 +
        8721060864766098380968309707088686788710046748201842800051796092149979) * 10 ^ 70 +
        9567793258497375698201968539208948932104348801601168279997687819627637) * 10 ^ 70 +
        2875577812607504889361804101540076831832386364523456547898154224799840) * 10 ^ 70 +
        6239432482853732241784821070885172492001354314155569223657839709007285) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (220 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (221 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (221 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_221 :
    recurrence4Scalar1Second.coeff 221 =
      -(((((20524895664821397354959345 * 10 ^ 70 +
        2954295677483610422026915134181514446741826679539124803262467272141589) * 10 ^ 70 +
        1401473702606965600496238139629993225060460346599545120592215564244020) * 10 ^ 70 +
        2778097709691472751839140635998469226882945203644282066061094954514218) * 10 ^ 70 +
        4120631637391445399690429749674471928983753168468789488029205656442344) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (221 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (222 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (222 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_222 :
    recurrence4Scalar1Second.coeff 222 =
      (((((30506824795304409629304980 * 10 ^ 70 +
        4802546227747942960570431681888205271518463267281475976541007747469843) * 10 ^ 70 +
        5026934744761431199945566834663336162077379086302245417339838155674266) * 10 ^ 70 +
        5867701108123076393242065813195755850069645370858368210199034755541959) * 10 ^ 70 +
        4529228619311945320857759271163420661256645061444681659717308207283674) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (222 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (223 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (223 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_223 :
    recurrence4Scalar1Second.coeff 223 =
      -(((((44636297328947795465434954 * 10 ^ 70 +
        7034982204521555702078137868968942436677786434419388174840922028555058) * 10 ^ 70 +
        8226847996375040775085576281427226950439807032890784118690191560331625) * 10 ^ 70 +
        8649796481827203623754826552600725873630296382157489786499424929537431) * 10 ^ 70 +
        5185702921585560519246335988770258917209098810425762248838200137662253) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (223 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (224 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (224 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_224 :
    recurrence4Scalar1Second.coeff 224 =
      (((((64277762283386024630274007 * 10 ^ 70 +
        1322452047003742909448253013815132128024730371949861066933901875048383) * 10 ^ 70 +
        5599685200634379818561954149675881709365176691918997362430766924001557) * 10 ^ 70 +
        7812194797517443167727968039637653691945247769734869308570054080759006) * 10 ^ 70 +
        2262767461558108379998156927294509285144890273275409016716282565144276) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (224 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (225 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (225 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_225 :
    recurrence4Scalar1Second.coeff 225 =
      -(((((91076374222210967959869321 * 10 ^ 70 +
        3450927426020252510533026884386805681227618742904055389137383632989199) * 10 ^ 70 +
        3007118090221521373402953869157588560539383975551997057501267278699794) * 10 ^ 70 +
        4071665002138251637035715467847130773770835437472612354845579875547896) * 10 ^ 70 +
        8365412902013762917527291161908847463507663615312569956432513481775107) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (225 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (226 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (226 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_226 :
    recurrence4Scalar1Second.coeff 226 =
      (((((126939097136595707123571005 * 10 ^ 70 +
        3139270648972654589739751272579356100549409281712629372830115226196592) * 10 ^ 70 +
        3736866119204178952314633733292001602381144312152915213264751738373786) * 10 ^ 70 +
        6121592754754232983306427070373470767044889789181648917549655831608139) * 10 ^ 70 +
        8092524862662769952327426392384541497191045546988697961643805817125109) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (226 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (227 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (227 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_227 :
    recurrence4Scalar1Second.coeff 227 =
      -(((((173971902796878330577499077 * 10 ^ 70 +
        5552773377810021654348509478517875188089217929547697240331515752833757) * 10 ^ 70 +
        3911342018719382738404709366497583125205016741854649338987034503500801) * 10 ^ 70 +
        9819717167392716291304284326595675752338778089357501096128802697812933) * 10 ^ 70 +
        3699952189646154403873858835277746170589573922827667230276100397473607) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (227 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (228 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (228 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_228 :
    recurrence4Scalar1Second.coeff 228 =
      (((((234356853477826135483874636 * 10 ^ 70 +
        3539764194352129067029438412117026668043265718174797546766057743269213) * 10 ^ 70 +
        7563276849979084496051485323680847102856858593374940653083573479298306) * 10 ^ 70 +
        3229854573796995499631571973453492298208957120056126293547515387959824) * 10 ^ 70 +
        8588173426259748126071311565440547014300706762208143940381642766187467) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (228 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (229 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (229 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_229 :
    recurrence4Scalar1Second.coeff 229 =
      -(((((310152885275789095354193712 * 10 ^ 70 +
        4451444861008298595340692387379016473685073981213448857518304654598046) * 10 ^ 70 +
        7698610799746807691078619204607133988267479339355668627045846529717438) * 10 ^ 70 +
        9891404323569456080685350800755001319920379530165662074555344641978961) * 10 ^ 70 +
        0430522553844886721193800949203518059310493963586741070382608068551564) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (229 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (230 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (230 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_230 :
    recurrence4Scalar1Second.coeff 230 =
      (((((403006694427585549340796322 * 10 ^ 70 +
        1018575008626511628196290519095793819087526498121770392428148686978885) * 10 ^ 70 +
        4824121993027352223681565788326970549068972399990432485492533765831214) * 10 ^ 70 +
        2579547987437657844192119646688119645809213565607551060198594242689635) * 10 ^ 70 +
        3757409663726274466999061762417174481634313758716850839548846265633785) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (230 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (231 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (231 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_231 :
    recurrence4Scalar1Second.coeff 231 =
      -(((((513766109635470966579028379 * 10 ^ 70 +
        5520424850600296350313584757533977548694491139135651131375106878263632) * 10 ^ 70 +
        1088510791936299880908858239345114685286939661460838266179503849349429) * 10 ^ 70 +
        5784664197420058592560122753787212252726806501516792867323038890539415) * 10 ^ 70 +
        5785981087594299968044301532080844467927500791902433367698520952398684) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (231 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (232 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (232 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_232 :
    recurrence4Scalar1Second.coeff 232 =
      (((((641998320526939874182553327 * 10 ^ 70 +
        1217801231243217719326736912852842214898641145278174589856611659803818) * 10 ^ 70 +
        6366845028954427588412325429640939765062116938269793132136172942763150) * 10 ^ 70 +
        6771437382671015555141743486777260581515025754286278103481780592354992) * 10 ^ 70 +
        1595350189069658184352246041061776161272781228438215550210499124134307) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (232 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (233 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (233 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_233 :
    recurrence4Scalar1Second.coeff 233 =
      -(((((785429489373611953175291286 * 10 ^ 70 +
        1610363239120786075563696675645228798582880218376416542583501680161031) * 10 ^ 70 +
        6288393310833645747968141543714808076640158374595840888831671818573946) * 10 ^ 70 +
        3723025175238050079841806890966271797718330904131754749155639037415430) * 10 ^ 70 +
        3695095895004243447696443632481462250400143979709053086596728015952661) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (233 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (234 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (234 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_234 :
    recurrence4Scalar1Second.coeff 234 =
      (((((939340079456755918197604905 * 10 ^ 70 +
        6645156207520050684592770125438862734571456302185722953154155534996331) * 10 ^ 70 +
        7919038198108294592430184629952683802128658528732990400570772815737338) * 10 ^ 70 +
        7967905153879774221687550676254798639034365533894877431907808682795580) * 10 ^ 70 +
        4777196536747410635045366887285349160369795208234559823813750051840380) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (234 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (235 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (235 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_235 :
    recurrence4Scalar1Second.coeff 235 =
      -(((((1095970289739031771944113543 * 10 ^ 70 +
        9665206970794944945663169899744138725585352277215566585293735127262243) * 10 ^ 70 +
        7449052510009267526777206977983610790109481660387992997106186512015085) * 10 ^ 70 +
        0931808718557924721869452346350558337399878461680589911832858960879399) * 10 ^ 70 +
        6055101342677160474768384872871684948225329097068532070183678927997171) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (235 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (236 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (236 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_236 :
    recurrence4Scalar1Second.coeff 236 =
      (((((1244009920643576342730522621 * 10 ^ 70 +
        5160197326866650062844808290407585040197248898811251416466133200144676) * 10 ^ 70 +
        0321718458679808528349256339914227820233242862898755520454681333236840) * 10 ^ 70 +
        6027508073454682590696025241871297721060612023337200974674628613602862) * 10 ^ 70 +
        3069272320083452744774131467274067065180353811744469493805203548757949) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (236 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (237 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (237 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_237 :
    recurrence4Scalar1Second.coeff 237 =
      -(((((1368263537444817456336377991 * 10 ^ 70 +
        5319846341692681785180037610975954523293396384772819845685967019200686) * 10 ^ 70 +
        6073689195799005512370033857576365818533455937973666314316259763613584) * 10 ^ 70 +
        1170784377463608933981878759264974238896951859612309061640618117701338) * 10 ^ 70 +
        1282748360446091140451475113011670073233087333686594809431871920796080) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (237 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (238 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (238 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_238 :
    recurrence4Scalar1Second.coeff 238 =
      (((((1449591055951173564475263054 * 10 ^ 70 +
        0145184157421612857410684583190146291177410196573567651464784858138876) * 10 ^ 70 +
        4287976241953818000176782953211882273631588221158255850514405906002203) * 10 ^ 70 +
        0013228312868802223286907018940814541973319419626468181566543644382279) * 10 ^ 70 +
        1746325196418603074833283258089154471843107176978675428289375241295460) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (238 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (239 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (239 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_239 :
    recurrence4Scalar1Second.coeff 239 =
      -(((((1465221855522087376139867567 * 10 ^ 70 +
        1487685909585456293282682024500538906890547905476291939728305670201731) * 10 ^ 70 +
        9913795806562647749831600108971553533388127531501092829467308139502511) * 10 ^ 70 +
        7303823367947728076798996268534351674096409126892527173969666616971292) * 10 ^ 70 +
        6572414310768929877997028458586553016642045897223742659129441973686016) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (239 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (240 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (240 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_240 :
    recurrence4Scalar1Second.coeff 240 =
      (((((1389523842650489374371013321 * 10 ^ 70 +
        3061362134131228231120315977169402265848251803202138426375190005901978) * 10 ^ 70 +
        0108433820264666789410984880412076819492621797452729878612146901996547) * 10 ^ 70 +
        2140540061775836399266832973408711704397440216318112700363344598746248) * 10 ^ 70 +
        5552700345032441808044522905809845530878505200185281527470250472702937) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (240 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (241 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (241 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_241 :
    recurrence4Scalar1Second.coeff 241 =
      -(((((1195275598300550181945002986 * 10 ^ 70 +
        8913175191269554018492677223640611465643276368296091089250093006347326) * 10 ^ 70 +
        5639448708294646011954790105433495231183120426692506035602498934646169) * 10 ^ 70 +
        5368711547436805465084139996931132491340078745189919512982634317192071) * 10 ^ 70 +
        4007943039215868786019399012875969447246582356992955856778210097096907) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (241 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (242 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (242 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_242 :
    recurrence4Scalar1Second.coeff 242 =
      (((((855440137863527391265830191 * 10 ^ 70 +
        5033377124702679646368677190187408059485614814051000120275927085655053) * 10 ^ 70 +
        1492477539233170315294615273066911587717702740436224567059908868075136) * 10 ^ 70 +
        3888730070541210819157832851135134116712686776801947735815110492728747) * 10 ^ 70 +
        7351925496531537144501835225062850064995581275068990858264293414935799) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (242 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (243 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (243 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_243 :
    recurrence4Scalar1Second.coeff 243 =
      -(((((345376024024573876194631425 * 10 ^ 70 +
        3413245875767717564011493014121431064645343924828152710276153662559011) * 10 ^ 70 +
        2899614108028451157819768405825213377892674321963816220663791945218599) * 10 ^ 70 +
        5246135749275597907867946956451372580475920458245548399807024865462437) * 10 ^ 70 +
        1134592310747257006297318433150504720531375230609828846039321994757758) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (243 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (244 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (244 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_244 :
    recurrence4Scalar1Second.coeff 244 =
      -(((((354648228663536970965253911 * 10 ^ 70 +
        9680772970910884382293570942015216920897157262671639202937432144113864) * 10 ^ 70 +
        9656483321024753964074361830212645280634823087958308408826867434345094) * 10 ^ 70 +
        1991297709814169772855589273262255521138558656571666634536879844204939) * 10 ^ 70 +
        4769380130288690406715328897882537092133982822579830476334895513605968) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (244 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (245 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (245 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_245 :
    recurrence4Scalar1Second.coeff 245 =
      (((((1256838455536064196204283070 * 10 ^ 70 +
        1632889171082594525080000051811869338555341744568195692410090234366064) * 10 ^ 70 +
        8198757633442086477845546734164083431317333376072847158271354151016782) * 10 ^ 70 +
        0280819813173798990896009267541786238991486965692396658279401836162759) * 10 ^ 70 +
        0553583974122950330473200999497839482182488393234699175725124738870460) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (245 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (246 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (246 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_246 :
    recurrence4Scalar1Second.coeff 246 =
      -(((((2363415279367108107200506367 * 10 ^ 70 +
        3920870571713899574816654316476629789827083864580715932428339456162867) * 10 ^ 70 +
        4743266185176232172792917769038350216056859377083825511764701752764861) * 10 ^ 70 +
        3387025644896120225976027893488998910497853945971765228560058501020239) * 10 ^ 70 +
        3695420702619149137151556256041242419679121936671711929372050181855488) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (246 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (247 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (247 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_247 :
    recurrence4Scalar1Second.coeff 247 =
      (((((3664600136572796843347730141 * 10 ^ 70 +
        2759070790093154880399687280838399579551002394451896104032373623867804) * 10 ^ 70 +
        4930571968157687709327869032746887989225745198660701339331492824885101) * 10 ^ 70 +
        2560462626039342084622057978788324553830752666820104556611134535214366) * 10 ^ 70 +
        2313724321100582025859297278998798036185266363875072133312821818816307) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (247 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (248 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (248 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_248 :
    recurrence4Scalar1Second.coeff 248 =
      -(((((5137335670770175199745669363 * 10 ^ 70 +
        8497126862502214675390080331772025245020268928898908234969380068862568) * 10 ^ 70 +
        6394164550578294971641772208494069018970206940574763339525172086290096) * 10 ^ 70 +
        4556179862566802947782696313204438763298817270892773718662800093635360) * 10 ^ 70 +
        8365735666776473056463174687404809129238868770082772756888695104630233) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (248 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (249 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (249 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_249 :
    recurrence4Scalar1Second.coeff 249 =
      (((((6744990167506193067298803259 * 10 ^ 70 +
        3155754601000156365834539271182149097044615615610560399283000104903174) * 10 ^ 70 +
        1785429198595841177036324888991704092871110661115266259459816909746390) * 10 ^ 70 +
        5569625861537853600921708250229127005305254951890465138057092994270385) * 10 ^ 70 +
        5268073198664864100755325378592024593881678612019782691968051115257902) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (249 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (250 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (250 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_250 :
    recurrence4Scalar1Second.coeff 250 =
      -(((((8438217621572457402857917220 * 10 ^ 70 +
        2303029414865792199292451956738311232696075185539970348818965925593687) * 10 ^ 70 +
        3054973096494016161526446504486392970892967042584851978722089724485916) * 10 ^ 70 +
        9312474806444931209831831226559754432852435396212783353435782180908316) * 10 ^ 70 +
        2515587099779083066070937542376991252169697514765976158918548826105385) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (250 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (251 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (251 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_251 :
    recurrence4Scalar1Second.coeff 251 =
      (((((10157033541281492631532408163 * 10 ^ 70 +
        5175131382466103155130463976094560777628865264007195005961785893737281) * 10 ^ 70 +
        0811377538941980111553526391622731450969436749157174865150044341487139) * 10 ^ 70 +
        2372729178233388037166378318009388967401845638993305780684586540789761) * 10 ^ 70 +
        2673347996328086492305429877905516778231924236036023804613694517753754) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (251 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (252 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (252 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_252 :
    recurrence4Scalar1Second.coeff 252 =
      -(((((11834033332121160099869532885 * 10 ^ 70 +
        8367774389004796140583801678605516069534180450232210113664073583578354) * 10 ^ 70 +
        0128918395753435207620713843572239059075908278502418961406635970843709) * 10 ^ 70 +
        4443529298202052551010771152098313523240045405991178221791511947920158) * 10 ^ 70 +
        8640732519264819654021153368607521306930929618424755954979406894513589) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (252 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (253 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (253 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_253 :
    recurrence4Scalar1Second.coeff 253 =
      (((((13398541560018667942643502598 * 10 ^ 70 +
        8327225796481364592044402665016777487993229782894270895203235868077109) * 10 ^ 70 +
        5459543706275102736419038728223966555586941163828479350549263636292512) * 10 ^ 70 +
        3669494691673001216791052370465420389461320825887612874910638926532148) * 10 ^ 70 +
        9171647537955006923495204483185171512942851266848725698668460145568317) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (253 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (254 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (254 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_254 :
    recurrence4Scalar1Second.coeff 254 =
      -(((((14781355697961824712180667563 * 10 ^ 70 +
        7577779790673045888882377988269322039059093916073539843426824477847577) * 10 ^ 70 +
        6881908216845679205351529576166398689978363393794998322816169247107343) * 10 ^ 70 +
        6809946383180758434852689523284208528627975877402338480942074144820340) * 10 ^ 70 +
        6910722589264002348598499904105286349882270795391334759891048446645647) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (254 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (255 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (255 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_255 :
    recurrence4Scalar1Second.coeff 255 =
      (((((15919655907482101971950259895 * 10 ^ 70 +
        8265264897898276361506982968152322788720625019207362350645507460737040) * 10 ^ 70 +
        0640486083999633850398857314294247437407121669003734554273421030018064) * 10 ^ 70 +
        2219251050532635148986794428462225026731707432502783266619174947897122) * 10 ^ 70 +
        2435387253872460173797540816789179302190981049711257307503714426893690) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (255 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (256 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (256 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_256 :
    recurrence4Scalar1Second.coeff 256 =
      -(((((16761608289192596992477176128 * 10 ^ 70 +
        9250994027701612190468508771962577408375682247182065300870802929246078) * 10 ^ 70 +
        2316589097725056205433604068570213721496228300496499633036068301853756) * 10 ^ 70 +
        8658340107254059753582202103898706167354859972678004460152411730956209) * 10 ^ 70 +
        9110617385687530394575597858715350194388926820770555640616450366139561) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (256 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (257 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (257 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_257 :
    recurrence4Scalar1Second.coeff 257 =
      (((((17270201831769075691523854614 * 10 ^ 70 +
        6891144213642261010627727935025478397804880988451595052575279453690219) * 10 ^ 70 +
        6273354086068235358580105466544170424287246189644656538080994098963715) * 10 ^ 70 +
        8792687273022098907097658610143762074034351977697931936030918255907193) * 10 ^ 70 +
        2594098342074625723288004096572963533183880061197704284124746393436292) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (257 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (258 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (258 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_258 :
    recurrence4Scalar1Second.coeff 258 =
      -(((((17425929799028233793795263922 * 10 ^ 70 +
        5255811761325093801889643957805359996812578452828394238082116559820508) * 10 ^ 70 +
        5486210897592561387272752377818944141895402041567369498389775298200510) * 10 ^ 70 +
        7488573629823307123329546205357399136611285454049597713776446280524054) * 10 ^ 70 +
        7195130369540627971544938110251474963267240123536137104468188353292777) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (258 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (259 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (259 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_259 :
    recurrence4Scalar1Second.coeff 259 =
      (((((17228046642271678984113028656 * 10 ^ 70 +
        8080072358474442464696874048865605800387798457971820723807128078355833) * 10 ^ 70 +
        8537142895879672046096032123347055669088898538905613403573592854285064) * 10 ^ 70 +
        6257176716358224063648559511331746518755957302752171245715596241948365) * 10 ^ 70 +
        8571422400654783127145513544059426079573930152175416565688092543398556) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (259 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (260 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (260 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_260 :
    recurrence4Scalar1Second.coeff 260 =
      -(((((16694286161814129520466429106 * 10 ^ 70 +
        4818053688289050253204838577974921048038874355715191636528339077055180) * 10 ^ 70 +
        8722650314813502902725658370587726964889343953143616929959898301769281) * 10 ^ 70 +
        4204048065466946535421344923273573306924325043539061018097836750582194) * 10 ^ 70 +
        8856459504275954826699775929121989256932143125980863888437556137853228) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (260 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (261 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (261 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_261 :
    recurrence4Scalar1Second.coeff 261 =
      (((((15859094733851769437952643581 * 10 ^ 70 +
        8842166670436084925237824040441835154468526956941203399177100192219877) * 10 ^ 70 +
        6458856000231170544736632026972752910851741599559858138691048084854348) * 10 ^ 70 +
        1009457353202006550642525902572528128588802437158647280392634373217251) * 10 ^ 70 +
        4279253014335117999578305183044044836973266405096340029671403638131031) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (261 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (262 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (262 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_262 :
    recurrence4Scalar1Second.coeff 262 =
      -(((((14770592184268820163722487390 * 10 ^ 70 +
        1940391126633653922417898159330573065639827425103684549905812185908344) * 10 ^ 70 +
        6559410601073915819481917508877567390758078794873157268305868802201528) * 10 ^ 70 +
        1066930218167498423784910643388698086575739615898294900026504560015641) * 10 ^ 70 +
        4641935773538555400203368233127894232843269841740820456124525895175739) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (262 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (263 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (263 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_263 :
    recurrence4Scalar1Second.coeff 263 =
      (((((13486601271134112254525331564 * 10 ^ 70 +
        1922642795761333538284962819340664393116591535325631436311974849485699) * 10 ^ 70 +
        1765582658552511288986462673264430436340582443183493980402464032971830) * 10 ^ 70 +
        3609248553732482063353903253373923309292095970895926255859630676211874) * 10 ^ 70 +
        5011267211002681524835433516356849924401387160491023516315355053525341) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (263 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (264 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (264 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_264 :
    recurrence4Scalar1Second.coeff 264 =
      -(((((12070168720896679103452425975 * 10 ^ 70 +
        8197032650386744808165071778903794643363952335449707284239706961267377) * 10 ^ 70 +
        9875766372753656332747364403602354910409616230024266970392928202759301) * 10 ^ 70 +
        3690241490772817457538507019150235947244915289203602341924457359999799) * 10 ^ 70 +
        3039773538342531030889380512444973753654127411126740429653216590021894) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (264 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (265 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (265 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_265 :
    recurrence4Scalar1Second.coeff 265 =
      (((((10585027752176142863312411342 * 10 ^ 70 +
        7875168858573992264681409195742329217357451067817772878067829177890616) * 10 ^ 70 +
        9009806402351326355175459044329155628955617861825941515790289431909851) * 10 ^ 70 +
        2287705268086976842246668481902094363236573161502568753804521733478459) * 10 ^ 70 +
        1408659194438841844009711758826886060769783018368760236910891138732869) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (265 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (266 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (266 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_266 :
    recurrence4Scalar1Second.coeff 266 =
      -(((((9091423840275256435169999216 * 10 ^ 70 +
        5440603454747236755718924093805897698985273380432542249978161631145055) * 10 ^ 70 +
        1771308447740407612253216849835902031774920063886146405308096515769545) * 10 ^ 70 +
        8009137170015823231952850650581478039864116666135912055183579367064391) * 10 ^ 70 +
        8290703419361259682180228488911456449546201075741971684374569795359176) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (266 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (267 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (267 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_267 :
    recurrence4Scalar1Second.coeff 267 =
      (((((7642649898406277731207602731 * 10 ^ 70 +
        8895901167954348181616746435998066338946928941107435406602716853585682) * 10 ^ 70 +
        5292079585580463265874258356393195691994927720495747047627636483212309) * 10 ^ 70 +
        6595190486158245837285755234055489140153765824740923477885758246585304) * 10 ^ 70 +
        0167434915547170363106278691333213552047959163887639938791643142917110) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (267 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (268 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (268 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_268 :
    recurrence4Scalar1Second.coeff 268 =
      -(((((6282528016152530923584022327 * 10 ^ 70 +
        9112971633021930618110211900982643731178809465142685147298967921874988) * 10 ^ 70 +
        2827213762050604019499068222660706080196212397102556357230823372813084) * 10 ^ 70 +
        5330770999599345890193377193346914514414890089907446342735113443382435) * 10 ^ 70 +
        9806078316960913340078122786991450998153573832674021603482549527874229) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (268 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (269 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (269 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_269 :
    recurrence4Scalar1Second.coeff 269 =
      (((((5043949824267295894764006667 * 10 ^ 70 +
        2075934487985379415647175523787652969699324650935981183927929067742299) * 10 ^ 70 +
        4363971732710346333644838388696122126759962475428660215315188603509646) * 10 ^ 70 +
        5542871443238672830275386029194353670116223189695453010928959398059756) * 10 ^ 70 +
        0179287350643645836531823330330572404364325676198646175229461440513848) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (269 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (270 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (270 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_270 :
    recurrence4Scalar1Second.coeff 270 =
      -(((((3948464332002477847489380521 * 10 ^ 70 +
        4725168376004834592923135420481369480534123395321950185218587380896554) * 10 ^ 70 +
        2734863378840811609925890214521100575700898034882434198158840010560388) * 10 ^ 70 +
        2470594924076415897254752874763411732041591175866577312573985642817800) * 10 ^ 70 +
        9462262450712948144987617252124779301198745007944419794437658674665440) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (270 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (271 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (271 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_271 :
    recurrence4Scalar1Second.coeff 271 =
      (((((3006796262654175416152197987 * 10 ^ 70 +
        6398700962371940337210519252008130673526055952209390668499487698738174) * 10 ^ 70 +
        7365152195550911330628533970014894028556617602808597063829284830547087) * 10 ^ 70 +
        2891935586999504472547112050743940485825539215727892582826538914446651) * 10 ^ 70 +
        8770902295403423567003032074877438537483568245427761464114578933913049) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (271 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (272 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (272 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_272 :
    recurrence4Scalar1Second.coeff 272 =
      -(((((2220100626463256908091672159 * 10 ^ 70 +
        3894573944867544397546141816259704572516914837481477386054354280658389) * 10 ^ 70 +
        2633809371089218756919480105685030225848923721758281218239722730673053) * 10 ^ 70 +
        8914960920088349602201032110282555040795856383587206987809572127375150) * 10 ^ 70 +
        7324830693677797617237658556808493819331327970741765478511827779912657) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (272 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (273 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (273 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_273 :
    recurrence4Scalar1Second.coeff 273 =
      (((((1581716122237692058165650686 * 10 ^ 70 +
        0202018379919678531742152946764954206795388862961481205318955663370856) * 10 ^ 70 +
        4628575084053743258975565289169381411386557411316049933769022635193681) * 10 ^ 70 +
        5146732922423107802597401024004866465560080773327883483038912456793108) * 10 ^ 70 +
        7980600902755686449659484169929570398739711780875130566695742486777664) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (273 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (274 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (274 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_274 :
    recurrence4Scalar1Second.coeff 274 =
      -(((((1079170977070673868606239519 * 10 ^ 70 +
        8023059942992295739528043734875088341071855290872251603777068898931574) * 10 ^ 70 +
        9316023603218281511388089726595420119423996051922573221955061082184918) * 10 ^ 70 +
        5411467671610151033257648003082875088392350044548157118242707421430453) * 10 ^ 70 +
        1278536417440787390729190697871139611621571571164557504128678781552912) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (274 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (275 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (275 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_275 :
    recurrence4Scalar1Second.coeff 275 =
      (((((696215328960945082173334013 * 10 ^ 70 +
        3812319752888411838100978601497768502057939567010733056371069287226335) * 10 ^ 70 +
        1427069839051404434477656522331958154406390166205627995553398749203791) * 10 ^ 70 +
        1776254588913513361769698803892116033687259398364718123890196584599247) * 10 ^ 70 +
        8111587063975665019965615261310055699675693819238606329090810876368222) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (275 - x)) = _
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
  rw [recurrence4Scalar1Second_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
