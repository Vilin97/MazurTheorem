/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart1Simp
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
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1

attribute [local simp]
  recurrence4LeadingSquare_coeff_10
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
  recurrence4LeadingSquare_coeff_11
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
  recurrence4LeadingSquare_coeff_12
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
  recurrence4LeadingSquare_coeff_13
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
  recurrence4LeadingSquare_coeff_14
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
  recurrence4LeadingSquare_coeff_15
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157

attribute [local simp]
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_16
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168
  recurrence4LeadingSquare_coeff_169
  recurrence4LeadingSquare_coeff_17
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
  recurrence4LeadingSquare_coeff_18
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
  recurrence4LeadingSquare_coeff_19
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
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
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
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214

attribute [local simp]
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_22
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
  recurrence4LeadingSquare_coeff_23
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
  recurrence4LeadingSquare_coeff_24
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
  recurrence4LeadingSquare_coeff_25
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
  recurrence4LeadingSquare_coeff_26
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
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_270
  recurrence4LeadingSquare_coeff_28
  recurrence4LeadingSquare_coeff_29

attribute [local simp]
  recurrence4LeadingSquare_coeff_3
  recurrence4LeadingSquare_coeff_30
  recurrence4LeadingSquare_coeff_31
  recurrence4LeadingSquare_coeff_32
  recurrence4LeadingSquare_coeff_33
  recurrence4LeadingSquare_coeff_34
  recurrence4LeadingSquare_coeff_35
  recurrence4LeadingSquare_coeff_36
  recurrence4LeadingSquare_coeff_37
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_4
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_5
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_6
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69
  recurrence4LeadingSquare_coeff_7
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_8
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87

attribute [local simp]
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_9
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

private theorem recurrence4Scalar1Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (246 + x) *
        remainder4Coefficient1.coeff (246 - (246 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 246 + x
  · rw [recurrence4LeadingSquare_coeff_high (246 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (246 - (246 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_246 :
    recurrence4Scalar1Left.coeff 246 =
      (((((9719087326442950558228533302 * 10 ^ 70 +
        6589787323404326136174104684876222348361504102973813862242731138698878) * 10 ^ 70 +
        6406744565314147301648071654116580419039059883077068286747754522934568) * 10 ^ 70 +
        0073440188579454672369972597801907755895750374249058299762624644626311) * 10 ^ 70 +
        6124070852169662929664389758038934925096829825471931339347963183492091) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (246 - x)) = _
  rw [show 247 = 56 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (247 + x) *
        remainder4Coefficient1.coeff (247 - (247 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 247 + x
  · rw [recurrence4LeadingSquare_coeff_high (247 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (247 - (247 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_247 :
    recurrence4Scalar1Left.coeff 247 =
      -(((((9634996602866077532714534660 * 10 ^ 70 +
        5267139533126966537071205425565210125338713335201857264473390840153406) * 10 ^ 70 +
        3947258355707970722553833745279543310379194606758828844910486504204509) * 10 ^ 70 +
        2537591840077230145926626938760525444848151553999748978980194490049687) * 10 ^ 70 +
        5921259785127590234363481617480024540768725994661013837337872654698236) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (247 - x)) = _
  rw [show 248 = 57 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (248 + x) *
        remainder4Coefficient1.coeff (248 - (248 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 248 + x
  · rw [recurrence4LeadingSquare_coeff_high (248 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (248 - (248 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_248 :
    recurrence4Scalar1Left.coeff 248 =
      (((((9307808523144226131515577154 * 10 ^ 70 +
        5649505778907938966863767559715810252804382302350006580557633994119747) * 10 ^ 70 +
        4788417554644314355913921366891431295022429697580589478765437872318802) * 10 ^ 70 +
        6077450539152915596181664486747945860961781795746988423378863475037541) * 10 ^ 70 +
        6175256397872287130290747603121194918542443809453781657921229577690897) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (248 - x)) = _
  rw [show 249 = 58 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (249 + x) *
        remainder4Coefficient1.coeff (249 - (249 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 249 + x
  · rw [recurrence4LeadingSquare_coeff_high (249 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (249 - (249 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_249 :
    recurrence4Scalar1Left.coeff 249 =
      -(((((8736328953892618777356563721 * 10 ^ 70 +
        6238067337036506735869655601997002704221793711856729689923390040753833) * 10 ^ 70 +
        9869915958972138952715096722383629872556099846010259513268001999333415) * 10 ^ 70 +
        2014462718243004656945838747135230658830569191223119901922548682371696) * 10 ^ 70 +
        4442055081350312107873035716044065547610304266431845215928467591671815) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (249 - x)) = _
  rw [show 250 = 59 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (250 + x) *
        remainder4Coefficient1.coeff (250 - (250 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 250 + x
  · rw [recurrence4LeadingSquare_coeff_high (250 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (250 - (250 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_250 :
    recurrence4Scalar1Left.coeff 250 =
      (((((7933618040210027699333668721 * 10 ^ 70 +
        8075522651564127238691989941150947544634790731622267609810271649476933) * 10 ^ 70 +
        5888271902283696182590603865398115427554757641460525321802733955320291) * 10 ^ 70 +
        3783532743854801477892580926417117377193617649333217592558715127834294) * 10 ^ 70 +
        8685082008183215517963885405733570262822629643840292816511611556139083) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (250 - x)) = _
  rw [show 251 = 60 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (251 + x) *
        remainder4Coefficient1.coeff (251 - (251 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 251 + x
  · rw [recurrence4LeadingSquare_coeff_high (251 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (251 - (251 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_251 :
    recurrence4Scalar1Left.coeff 251 =
      -(((((6927006485844067499077555738 * 10 ^ 70 +
        3670945552187489121940778102263477564976756254139092009141412864456664) * 10 ^ 70 +
        0420404113153994001056989456326612771546264012553258124969360402897009) * 10 ^ 70 +
        9494038003476360264967765597739000960269252044042225576620842032155457) * 10 ^ 70 +
        6871271939208836707408937439899117360304388515146549402097480131965411) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (251 - x)) = _
  rw [show 252 = 61 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (252 + x) *
        remainder4Coefficient1.coeff (252 - (252 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 252 + x
  · rw [recurrence4LeadingSquare_coeff_high (252 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (252 - (252 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_252 :
    recurrence4Scalar1Left.coeff 252 =
      (((((5756856498159478080310862742 * 10 ^ 70 +
        7543541759099436637558456954522754928570442619928716839395544838265599) * 10 ^ 70 +
        1831498224524220623973394741889907765667399326156810641418164004610012) * 10 ^ 70 +
        7118430165560821796071418712602298929336812187700675270908479478373810) * 10 ^ 70 +
        5532200792004812209801897812391702411345497723221724927848214880682640) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (252 - x)) = _
  rw [show 253 = 62 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (253 + x) *
        remainder4Coefficient1.coeff (253 - (253 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 253 + x
  · rw [recurrence4LeadingSquare_coeff_high (253 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (253 - (253 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_253 :
    recurrence4Scalar1Left.coeff 253 =
      -(((((4474112496266397701996713678 * 10 ^ 70 +
        7791851918717842417967037380516367078945702608541309905981271114664692) * 10 ^ 70 +
        4188337643880820721714110707532663775704785332377292097845113883204251) * 10 ^ 70 +
        7629322432835036552469547508267233329990333515422570781035389170927942) * 10 ^ 70 +
        9318841293043741356878377871701766869706583508875269631891364243233960) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (253 - x)) = _
  rw [show 254 = 63 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (254 + x) *
        remainder4Coefficient1.coeff (254 - (254 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 254 + x
  · rw [recurrence4LeadingSquare_coeff_high (254 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (254 - (254 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_254 :
    recurrence4Scalar1Left.coeff 254 =
      (((((3136829348427769520657254701 * 10 ^ 70 +
        7460575219655912961616723825361012260932794612945604315403069803552592) * 10 ^ 70 +
        4000971698506462063741499823976873838835871876767857073925502622052110) * 10 ^ 70 +
        1704720678103511573318156467561193201297766971715726276103419373178223) * 10 ^ 70 +
        2384326379296277133908233965086663967125385218475821362851819600920291) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (254 - x)) = _
  rw [show 255 = 64 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (255 + x) *
        remainder4Coefficient1.coeff (255 - (255 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 255 + x
  · rw [recurrence4LeadingSquare_coeff_high (255 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (255 - (255 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_255 :
    recurrence4Scalar1Left.coeff 255 =
      -(((((1805992531907459880646408051 * 10 ^ 70 +
        1378541113181113314919039266947942816439793584770143362912270130442441) * 10 ^ 70 +
        7083732299116445151882022038896417151858713134033689678425853209224773) * 10 ^ 70 +
        6401799438134711786131943436201348417308812113381400922135084274610977) * 10 ^ 70 +
        8412276650537283713296875293453105130217786008900490910725836196561184) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (255 - x)) = _
  rw [show 256 = 65 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (256 + x) *
        remainder4Coefficient1.coeff (256 - (256 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 256 + x
  · rw [recurrence4LeadingSquare_coeff_high (256 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (256 - (256 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_256 :
    recurrence4Scalar1Left.coeff 256 =
      (((((541036366578576034310583309 * 10 ^ 70 +
        4925297556997894761055432049545984899600671106977482222303573856187130) * 10 ^ 70 +
        2666649359237018319381423465444736422222579577276223210266072600905183) * 10 ^ 70 +
        4684422495571062950007179796693163313355295936893253321557089878688233) * 10 ^ 70 +
        8283114609679712699955257554309051774291071548489586547313464668157775) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (256 - x)) = _
  rw [show 257 = 66 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (257 + x) *
        remainder4Coefficient1.coeff (257 - (257 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 257 + x
  · rw [recurrence4LeadingSquare_coeff_high (257 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (257 - (257 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_257 :
    recurrence4Scalar1Left.coeff 257 =
      (((((604490970864071608605352423 * 10 ^ 70 +
        5118704746486471947459957353477318600488786137540121650394066271915943) * 10 ^ 70 +
        6805431984186432270781622063686058041216584751171092081748523203267665) * 10 ^ 70 +
        7886925217983304624860430276261296561925900522472732799098993538797808) * 10 ^ 70 +
        9799634438398554895966590872567988917240021886119264525318004229901371) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (257 - x)) = _
  rw [show 258 = 67 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (258 + x) *
        remainder4Coefficient1.coeff (258 - (258 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 258 + x
  · rw [recurrence4LeadingSquare_coeff_high (258 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (258 - (258 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_258 :
    recurrence4Scalar1Left.coeff 258 =
      -(((((1586680836797053520714582298 * 10 ^ 70 +
        1181771622422485648467312444203179605178675087520037272664099903480924) * 10 ^ 70 +
        6513330748328245425679444428575843575593921597357443526169361584997080) * 10 ^ 70 +
        7596402529393918124462238391473073870190180187636260612059908008326388) * 10 ^ 70 +
        9287632713379171453637695518743939904439839035432398509736452192998713) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (258 - x)) = _
  rw [show 259 = 68 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (259 + x) *
        remainder4Coefficient1.coeff (259 - (259 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 259 + x
  · rw [recurrence4LeadingSquare_coeff_high (259 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (259 - (259 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_259 :
    recurrence4Scalar1Left.coeff 259 =
      (((((2374070175360243059399651697 * 10 ^ 70 +
        1223868900887043581883110307086785931313785772241191578689209206811929) * 10 ^ 70 +
        9828421757374502821979276929319939208230953965472172467824740021059190) * 10 ^ 70 +
        7504460624568642565908757768401636126573335047635678034364843291257111) * 10 ^ 70 +
        0225517292201114885826160022261180745006244178278691285004332593595950) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (259 - x)) = _
  rw [show 260 = 69 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (260 + x) *
        remainder4Coefficient1.coeff (260 - (260 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 260 + x
  · rw [recurrence4LeadingSquare_coeff_high (260 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (260 - (260 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_260 :
    recurrence4Scalar1Left.coeff 260 =
      -(((((2949249059872805588854129842 * 10 ^ 70 +
        1922338246337094916945350284852356916797634701209351346911592014455409) * 10 ^ 70 +
        1814964674181483434247470213909425619137384395529126602890756998144180) * 10 ^ 70 +
        4495431946067174211675041431879166360956119946029549326079200672736364) * 10 ^ 70 +
        9655670284996585047745891237283281518036400734253940764226561011736007) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (260 - x)) = _
  rw [show 261 = 70 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (261 + x) *
        remainder4Coefficient1.coeff (261 - (261 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 261 + x
  · rw [recurrence4LeadingSquare_coeff_high (261 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (261 - (261 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_261 :
    recurrence4Scalar1Left.coeff 261 =
      (((((3309162028234923841189522528 * 10 ^ 70 +
        5495066075840522302971643728961779269496999275555087009959625999882305) * 10 ^ 70 +
        3461832015689901105224031396650670800039133859210835576795921495450653) * 10 ^ 70 +
        4917634941172765224169622141419756175822614122977866396049025229402171) * 10 ^ 70 +
        8056583828493648659440119790565116107981355636251570020540819233276045) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (261 - x)) = _
  rw [show 262 = 71 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (262 + x) *
        remainder4Coefficient1.coeff (262 - (262 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 262 + x
  · rw [recurrence4LeadingSquare_coeff_high (262 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (262 - (262 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_262 :
    recurrence4Scalar1Left.coeff 262 =
      -(((((3464147294611502928550534691 * 10 ^ 70 +
        3212038989379478256823539323597946177001021441801013891470305649510576) * 10 ^ 70 +
        4140976021295187694392710453732732113896779730186852058548848031311982) * 10 ^ 70 +
        9644196543065535604596096403092772991152786890214837026228093087959733) * 10 ^ 70 +
        5900641183320379131521043156824832917555416929777164271848024258370112) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (262 - x)) = _
  rw [show 263 = 72 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (263 + x) *
        remainder4Coefficient1.coeff (263 - (263 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 263 + x
  · rw [recurrence4LeadingSquare_coeff_high (263 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (263 - (263 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_263 :
    recurrence4Scalar1Left.coeff 263 =
      (((((3435896743722092576699822692 * 10 ^ 70 +
        4874381345018449957159769298514501139722413345980655689126030248640244) * 10 ^ 70 +
        6322435710161061148260724982420658380148550617997558728936658147546323) * 10 ^ 70 +
        2804878761260167395599789854066531232216143074631042717653148049925777) * 10 ^ 70 +
        1574605642781189900389196917047833706690671839445864016767646107706412) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (263 - x)) = _
  rw [show 264 = 73 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (264 + x) *
        remainder4Coefficient1.coeff (264 - (264 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 264 + x
  · rw [recurrence4LeadingSquare_coeff_high (264 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (264 - (264 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_264 :
    recurrence4Scalar1Left.coeff 264 =
      -(((((3254627119080472140953501394 * 10 ^ 70 +
        6835263084512342073791449499003023786048822707107209629564331611800638) * 10 ^ 70 +
        0065935875862900435352040498243550979177891398717327320195731272192281) * 10 ^ 70 +
        8332011526277798634416213453130963242960982944770731446665148860686167) * 10 ^ 70 +
        8074978489818245937707110212787300416804235543868339091963826364100891) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (264 - x)) = _
  rw [show 265 = 74 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (265 + x) *
        remainder4Coefficient1.coeff (265 - (265 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 265 + x
  · rw [recurrence4LeadingSquare_coeff_high (265 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (265 - (265 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_265 :
    recurrence4Scalar1Left.coeff 265 =
      (((((2955816345700090159822779913 * 10 ^ 70 +
        9323463551720500986780480543344711373153425037542952090977903866309391) * 10 ^ 70 +
        8502463321585417432925038575629364783295618190263312874390580418289622) * 10 ^ 70 +
        9742162592146316325312714203927760934785674367748335702448993352251615) * 10 ^ 70 +
        3914199659862565434742793855418746087617410041391643314435255408377914) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (265 - x)) = _
  rw [show 266 = 75 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (266 + x) *
        remainder4Coefficient1.coeff (266 - (266 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 266 + x
  · rw [recurrence4LeadingSquare_coeff_high (266 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (266 - (266 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_266 :
    recurrence4Scalar1Left.coeff 266 =
      -(((((2576873232289360510631625789 * 10 ^ 70 +
        7964430774688375858116968248778220997238544105727288286132663059779535) * 10 ^ 70 +
        8617820164626329222441504276030776168998712188922849586408408026299282) * 10 ^ 70 +
        7193398376715435018032947623385200473027485730277242620586810675000138) * 10 ^ 70 +
        6332624753984012204004501977512870755520943495288566336898590905426579) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (266 - x)) = _
  rw [show 267 = 76 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (267 + x) *
        remainder4Coefficient1.coeff (267 - (267 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 267 + x
  · rw [recurrence4LeadingSquare_coeff_high (267 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (267 - (267 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_267 :
    recurrence4Scalar1Left.coeff 267 =
      (((((2154076342018371345042222019 * 10 ^ 70 +
        6526783476919404825749304446591595145323419183336420620808581632068033) * 10 ^ 70 +
        1809275756767208563992825875007513365047890095346040617055586772947330) * 10 ^ 70 +
        9432781046244196997108075980661907051086645296816098049749159923903028) * 10 ^ 70 +
        5371257929221378132996534696267629939521220561769716949345163288689228) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (267 - x)) = _
  rw [show 268 = 77 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (268 + x) *
        remainder4Coefficient1.coeff (268 - (268 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 268 + x
  · rw [recurrence4LeadingSquare_coeff_high (268 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (268 - (268 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_268 :
    recurrence4Scalar1Left.coeff 268 =
      -(((((1720047734557428837083072656 * 10 ^ 70 +
        9830981548104226022505837348132070650130019696009235002753420329900172) * 10 ^ 70 +
        9784547553267853538184181221228080411869315560716825042856700850379194) * 10 ^ 70 +
        5427825224353713519208717944330109215853213200461879653305109559821361) * 10 ^ 70 +
        1998328271444855841707090843592475765755871657520988808771480595363404) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (268 - x)) = _
  rw [show 269 = 78 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (269 + x) *
        remainder4Coefficient1.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 269 + x
  · rw [recurrence4LeadingSquare_coeff_high (269 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (269 - (269 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_269 :
    recurrence4Scalar1Left.coeff 269 =
      (((((1301933263640915454046416562 * 10 ^ 70 +
        1047765517288697629922192428361121009171910745415604408111396462056079) * 10 ^ 70 +
        1650049774484133381600892861410014899407282923006876974869457869387360) * 10 ^ 70 +
        6730468170955694546646052992320668255169034566112229168654302315383417) * 10 ^ 70 +
        6045311848026358311869646845904133507688561111154883678175115199845418) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (269 - x)) = _
  rw [show 270 = 79 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (270 + x) *
        remainder4Coefficient1.coeff (270 - (270 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 270 + x
  · rw [recurrence4LeadingSquare_coeff_high (270 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (270 - (270 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_270 :
    recurrence4Scalar1Left.coeff 270 =
      -(((((920358764350887398259341869 * 10 ^ 70 +
        5063340318057849730090473893284667107205107962256002815983684742864199) * 10 ^ 70 +
        1587710836110412952142533190566810286516054200790266650205383145158984) * 10 ^ 70 +
        4309923243996374311601742843224472833495944163407112403674152994229249) * 10 ^ 70 +
        9712774156468948091606606211657018095719445920626592571381410684473132) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (270 - x)) = _
  rw [show 271 = 80 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (271 + x) *
        remainder4Coefficient1.coeff (271 - (271 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 271 + x
  · rw [recurrence4LeadingSquare_coeff_high (271 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (271 - (271 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_271 :
    recurrence4Scalar1Left.coeff 271 =
      (((((589135595178670083182027202 * 10 ^ 70 +
        6732462447171459339575856492477783970101177568330814336564975926662045) * 10 ^ 70 +
        8999398474510218759175567444756595095746123673145659372678521274616432) * 10 ^ 70 +
        7424100551177898165927566746125474827138892748727656463330358450024849) * 10 ^ 70 +
        1918321316201057021928986953950284358376585381012710213029816198900085) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (271 - x)) = _
  rw [show 272 = 81 +
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
