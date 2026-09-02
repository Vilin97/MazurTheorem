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

private theorem recurrence4Scalar1Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (220 + x) *
        remainder4Coefficient1.coeff (220 - (220 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 220 + x
  · rw [recurrence4LeadingSquare_coeff_high (220 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (220 - (220 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_220 :
    recurrence4Scalar1Left.coeff 220 =
      (((((22665165613312500531640290 * 10 ^ 70 +
        7452893137472705705030300492664312689798351073091117860888714660016427) * 10 ^ 70 +
        2749651842766103644694349523468106527893821512121115637691039919641505) * 10 ^ 70 +
        4295936933322228814745132548489414952292651405348022668382401474412299) * 10 ^ 70 +
        0419284408416981514873421402396516156053219573008428931263581240088402) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (220 - x)) = _
  rw [show 221 = 30 +
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
  rw [recurrence4Scalar1Left_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (221 + x) *
        remainder4Coefficient1.coeff (221 - (221 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 221 + x
  · rw [recurrence4LeadingSquare_coeff_high (221 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (221 - (221 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_221 :
    recurrence4Scalar1Left.coeff 221 =
      -(((((34672673842289262721636449 * 10 ^ 70 +
        0292544470977788371719552443180174275903623430215594294035122732444020) * 10 ^ 70 +
        4084960229358266682217778583440781234383012366075677906846939260347345) * 10 ^ 70 +
        9199674844965606427163353935033057253886964382481590288978151634256420) * 10 ^ 70 +
        5715868559701875770778795245374794911342424718109457085645519725359770) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (221 - x)) = _
  rw [show 222 = 31 +
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
  rw [recurrence4Scalar1Left_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (222 + x) *
        remainder4Coefficient1.coeff (222 - (222 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 222 + x
  · rw [recurrence4LeadingSquare_coeff_high (222 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (222 - (222 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_222 :
    recurrence4Scalar1Left.coeff 222 =
      (((((52281889225162533322107181 * 10 ^ 70 +
        1271765626178948416587147704991530700591663404512220683262542935236595) * 10 ^ 70 +
        9740316414767108584239866627102477910935688397285682243607291540332132) * 10 ^ 70 +
        3034644495780990685166949811371742632860493371551710451105211146392335) * 10 ^ 70 +
        7724347502972492890627357921679285813699165152566550612646912723898910) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (222 - x)) = _
  rw [show 223 = 32 +
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
  rw [recurrence4Scalar1Left_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (223 + x) *
        remainder4Coefficient1.coeff (223 - (223 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 223 + x
  · rw [recurrence4LeadingSquare_coeff_high (223 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (223 - (223 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_223 :
    recurrence4Scalar1Left.coeff 223 =
      -(((((77701471394438519022330296 * 10 ^ 70 +
        9568070133251412116935743286714049174307213785315974892751041063825495) * 10 ^ 70 +
        6123985748522948147758038507099875502141715955212039310639124225847208) * 10 ^ 70 +
        3208435315655486209386968506221609602471753687017091272948212588770450) * 10 ^ 70 +
        2493453206560877532126728563880748918305166258009838929249177191499002) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (223 - x)) = _
  rw [show 224 = 33 +
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
  rw [recurrence4Scalar1Left_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (224 + x) *
        remainder4Coefficient1.coeff (224 - (224 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 224 + x
  · rw [recurrence4LeadingSquare_coeff_high (224 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (224 - (224 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_224 :
    recurrence4Scalar1Left.coeff 224 =
      (((((113814408323352876220922275 * 10 ^ 70 +
        1426815712408759138377827873466865816468137668254805960627499583711597) * 10 ^ 70 +
        8477938135978653260495543164112605836166850598694213739785230317506642) * 10 ^ 70 +
        6140578594475549809298910020810762154696153952773909394696925368406945) * 10 ^ 70 +
        8770907485576819916601017963908247177804901086105896755863375087934426) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (224 - x)) = _
  rw [show 225 = 34 +
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
  rw [recurrence4Scalar1Left_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (225 + x) *
        remainder4Coefficient1.coeff (225 - (225 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 225 + x
  · rw [recurrence4LeadingSquare_coeff_high (225 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (225 - (225 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_225 :
    recurrence4Scalar1Left.coeff 225 =
      -(((((164296565878985349334917833 * 10 ^ 70 +
        2140824760232090463885041957832657006930192164748815904953313221651779) * 10 ^ 70 +
        4266774218216044649352031667947753913890183354514458421238300526759965) * 10 ^ 70 +
        6513181077299351346375269060735210290283962440196655043486012548609291) * 10 ^ 70 +
        9133019611988046161991922700860628886216649732844393855409198638586180) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (225 - x)) = _
  rw [show 226 = 35 +
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
  rw [recurrence4Scalar1Left_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (226 + x) *
        remainder4Coefficient1.coeff (226 - (226 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 226 + x
  · rw [recurrence4LeadingSquare_coeff_high (226 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (226 - (226 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_226 :
    recurrence4Scalar1Left.coeff 226 =
      (((((233718493325319791910666174 * 10 ^ 70 +
        5945835181686849177377279636956946990991179417881231905870620519731668) * 10 ^ 70 +
        0606039673642295825949429171581176167394162271926464648398113925411458) * 10 ^ 70 +
        5633962713857016616891185551017533626613808480417041611675323094616087) * 10 ^ 70 +
        2225249865279834595040061601059933385735899094453384318802621968940801) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (226 - x)) = _
  rw [show 227 = 36 +
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
  rw [recurrence4Scalar1Left_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (227 + x) *
        remainder4Coefficient1.coeff (227 - (227 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 227 + x
  · rw [recurrence4LeadingSquare_coeff_high (227 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (227 - (227 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_227 :
    recurrence4Scalar1Left.coeff 227 =
      -(((((327610405988392242444207521 * 10 ^ 70 +
        7282034802839993568628925596208934704501713830007168392852068195891185) * 10 ^ 70 +
        2318239453057531789536047310596772563872791489614418506658113749905351) * 10 ^ 70 +
        5048507420134853326400060312399188991592818644619588742385314600036458) * 10 ^ 70 +
        0076609386830602767579625689447244776795058064678513141554122719593980) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (227 - x)) = _
  rw [show 228 = 37 +
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
  rw [recurrence4Scalar1Left_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (228 + x) *
        remainder4Coefficient1.coeff (228 - (228 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 228 + x
  · rw [recurrence4LeadingSquare_coeff_high (228 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (228 - (228 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_228 :
    recurrence4Scalar1Left.coeff 228 =
      (((((452465143319850015249378481 * 10 ^ 70 +
        1944804039275560197445790167932946495119975287194243085419824794084904) * 10 ^ 70 +
        3818027068067285643482073895645243108451140641674871192115867621272184) * 10 ^ 70 +
        5946716250845643599463767067139486300857969923067054297291790921220879) * 10 ^ 70 +
        8168051624574349468327016200888422777923127206140917591535066390900697) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (228 - x)) = _
  rw [show 229 = 38 +
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
  rw [recurrence4Scalar1Left_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (229 + x) *
        remainder4Coefficient1.coeff (229 - (229 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 229 + x
  · rw [recurrence4LeadingSquare_coeff_high (229 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (229 - (229 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_229 :
    recurrence4Scalar1Left.coeff 229 =
      -(((((615649988072041095160893519 * 10 ^ 70 +
        2298630553434790607307188609055687054174364539608985663537758665003688) * 10 ^ 70 +
        2636857320557259679819669748498019428021689516055019772532359022853594) * 10 ^ 70 +
        7059611795744013689400312106468501576963371937327646161901996287036169) * 10 ^ 70 +
        4985635854491821149979834949860106287013805121560632275244637498204405) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (229 - x)) = _
  rw [show 230 = 39 +
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
  rw [recurrence4Scalar1Left_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (230 + x) *
        remainder4Coefficient1.coeff (230 - (230 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 230 + x
  · rw [recurrence4LeadingSquare_coeff_high (230 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (230 - (230 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_230 :
    recurrence4Scalar1Left.coeff 230 =
      (((((825196745919642999623075881 * 10 ^ 70 +
        3622712122492337005322415548214009177237060910987226974768010754193223) * 10 ^ 70 +
        7870877362313045958395373375388294614902018774829276524950666499405966) * 10 ^ 70 +
        0673247916042413998132737632215297800984039009077285221769523733366735) * 10 ^ 70 +
        6218620317648894172314366458754396769362470045575871432804790624214646) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (230 - x)) = _
  rw [show 231 = 40 +
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
  rw [recurrence4Scalar1Left_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (231 + x) *
        remainder4Coefficient1.coeff (231 - (231 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 231 + x
  · rw [recurrence4LeadingSquare_coeff_high (231 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (231 - (231 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_231 :
    recurrence4Scalar1Left.coeff 231 =
      -(((((1089441779005643657583358826 * 10 ^ 70 +
        4791490667458665178365563803432162027387291456716802537664483385236473) * 10 ^ 70 +
        9437190983624843721745081277190642737981659968759458513553385342833932) * 10 ^ 70 +
        1739909317478174054622858887692977600484535929698514128068955116156977) * 10 ^ 70 +
        7460228135682486322462346320352789544867571004229977179282610002290214) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (231 - x)) = _
  rw [show 232 = 41 +
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
  rw [recurrence4Scalar1Left_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (232 + x) *
        remainder4Coefficient1.coeff (232 - (232 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 232 + x
  · rw [recurrence4LeadingSquare_coeff_high (232 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (232 - (232 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_232 :
    recurrence4Scalar1Left.coeff 232 =
      (((((1416495056742011769223485138 * 10 ^ 70 +
        0811047386059668752435434114676612870517059339695882496434796754507172) * 10 ^ 70 +
        8244555470245424829364361229243697390226235293387018654236283614587332) * 10 ^ 70 +
        5655932123268509964372857877536406816686977132172813720789809809453903) * 10 ^ 70 +
        8969279911757291242196029038082346847771333368987671847780090177737935) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (232 - x)) = _
  rw [show 233 = 42 +
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
  rw [recurrence4Scalar1Left_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (233 + x) *
        remainder4Coefficient1.coeff (233 - (233 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 233 + x
  · rw [recurrence4LeadingSquare_coeff_high (233 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (233 - (233 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_233 :
    recurrence4Scalar1Left.coeff 233 =
      -(((((1813530693773275660649375296 * 10 ^ 70 +
        5110132482015974360656063900846990348037129786511075188565234227889600) * 10 ^ 70 +
        4254443303718444922175179396056084089374750233522082813308775748199991) * 10 ^ 70 +
        0364576553552449457139534147684884025814456955355484044323572632456251) * 10 ^ 70 +
        0277257974777517926502570306440344159731336868887886850078091613429242) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (233 - x)) = _
  rw [show 234 = 43 +
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
  rw [recurrence4Scalar1Left_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (234 + x) *
        remainder4Coefficient1.coeff (234 - (234 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 234 + x
  · rw [recurrence4LeadingSquare_coeff_high (234 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (234 - (234 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_234 :
    recurrence4Scalar1Left.coeff 234 =
      (((((2285911190137228061560453745 * 10 ^ 70 +
        8265005363448339152013600763037790627007685517101197986237908187836319) * 10 ^ 70 +
        2684112026651209276729042845179916994357099184075144312595184067389498) * 10 ^ 70 +
        0743503754252896237405020683298572491508830730147741557878206432889770) * 10 ^ 70 +
        5256180989873979480405692234220104230138399500137260228522626899209503) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (234 - x)) = _
  rw [show 235 = 44 +
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
  rw [recurrence4Scalar1Left_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (235 + x) *
        remainder4Coefficient1.coeff (235 - (235 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 235 + x
  · rw [recurrence4LeadingSquare_coeff_high (235 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (235 - (235 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_235 :
    recurrence4Scalar1Left.coeff 235 =
      -(((((2836182990614060718226541039 * 10 ^ 70 +
        7441530584930820177296184435022248240580792606189885936942699827113105) * 10 ^ 70 +
        1416899202128441541190283923628848988722700561844034491705582412104584) * 10 ^ 70 +
        5750439070525419995029140567795726329917443518100951280567114520005418) * 10 ^ 70 +
        3354365920775600609542510041663303027840905476631360656423417120983101) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (235 - x)) = _
  rw [show 236 = 45 +
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
  rw [recurrence4Scalar1Left_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (236 + x) *
        remainder4Coefficient1.coeff (236 - (236 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 236 + x
  · rw [recurrence4LeadingSquare_coeff_high (236 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (236 - (236 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_236 :
    recurrence4Scalar1Left.coeff 236 =
      (((((3463010121751328725429549920 * 10 ^ 70 +
        1046175160846593467461122025550807035324074124011990870469329429172944) * 10 ^ 70 +
        4612709475438698367077539513594959589480319788557090687240867376433051) * 10 ^ 70 +
        6337616966173220089849486174145464753242855955374311202692966310564717) * 10 ^ 70 +
        4639219422009474789049924351127536417992213492645028948080614295882148) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (236 - x)) = _
  rw [show 237 = 46 +
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
  rw [recurrence4Scalar1Left_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (237 + x) *
        remainder4Coefficient1.coeff (237 - (237 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 237 + x
  · rw [recurrence4LeadingSquare_coeff_high (237 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (237 - (237 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_237 :
    recurrence4Scalar1Left.coeff 237 =
      -(((((4160142296704420700436302216 * 10 ^ 70 +
        1049020991258936056306691772672880285640667476491314985941790237609623) * 10 ^ 70 +
        7063604877620116762031030731760773886418298427398887045861589851202290) * 10 ^ 70 +
        7726828345997819202117563385934668096919744848625477681905775278932643) * 10 ^ 70 +
        0152959130266612848187336191664731610641344363362927689265779629536192) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (237 - x)) = _
  rw [show 238 = 47 +
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
  rw [recurrence4Scalar1Left_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (238 + x) *
        remainder4Coefficient1.coeff (238 - (238 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 238 + x
  · rw [recurrence4LeadingSquare_coeff_high (238 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (238 - (238 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_238 :
    recurrence4Scalar1Left.coeff 238 =
      (((((4915539556003682748898280443 * 10 ^ 70 +
        3382822868322110011194509250435099926959735044099523689496683152486001) * 10 ^ 70 +
        0813847558372354287251708586465451996683705134246825534808167575735999) * 10 ^ 70 +
        8602635088732793385448644421716537871121395007754055140862609175713830) * 10 ^ 70 +
        4452595489129709267680652467351833321969487699326601595489531624114623) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (238 - x)) = _
  rw [show 239 = 48 +
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
  rw [recurrence4Scalar1Left_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (239 + x) *
        remainder4Coefficient1.coeff (239 - (239 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 239 + x
  · rw [recurrence4LeadingSquare_coeff_high (239 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (239 - (239 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_239 :
    recurrence4Scalar1Left.coeff 239 =
      -(((((5710792023110972301926956388 * 10 ^ 70 +
        4190955707126695088400525328718611727643687882009627006189551468596270) * 10 ^ 70 +
        5598145003418292580422325890405943187617620960165784442309610020474170) * 10 ^ 70 +
        5722697261459094071616169338636434828122989640717274043898601039008565) * 10 ^ 70 +
        2458868301073747629683082675231499218782747582918329758534948906415621) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (239 - x)) = _
  rw [show 240 = 49 +
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
  rw [recurrence4Scalar1Left_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (240 + x) *
        remainder4Coefficient1.coeff (240 - (240 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 240 + x
  · rw [recurrence4LeadingSquare_coeff_high (240 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (240 - (240 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_240 :
    recurrence4Scalar1Left.coeff 240 =
      (((((6520975431002850371197773121 * 10 ^ 70 +
        5152466622145623911680743215769139851694501373813905910151603520911131) * 10 ^ 70 +
        9709816968725286353892455442166405156940002101117144097977005492782279) * 10 ^ 70 +
        0376012413736225465085331780206415773425493639332432018644122772390240) * 10 ^ 70 +
        8208668653351851719418204506351840497121418487248055446246084842950181) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (240 - x)) = _
  rw [show 241 = 50 +
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
  rw [recurrence4Scalar1Left_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (241 + x) *
        remainder4Coefficient1.coeff (241 - (241 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 241 + x
  · rw [recurrence4LeadingSquare_coeff_high (241 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (241 - (241 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_241 :
    recurrence4Scalar1Left.coeff 241 =
      -(((((7315066350757307238836761801 * 10 ^ 70 +
        9520432064651420990216227187877301256750126444690806369060045987295272) * 10 ^ 70 +
        0804578034463668561109427654360839384641113531075458495948576443108081) * 10 ^ 70 +
        5609589461263355097736630664851348805158420920362049395846324097424424) * 10 ^ 70 +
        9307878859623156869202621793775566323723227638915220588123965625635385) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (241 - x)) = _
  rw [show 242 = 51 +
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
  rw [recurrence4Scalar1Left_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (242 + x) *
        remainder4Coefficient1.coeff (242 - (242 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 242 + x
  · rw [recurrence4LeadingSquare_coeff_high (242 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (242 - (242 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_242 :
    recurrence4Scalar1Left.coeff 242 =
      (((((8057003103471475965886868913 * 10 ^ 70 +
        5976437449778574804965896832893105661807611207013135660918024977041750) * 10 ^ 70 +
        8862218096582763430660778137786944762309749226190347944273931419695444) * 10 ^ 70 +
        7244607120744610674270789849492517473526525358979771965198332893662140) * 10 ^ 70 +
        8296088544129503045680165608816047057671049623106476743151163457036817) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (242 - x)) = _
  rw [show 243 = 52 +
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
  rw [recurrence4Scalar1Left_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (243 + x) *
        remainder4Coefficient1.coeff (243 - (243 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 243 + x
  · rw [recurrence4LeadingSquare_coeff_high (243 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (243 - (243 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_243 :
    recurrence4Scalar1Left.coeff 243 =
      -(((((8707419647379254952476228598 * 10 ^ 70 +
        6055176852181496251306803225538808550778042528877593429682292652015620) * 10 ^ 70 +
        8565790765322754625370951729703861087558191391327138248189766133225712) * 10 ^ 70 +
        6769272430941415414630843943964480020377177816421182293301162059134687) * 10 ^ 70 +
        1222155995763456327056500739622438091419207128530133057694182480853522) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (243 - x)) = _
  rw [show 244 = 53 +
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
  rw [recurrence4Scalar1Left_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (244 + x) *
        remainder4Coefficient1.coeff (244 - (244 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 244 + x
  · rw [recurrence4LeadingSquare_coeff_high (244 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (244 - (244 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_244 :
    recurrence4Scalar1Left.coeff 244 =
      (((((9226004334886739480551615663 * 10 ^ 70 +
        2591422393211508703151598977691016586349618323731918226312267463592628) * 10 ^ 70 +
        1853079963547392562685114654348064849306825465027512111744280087643247) * 10 ^ 70 +
        3388121557085089083281946671391066671359057759095161716271414646870815) * 10 ^ 70 +
        3179740275310278145024770375412330167354117666193074058059273419833055) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (244 - x)) = _
  rw [show 245 = 54 +
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
  rw [recurrence4Scalar1Left_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (245 + x) *
        remainder4Coefficient1.coeff (245 - (245 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 245 + x
  · rw [recurrence4LeadingSquare_coeff_high (245 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (245 - (245 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_245 :
    recurrence4Scalar1Left.coeff 245 =
      -(((((9574351018572074293520434948 * 10 ^ 70 +
        9009594936515919696745964565798199974258571250809430544371686079968999) * 10 ^ 70 +
        5412020340300650703865976418134874651261816738442010849879964824274492) * 10 ^ 70 +
        9651677467128303060612201502296738850118156095437807093713594148977516) * 10 ^ 70 +
        5777458722668769561936724491846409679732588808865015042011337694587941) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (245 - x)) = _
  rw [show 246 = 55 +
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
  rw [recurrence4Scalar1Left_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
