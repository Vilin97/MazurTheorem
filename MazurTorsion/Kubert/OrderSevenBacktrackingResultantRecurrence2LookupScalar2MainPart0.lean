/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B2_coeff_0
  recurrence2B2_coeff_1
  recurrence2B2_coeff_2
  recurrence2B2_coeff_3
  recurrence2B2_coeff_4
  recurrence2B2_coeff_5
  recurrence2B2_coeff_6
  recurrence2B2_coeff_7
  recurrence2B2_coeff_8
  recurrence2B2_coeff_9
  recurrence2B2_coeff_10
  recurrence2B2_coeff_11
  recurrence2B2_coeff_12
  recurrence2B2_coeff_13
  recurrence2B2_coeff_14
  recurrence2B2_coeff_15
  recurrence2B2_coeff_16
  recurrence2B2_coeff_17
  recurrence2B2_coeff_18
  recurrence2B2_coeff_19
  recurrence2B2_coeff_20
  recurrence2B2_coeff_21
  recurrence2B2_coeff_22
  recurrence2B2_coeff_23
  recurrence2B2_coeff_24
  recurrence2B2_coeff_25
  recurrence2B2_coeff_26
  recurrence2B2_coeff_27
  recurrence2B2_coeff_28
  recurrence2B2_coeff_29
  recurrence2B2_coeff_30
  recurrence2B2_coeff_31
  recurrence2B2_coeff_32
  recurrence2B2_coeff_33
  recurrence2B2_coeff_34
  recurrence2B2_coeff_35
  recurrence2B2_coeff_36
  recurrence2B2_coeff_37
  recurrence2B2_coeff_38
  recurrence2B2_coeff_39
  recurrence2B2_coeff_40
  recurrence2B2_coeff_41
  recurrence2B2_coeff_42
  recurrence2B2_coeff_43
  recurrence2B2_coeff_44
  recurrence2B2_coeff_45
  recurrence2B2_coeff_46
  recurrence2B2_coeff_47
  recurrence2B2_coeff_48
  recurrence2B2_coeff_49
  recurrence2B2_coeff_50
  recurrence2B2_coeff_51
  recurrence2B2_coeff_52
  recurrence2B2_coeff_53
  recurrence2B2_coeff_54
  recurrence2B2_coeff_55
  recurrence2B2_coeff_56
  recurrence2B2_coeff_57
  recurrence2B2_coeff_58
  recurrence2B2_coeff_59
  recurrence2B2_coeff_60
  recurrence2B2_coeff_61
  recurrence2B2_coeff_62
  recurrence2B2_coeff_63
  recurrence2B2_coeff_64
  recurrence2B2_coeff_65
  recurrence2B2_coeff_66
  recurrence2B2_coeff_67
  recurrence2B2_coeff_68
  recurrence2B2_coeff_69
  recurrence2B2_coeff_70
  recurrence2B2_coeff_71
  recurrence2B2_coeff_72
  recurrence2B2_coeff_73
  recurrence2B2_coeff_74
  recurrence2B2_coeff_75
  recurrence2B2_coeff_76
  recurrence2B2_coeff_77
  recurrence2B2_coeff_78
  recurrence2B2_coeff_79
  recurrence2B2_coeff_80
  recurrence2B2_coeff_81
  recurrence2B2_coeff_82
  recurrence2B2_coeff_83
  recurrence2B2_coeff_84
  recurrence2B2_coeff_85
  recurrence2B2_coeff_86
  recurrence2B2_coeff_87
  recurrence2B2_coeff_88
  recurrence2B2_coeff_89
  recurrence2B2_coeff_90
  recurrence2B2_coeff_91
  recurrence2B2_coeff_92
  recurrence2B2_coeff_93
  recurrence2B2_coeff_94
  recurrence2B2_coeff_95
  recurrence2B2_coeff_96
  recurrence2B2_coeff_97
  recurrence2B2_coeff_98
  recurrence2B2_coeff_99
  recurrence2B2_coeff_100
  recurrence2B2_coeff_101
  recurrence2B2_coeff_102
  recurrence2B2_coeff_103
  recurrence2B2_coeff_104
  recurrence2B2_coeff_105
  recurrence2B2_coeff_106
  recurrence2B2_coeff_107
  recurrence2B2_coeff_108
  recurrence2B2_coeff_109
  recurrence2B2_coeff_110
  recurrence2B2_coeff_111
  recurrence2B2_coeff_112
  recurrence2B2_coeff_113
  recurrence2B2_coeff_114
  recurrence2B2_coeff_115
  recurrence2B2_coeff_116
  recurrence2B2_coeff_117
  recurrence2B2_coeff_118
  recurrence2B2_coeff_119
  recurrence2B2_coeff_120
  recurrence2B2_coeff_121
  recurrence2B2_coeff_122
  recurrence2B2_coeff_123
  recurrence2B2_coeff_124
  recurrence2B2_coeff_125
  recurrence2B2_coeff_126
  recurrence2B2_coeff_127
  recurrence2B2_coeff_128
  recurrence2B2_coeff_129
  recurrence2B2_coeff_130
  recurrence2B2_coeff_131
  recurrence2B2_coeff_132
  recurrence2B2_coeff_133
  recurrence2B2_coeff_134
  recurrence2B2_coeff_135
  recurrence2B2_coeff_136
  recurrence2B2_coeff_137
  recurrence2B2_coeff_138
  recurrence2B2_coeff_139
  recurrence2B2_coeff_140
  recurrence2B2_coeff_141
  recurrence2B2_coeff_142
  recurrence2B2_coeff_143
  recurrence2B2_coeff_144
  recurrence2B2_coeff_145
  recurrence2B2_coeff_146
  recurrence2QuotientConstant_coeff_0
  recurrence2QuotientConstant_coeff_1
  recurrence2QuotientConstant_coeff_2
  recurrence2QuotientConstant_coeff_3
  recurrence2QuotientConstant_coeff_4
  recurrence2QuotientConstant_coeff_5
  recurrence2QuotientConstant_coeff_6
  recurrence2QuotientConstant_coeff_7
  recurrence2QuotientConstant_coeff_8
  recurrence2QuotientConstant_coeff_9
  recurrence2QuotientConstant_coeff_10
  recurrence2QuotientConstant_coeff_11
  recurrence2QuotientConstant_coeff_12
  recurrence2QuotientConstant_coeff_13
  recurrence2QuotientConstant_coeff_14
  recurrence2QuotientConstant_coeff_15
  recurrence2QuotientConstant_coeff_16
  recurrence2QuotientConstant_coeff_17
  recurrence2QuotientConstant_coeff_18
  recurrence2QuotientConstant_coeff_19
  recurrence2QuotientConstant_coeff_20
  recurrence2QuotientConstant_coeff_21
  recurrence2QuotientConstant_coeff_22
  recurrence2QuotientConstant_coeff_23
  recurrence2QuotientConstant_coeff_24
  recurrence2QuotientConstant_coeff_25
  recurrence2QuotientConstant_coeff_26
  recurrence2QuotientConstant_coeff_27
  recurrence2QuotientConstant_coeff_28
  recurrence2QuotientConstant_coeff_29
  recurrence2QuotientConstant_coeff_30
  recurrence2QuotientConstant_coeff_31
  recurrence2QuotientConstant_coeff_32
  recurrence2QuotientConstant_coeff_33
  recurrence2QuotientConstant_coeff_34
  recurrence2QuotientConstant_coeff_35
  recurrence2QuotientConstant_coeff_36
  recurrence2QuotientConstant_coeff_37
  recurrence2QuotientConstant_coeff_38
  recurrence2QuotientConstant_coeff_39
  recurrence2QuotientConstant_coeff_40
  recurrence2QuotientConstant_coeff_41
  recurrence2QuotientConstant_coeff_42
  recurrence2QuotientConstant_coeff_43
  recurrence2QuotientConstant_coeff_44
  recurrence2QuotientConstant_coeff_45
  recurrence2QuotientConstant_coeff_46
  recurrence2QuotientConstant_coeff_47
  recurrence2QuotientConstant_coeff_48
  recurrence2QuotientConstant_coeff_49
  recurrence2QuotientConstant_coeff_50
  recurrence2QuotientConstant_coeff_51
  recurrence2QuotientConstant_coeff_52
  recurrence2QuotientConstant_coeff_53
  recurrence2QuotientConstant_coeff_54
  recurrence2QuotientConstant_coeff_55
  recurrence2QuotientConstant_coeff_56
  recurrence2QuotientConstant_coeff_57
  recurrence2QuotientConstant_coeff_58
  recurrence2QuotientConstant_coeff_59
  recurrence2QuotientConstant_coeff_60
  recurrence2QuotientConstant_coeff_61
  recurrence2QuotientConstant_coeff_62
  recurrence2QuotientConstant_coeff_63
  recurrence2QuotientConstant_coeff_64
  recurrence2QuotientConstant_coeff_65
  recurrence2QuotientConstant_coeff_66
  recurrence2QuotientConstant_coeff_67
  recurrence2QuotientConstant_coeff_68
  recurrence2QuotientConstant_coeff_69
  recurrence2QuotientConstant_coeff_70
  recurrence2QuotientConstant_coeff_71
  recurrence2QuotientConstant_coeff_72
  recurrence2QuotientConstant_coeff_73
  recurrence2QuotientConstant_coeff_74
  recurrence2QuotientConstant_coeff_75
  recurrence2QuotientConstant_coeff_76
  recurrence2QuotientConstant_coeff_77
  recurrence2QuotientConstant_coeff_78
  recurrence2QuotientConstant_coeff_79
  recurrence2QuotientConstant_coeff_80
  recurrence2QuotientConstant_coeff_81
  recurrence2QuotientConstant_coeff_82
  recurrence2QuotientConstant_coeff_83
  recurrence2QuotientConstant_coeff_84
  recurrence2QuotientConstant_coeff_85
  recurrence2QuotientConstant_coeff_86
  recurrence2QuotientConstant_coeff_87
  recurrence2QuotientConstant_coeff_88
  recurrence2QuotientConstant_coeff_89
  recurrence2QuotientConstant_coeff_90
  recurrence2QuotientConstant_coeff_91
  recurrence2QuotientConstant_coeff_92
  recurrence2QuotientConstant_coeff_93
  recurrence2QuotientConstant_coeff_94
  recurrence2QuotientConstant_coeff_95
  recurrence2QuotientConstant_coeff_96
  recurrence2QuotientConstant_coeff_97
  recurrence2QuotientConstant_coeff_98
  recurrence2QuotientConstant_coeff_99
  recurrence2QuotientConstant_coeff_100
  recurrence2QuotientConstant_coeff_101
  recurrence2QuotientConstant_coeff_102
  recurrence2QuotientConstant_coeff_103
  recurrence2QuotientConstant_coeff_104
  recurrence2QuotientConstant_coeff_105
  recurrence2QuotientConstant_coeff_106
  recurrence2QuotientConstant_coeff_107
  recurrence2QuotientConstant_coeff_108
  recurrence2QuotientConstant_coeff_109
  recurrence2QuotientConstant_coeff_110
  recurrence2QuotientConstant_coeff_111
  recurrence2QuotientConstant_coeff_112
  recurrence2QuotientConstant_coeff_113
  recurrence2QuotientConstant_coeff_114
  recurrence2QuotientConstant_coeff_115
  recurrence2QuotientConstant_coeff_116
  recurrence2QuotientConstant_coeff_117
  recurrence2QuotientConstant_coeff_118
  recurrence2QuotientConstant_coeff_119
  recurrence2QuotientConstant_coeff_120
  recurrence2QuotientConstant_coeff_121
  recurrence2QuotientConstant_coeff_122
  recurrence2QuotientConstant_coeff_123
  recurrence2QuotientConstant_coeff_124
  recurrence2QuotientConstant_coeff_125
  recurrence2QuotientConstant_coeff_126
  recurrence2QuotientConstant_coeff_127
  recurrence2QuotientConstant_coeff_128
  recurrence2QuotientConstant_coeff_129
  recurrence2QuotientConstant_coeff_130
  recurrence2QuotientConstant_coeff_131
  recurrence2QuotientConstant_coeff_132
  recurrence2QuotientConstant_coeff_133
  recurrence2QuotientConstant_coeff_134
  recurrence2QuotientConstant_coeff_135
  recurrence2QuotientConstant_coeff_136
  recurrence2QuotientConstant_coeff_137
  recurrence2QuotientConstant_coeff_138
  recurrence2QuotientConstant_coeff_139
  recurrence2QuotientConstant_coeff_140
  recurrence2QuotientConstant_coeff_141
  recurrence2QuotientConstant_coeff_142
  recurrence2QuotientConstant_coeff_143
  recurrence2QuotientConstant_coeff_144
  recurrence2QuotientConstant_coeff_145
  recurrence2QuotientConstant_coeff_146
  recurrence2QuotientConstant_coeff_147
  recurrence2QuotientConstant_coeff_148
  recurrence2QuotientConstant_coeff_149
  recurrence2QuotientConstant_coeff_150
  recurrence2QuotientConstant_coeff_151
  recurrence2QuotientConstant_coeff_152
  recurrence2QuotientConstant_coeff_153
  recurrence2QuotientConstant_coeff_154
  recurrence2QuotientConstant_coeff_155
  recurrence2QuotientConstant_coeff_156
  recurrence2QuotientConstant_coeff_157
  recurrence2QuotientConstant_coeff_158
  recurrence2QuotientConstant_coeff_159
  recurrence2QuotientConstant_coeff_160
  recurrence2QuotientConstant_coeff_161
  recurrence2QuotientConstant_coeff_162
  recurrence2QuotientConstant_coeff_163
  recurrence2QuotientConstant_coeff_164
  recurrence2QuotientConstant_coeff_165
  recurrence2QuotientConstant_coeff_166
  recurrence2QuotientConstant_coeff_167
  recurrence2QuotientConstant_coeff_168
  recurrence2QuotientConstant_coeff_169
  recurrence2QuotientConstant_coeff_170
  recurrence2QuotientConstant_coeff_171
  recurrence2QuotientConstant_coeff_172
  recurrence2QuotientConstant_coeff_173
  recurrence2QuotientConstant_coeff_174
  recurrence2QuotientConstant_coeff_175
  recurrence2QuotientConstant_coeff_176
  recurrence2QuotientConstant_coeff_177
  recurrence2QuotientConstant_coeff_178
  recurrence2QuotientConstant_coeff_179
  recurrence2QuotientConstant_coeff_180
  recurrence2QuotientConstant_coeff_181
  recurrence2QuotientConstant_coeff_182
  recurrence2QuotientConstant_coeff_183
  recurrence2QuotientConstant_coeff_184
  recurrence2QuotientConstant_coeff_185
  recurrence2QuotientConstant_coeff_186
  recurrence2QuotientConstant_coeff_187
  recurrence2QuotientConstant_coeff_188
  recurrence2QuotientConstant_coeff_189
  recurrence2QuotientConstant_coeff_190
  recurrence2QuotientConstant_coeff_191
  recurrence2QuotientConstant_coeff_192
  recurrence2QuotientConstant_coeff_193
  recurrence2QuotientConstant_coeff_194
  recurrence2QuotientConstant_coeff_195
  recurrence2QuotientConstant_coeff_196
  recurrence2QuotientConstant_coeff_197
  recurrence2QuotientConstant_coeff_198
  recurrence2QuotientConstant_coeff_199
  recurrence2QuotientConstant_coeff_200
  recurrence2QuotientConstant_coeff_201
  recurrence2QuotientConstant_coeff_202
  recurrence2QuotientConstant_coeff_203
  recurrence2QuotientConstant_coeff_204
  recurrence2QuotientConstant_coeff_205
  recurrence2QuotientConstant_coeff_206
  recurrence2QuotientConstant_coeff_207
  recurrence2QuotientConstant_coeff_208
  recurrence2QuotientConstant_coeff_209
  recurrence2QuotientConstant_coeff_210
  recurrence2QuotientConstant_coeff_211
  recurrence2QuotientConstant_coeff_212
  recurrence2QuotientConstant_coeff_213
  recurrence2QuotientConstant_coeff_214
  recurrence2QuotientConstant_coeff_215
  recurrence2QuotientConstant_coeff_216
  recurrence2QuotientConstant_coeff_217
  recurrence2QuotientConstant_coeff_218
  recurrence2QuotientConstant_coeff_219
  recurrence2QuotientConstant_coeff_220
  recurrence2QuotientConstant_coeff_221
  recurrence2QuotientConstant_coeff_222
  recurrence2QuotientConstant_coeff_223
  recurrence2QuotientConstant_coeff_224
  recurrence2QuotientConstant_coeff_225
  recurrence2QuotientConstant_coeff_226
  recurrence2QuotientConstant_coeff_227
  recurrence2QuotientConstant_coeff_228
  recurrence2QuotientConstant_coeff_229
  recurrence2QuotientConstant_coeff_230
  recurrence2QuotientConstant_coeff_231
  recurrence2QuotientConstant_coeff_232
  recurrence2QuotientConstant_coeff_233

theorem recurrence2Scalar2Main_coeff_0 :
    recurrence2Scalar2Main.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_1 :
    recurrence2Scalar2Main.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_2 :
    recurrence2Scalar2Main.coeff 2 =
      (-10529792 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_3 :
    recurrence2Scalar2Main.coeff 3 =
      (-249451191520 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_4 :
    recurrence2Scalar2Main.coeff 4 =
      (745610070910752 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_5 :
    recurrence2Scalar2Main.coeff 5 =
      (18895545486795579744 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_6 :
    recurrence2Scalar2Main.coeff 6 =
      (-16247831568543708403912 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_7 :
    recurrence2Scalar2Main.coeff 7 =
      (45147908737249219912255528 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_8 :
    recurrence2Scalar2Main.coeff 8 =
      (-29881411614576144932874912544 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_9 :
    recurrence2Scalar2Main.coeff 9 =
      (21036587864633413436809175746236 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_10 :
    recurrence2Scalar2Main.coeff 10 =
      (-6002817724092867864637372919007692 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_11 :
    recurrence2Scalar2Main.coeff 11 =
      (-4316427893016067443990366817624917370 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_12 :
    recurrence2Scalar2Main.coeff 12 =
      (4782439040182593299811115397371955369794 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_13 :
    recurrence2Scalar2Main.coeff 13 =
      (-2634240198427590708026373961562366667290616 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_14 :
    recurrence2Scalar2Main.coeff 14 =
      (963488150141891600719593185234919082422477549 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_15 :
    recurrence2Scalar2Main.coeff 15 =
      (-261585862998558353121181385247173898276512307196 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_16 :
    recurrence2Scalar2Main.coeff 16 =
      (54438546624135816636624793729937392916954216556316 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_17 :
    recurrence2Scalar2Main.coeff 17 =
      (-8833153023304696005193727029010782602235134241325529 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_18 :
    recurrence2Scalar2Main.coeff 18 =
      (1127075097054613870561944644319646704737900636008910474 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_19 :
    recurrence2Scalar2Main.coeff 19 =
      (-112885466578084577363966093354627702159691595773685105427 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_20 :
    recurrence2Scalar2Main.coeff 20 =
      (8731392712770797236723341668506883340613868779290813839428 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_21 :
    recurrence2Scalar2Main.coeff 21 =
      (-495128167052774291706026717762963908054546515359309518555021 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_22 :
    recurrence2Scalar2Main.coeff 22 =
      (16996371698066759565926509302512668102378744164343071152366464 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_23 :
    recurrence2Scalar2Main.coeff 23 =
      (109270296715914058061385254480150249356908911629060523907131688 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_24 :
    recurrence2Scalar2Main.coeff 24 =
      (-63413912007431996174765286589417293195350626275367711071047071256 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_25 :
    recurrence2Scalar2Main.coeff 25 =
      (5083118210859125669707853236180718162473890368157220742806365938108 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_26 :
    recurrence2Scalar2Main.coeff 26 =
      (-245233203302910639028440558533268675801251289976564788004498730220079 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_27 :
    recurrence2Scalar2Main.coeff 27 =
      (6343495224909179541938764095592845677067182896021559360316294128803366 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_28 :
    recurrence2Scalar2Main.coeff 28 =
      ((13 * 10 ^ 70 +
        4068275893168603208737233333403224867640002980955806703317201020213606) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_29 :
    recurrence2Scalar2Main.coeff 29 =
      -((2719 * 10 ^ 70 +
        8667256190890545443741881899134369867632940868449333820635423180704879) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_30 :
    recurrence2Scalar2Main.coeff 30 =
      ((184137 * 10 ^ 70 +
        9751910405027851850498751860171534823959024003151357816772278718596587) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_31 :
    recurrence2Scalar2Main.coeff 31 =
      -((8336343 * 10 ^ 70 +
        0453408801553223278525769443367244573566929621250794409599799948924478) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_32 :
    recurrence2Scalar2Main.coeff 32 =
      ((280728318 * 10 ^ 70 +
        8387134589452884913236825768212806000496283809377266511148575584116282) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_33 :
    recurrence2Scalar2Main.coeff 33 =
      -((7975284362 * 10 ^ 70 +
        1440949358006030346380198047678621048431123942741621490987197646930776) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_34 :
    recurrence2Scalar2Main.coeff 34 =
      ((277170502011 * 10 ^ 70 +
        8889877757841620788874087372829740032924378727179948434475579091469612) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_35 :
    recurrence2Scalar2Main.coeff 35 =
      -((14648385752413 * 10 ^ 70 +
        3171144706645943355692431329821803580862733598008653458906907196728948) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_36 :
    recurrence2Scalar2Main.coeff 36 =
      ((804802344381640 * 10 ^ 70 +
        2626619381308034924172865713892488675936909852887107508246898408855705) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_37 :
    recurrence2Scalar2Main.coeff 37 =
      -((36188863824673420 * 10 ^ 70 +
        5511878677225010211219681242825584975137333126992304438179799194174266) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_38 :
    recurrence2Scalar2Main.coeff 38 =
      ((1278341751679400674 * 10 ^ 70 +
        8953439766896298503628875496940581272853264001706804810269702453007698) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_39 :
    recurrence2Scalar2Main.coeff 39 =
      -((35252214770680601062 * 10 ^ 70 +
        9276989989382682979145153004396569967294191145921157197508103712334399) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_40 :
    recurrence2Scalar2Main.coeff 40 =
      ((736649520534053202030 * 10 ^ 70 +
        3568757422172062576148809235836828643579761529688734635530676854489928) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_41 :
    recurrence2Scalar2Main.coeff 41 =
      -((10318257044567886904209 * 10 ^ 70 +
        9116825605648942440892850269709561259142195338418923404258431137494566) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_42 :
    recurrence2Scalar2Main.coeff 42 =
      ((36443043350551329698719 * 10 ^ 70 +
        1754208465588934041143545789138362135860627625364168189912303350113599) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_43 :
    recurrence2Scalar2Main.coeff 43 =
      ((2689340703725529490272333 * 10 ^ 70 +
        1964494283454713474801395473024528935386640449731870651093158458542301) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_44 :
    recurrence2Scalar2Main.coeff 44 =
      -((83120614213464567397639261 * 10 ^ 70 +
        4400626757602995650773846463810783783591508195301203009483648962644708) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_45 :
    recurrence2Scalar2Main.coeff 45 =
      ((1114471632697188121917364593 * 10 ^ 70 +
        6822438141399277770716702505378060986744828805669299767320610881209195) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_46 :
    recurrence2Scalar2Main.coeff 46 =
      ((1811936574286448532172806588 * 10 ^ 70 +
        5836103131209408360041211596627926477439572385007107528999005775478765) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_47 :
    recurrence2Scalar2Main.coeff 47 =
      -((322115911106498108882028940110 * 10 ^ 70 +
        1581684073395032195482134932858094693444640248319997171820638758445660) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_48 :
    recurrence2Scalar2Main.coeff 48 =
      -((520940962334617201591297645520 * 10 ^ 70 +
        8623945024767158866936411470172328887607448408195091806546384594980439) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_49 :
    recurrence2Scalar2Main.coeff 49 =
      ((440458655640833418610882732439122 * 10 ^ 70 +
        0815780273781241026986723871684923318948911799872011776996803489994819) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_50 :
    recurrence2Scalar2Main.coeff 50 =
      -((20340323167221691460460784442615880 * 10 ^ 70 +
        1057428207513990628001118639895742412715793094540321027667098585200669) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_51 :
    recurrence2Scalar2Main.coeff 51 =
      ((598102977884323476561992231828859336 * 10 ^ 70 +
        7733446515937484623243994039504174881451845542583984106952711489047116) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_52 :
    recurrence2Scalar2Main.coeff 52 =
      -((13393260606313757996084271416606041468 * 10 ^ 70 +
        0758564187247159548238127295509137506352126127077594153034372565146909) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_53 :
    recurrence2Scalar2Main.coeff 53 =
      ((239802840703225678054107165332935663943 * 10 ^ 70 +
        7623161115903474642170095556305623832424088559538211721641607030482904) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_54 :
    recurrence2Scalar2Main.coeff 54 =
      -((3394113169659754985269419700053150007662 * 10 ^ 70 +
        7357772952298395842067825111590163348205639410467306783087642114803539) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_55 :
    recurrence2Scalar2Main.coeff 55 =
      ((33353143116362703083781676951954179991017 * 10 ^ 70 +
        3496619824252303510271817710287297592474684895475919497747010266180580) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_56 :
    recurrence2Scalar2Main.coeff 56 =
      -((33370174793629617068540671681826416209141 * 10 ^ 70 +
        1746261198886546019303539284380499033802058768382022955426298609800839) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_57 :
    recurrence2Scalar2Main.coeff 57 =
      -((8669420916550283735337571112390435530610746 * 10 ^ 70 +
        5925866224085386844900656567312212826972618172363611761908015678321888) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_58 :
    recurrence2Scalar2Main.coeff 58 =
      ((280367441501543725649867005150851850874480614 * 10 ^ 70 +
        1297337377169159043904103369126710724085005048867397615310374921857266) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_59 :
    recurrence2Scalar2Main.coeff 59 =
      -((6305600641385068433139850130826659248242417427 * 10 ^ 70 +
        4088199747477545904758718466788909193424994696296646277924665910656853) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_60 :
    recurrence2Scalar2Main.coeff 60 =
      ((118499207073787859860146438625239385318198633205 * 10 ^ 70 +
        5908082442802460759046440694977966762065945113792730366456667900270699) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_61 :
    recurrence2Scalar2Main.coeff 61 =
      -((1958140663183750269703620007886073771582107645698 * 10 ^ 70 +
        5738089754676262352279871906636847362937634986560842637400896496451958) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_62 :
    recurrence2Scalar2Main.coeff 62 =
      ((28947990843536646800716405344249293348255323190908 * 10 ^ 70 +
        6823319631899911493194946032774589081170621016460391250597973021102361) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_63 :
    recurrence2Scalar2Main.coeff 63 =
      -((384102030884694962406929268407786691003419177610857 * 10 ^ 70 +
        7502004751042309998783736331993965953439186451631975935113438415149874) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_64 :
    recurrence2Scalar2Main.coeff 64 =
      ((4542426431794067351085848256733479588060132903034026 * 10 ^ 70 +
        2975916411347843032534411372006100695795907692039740228725911423150066) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_65 :
    recurrence2Scalar2Main.coeff 65 =
      -((46821868941673083796735184219420463227179235124170134 * 10 ^ 70 +
        8875309011657045235541517744401823861967946931453691390516766709503504) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_66 :
    recurrence2Scalar2Main.coeff 66 =
      ((395414611703218390243217217676187161099918132549664435 * 10 ^ 70 +
        3481839139161752482848598876929132102331819646626244851497489323860750) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_67 :
    recurrence2Scalar2Main.coeff 67 =
      -((2150426602031640085802544761814026037391828159490271028 * 10 ^ 70 +
        8460724558156443894044338385545254361319830723380362601209346788231683) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_68 :
    recurrence2Scalar2Main.coeff 68 =
      -((7638531835744286558529135984736341793853507412082271185 * 10 ^ 70 +
        9649430815071452858076069204457631283436974553820652231124987010704211) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_69 :
    recurrence2Scalar2Main.coeff 69 =
      ((461195084211357391517293531493439486661550955730976026728 * 10 ^ 70 +
        9534216896502901931895094629667693575842628404968626017004495500569191) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_70 :
    recurrence2Scalar2Main.coeff 70 =
      -((9015851482647682413281120725815565998117990390944899736616 * 10 ^ 70 +
        1412756376525035484101188277833488455571491883352117482380785901703363) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_71 :
    recurrence2Scalar2Main.coeff 71 =
      ((134565519448727490850096292894658668421334135270257128978463 * 10 ^ 70 +
        4054274606160662415777650521039007204143328678030020674523014094189439) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_72 :
    recurrence2Scalar2Main.coeff 72 =
      -((1737291088481775946628494158426805734964335873322337304912508 * 10 ^ 70 +
        0080533233632806505368280451760939085689212155028671423758864922456883) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_73 :
    recurrence2Scalar2Main.coeff 73 =
      ((20275765405165084933658293530243421227634092345159864037109618 * 10 ^ 70 +
        3977585362725092128498465316864139081753996488998646902787073920790728) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_74 :
    recurrence2Scalar2Main.coeff 74 =
      -((218464809488103099574875571512065337259470418412222079082559965 * 10 ^ 70 +
        3960210497550242223371845848566972783107813767053005393141184645076062) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_75 :
    recurrence2Scalar2Main.coeff 75 =
      ((2199170491537072738547234777557586161238756027204067899209643619 * 10 ^ 70 +
        1892330447074262304192754939815659993144725835054834564380013026193371) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_76 :
    recurrence2Scalar2Main.coeff 76 =
      -((20840475597712613438596252688298588186594085510077526914062213340 * 10 ^ 70 +
        1713097054276486885276109977162772355565474136621438654104751982730619) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_77 :
    recurrence2Scalar2Main.coeff 77 =
      ((186901201683872147710328571796558756343370029392287371967779108486 * 10 ^ 70 +
        2513476437224419095959701958372833670876558105396760452316590590097383) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_78 :
    recurrence2Scalar2Main.coeff 78 =
      -((1592350834805553737050477620601815080573392746237958572900474742302 * 10 ^ 70 +
        7908491377346243943261230898748501899247071695204412458584408175050602) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_79 :
    recurrence2Scalar2Main.coeff 79 =
      ((12925103463121916259587994370275916529288955810068119624134121026079 * 10 ^ 70 +
        9122982010030923601829964215864384989471093092384027127652184890332181) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_80 :
    recurrence2Scalar2Main.coeff 80 =
      -((100169923692549578647790418663685007325896745825145928516458787723804 * 10 ^ 70 +
        7642563155422397883327135721609183116623080174215386944690841838579143) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_81 :
    recurrence2Scalar2Main.coeff 81 =
      ((742438344420302227143250327220253089005130174850868175712772434237241 * 10 ^ 70 +
        5924405154748368978056136006925984832504522174738516023741040746932221) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_82 :
    recurrence2Scalar2Main.coeff 82 =
      -((5269294915611503978343151251094510903097037281475443333521048096990425 * 10 ^ 70 +
        6408399731431656827223869811031849899980923290595004139252053941589326) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_83 :
    recurrence2Scalar2Main.coeff 83 =
      (((3 * 10 ^ 70 +
        5847203690519808488161664430971685345726443219749709573386995262059605) * 10 ^ 70 +
        5380581652139313405666936545251622061012697822253014730765289354140451) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_84 :
    recurrence2Scalar2Main.coeff 84 =
      -(((23 * 10 ^ 70 +
        3959980907054204163414342590175167475981846720357365334492238552267728) * 10 ^ 70 +
        0734219204577271433759105766904442160350676560920156133677610946684793) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_85 :
    recurrence2Scalar2Main.coeff 85 =
      (((146 * 10 ^ 70 +
        5996975800228024525028639652381313818085194087512867136790448936587823) * 10 ^ 70 +
        2736010082754030124515781517745497861269690077633813914847709892163353) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_86 :
    recurrence2Scalar2Main.coeff 86 =
      -(((882 * 10 ^ 70 +
        4605783784036102227979101189213163764810606968418665458162872304975699) * 10 ^ 70 +
        6416952126235487557300209366174985023976205598910791607672844504787618) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_87 :
    recurrence2Scalar2Main.coeff 87 =
      (((5105 * 10 ^ 70 +
        2396293060499439488724915973639603504616421977372981471919756405628192) * 10 ^ 70 +
        2271017798123382181988875846331377792592293826129836432624550592493819) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_88 :
    recurrence2Scalar2Main.coeff 88 =
      -(((28390 * 10 ^ 70 +
        9575476638571668704462185970066425763543223699876009555049847235874278) * 10 ^ 70 +
        7302248927740669524839155272133424175653403974387802347685888321677345) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_89 :
    recurrence2Scalar2Main.coeff 89 =
      (((151758 * 10 ^ 70 +
        5824340252178451158906946315736589403020617876611538410482848283918212) * 10 ^ 70 +
        0113335752941977260642322438158756374670845668298859671923784456177856) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_90 :
    recurrence2Scalar2Main.coeff 90 =
      -(((779452 * 10 ^ 70 +
        4844387313709757669527528220794941358354374796105816311531705081726379) * 10 ^ 70 +
        7927635988459701512386616395146164329050939916503811934183645753891870) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_91 :
    recurrence2Scalar2Main.coeff 91 =
      (((3844646 * 10 ^ 70 +
        1267494430123415052291778898866379025539798531583060903511065915005689) * 10 ^ 70 +
        8920790074024902472235898812634818382559375560084258512366802012784898) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_92 :
    recurrence2Scalar2Main.coeff 92 =
      -(((18199647 * 10 ^ 70 +
        9691564437142171691696125239365115373811139059804463376399933170342398) * 10 ^ 70 +
        7686841192484438693317994324656609006918650836432833677353179453974502) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_93 :
    recurrence2Scalar2Main.coeff 93 =
      (((82615696 * 10 ^ 70 +
        2759337552822079221469684719671806127806104994354548930647402116728781) * 10 ^ 70 +
        0191137042352746015458765530531770295214845317622921123571083611139238) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_94 :
    recurrence2Scalar2Main.coeff 94 =
      -(((359239796 * 10 ^ 70 +
        0234355682966465998133197703393028160060404700941656738416219659833936) * 10 ^ 70 +
        2407292092928797250059813087732670781360034503049792495423218155746129) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_95 :
    recurrence2Scalar2Main.coeff 95 =
      (((1493683769 * 10 ^ 70 +
        3484533406279069577579741206654555224046668914555705618037706082486034) * 10 ^ 70 +
        7982213458294706215688196310672751675732399954382517189387723795801034) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_96 :
    recurrence2Scalar2Main.coeff 96 =
      -(((5919776961 * 10 ^ 70 +
        0606568419642561712651758372219849973485632223018111794353112339441951) * 10 ^ 70 +
        8596510409596973387975543844970017303939222300847021486558382905893750) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_97 :
    recurrence2Scalar2Main.coeff 97 =
      (((22237094224 * 10 ^ 70 +
        6643413798754019802367980241020090645212250943484919101428974474097270) * 10 ^ 70 +
        7302947107080052997729296415439982990259911513996536364937164337148359) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_98 :
    recurrence2Scalar2Main.coeff 98 =
      -(((78420477004 * 10 ^ 70 +
        3596210200962220119080897357468735780484959508127110479611227575852045) * 10 ^ 70 +
        3403100751221773810003060031582700377971631171411976377909898928640363) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_99 :
    recurrence2Scalar2Main.coeff 99 =
      (((255563808746 * 10 ^ 70 +
        3434558372972373116783263523777411400427905098123742238685763877228713) * 10 ^ 70 +
        5725039038020077026666774159616415494247289360179979110625293583002652) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_100 :
    recurrence2Scalar2Main.coeff 100 =
      -(((748951492261 * 10 ^ 70 +
        5881866046815239736271268509325527232415227401814318473533590775912511) * 10 ^ 70 +
        7098151357229753829156241018501800864705078013274281894511540493231817) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_101 :
    recurrence2Scalar2Main.coeff 101 =
      (((1867124214056 * 10 ^ 70 +
        5329374311645379979280092407901283978763409040626749644405839644087864) * 10 ^ 70 +
        6362319819207771221288365004669723187345669251741239717297980827118728) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_102 :
    recurrence2Scalar2Main.coeff 102 =
      -(((3346116819860 * 10 ^ 70 +
        8859260512942387535045905239579109258181984878975006313184830763913474) * 10 ^ 70 +
        7868913204071340732516782314138398223735376607898268554135581820377848) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_103 :
    recurrence2Scalar2Main.coeff 103 =
      (((1117598439 * 10 ^ 70 +
        4317070299997385687168402923841720831226923038447230609658758933130775) * 10 ^ 70 +
        0134500147066463859554865318542920183127683855142890460296086289001949) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_104 :
    recurrence2Scalar2Main.coeff 104 =
      (((39494165531559 * 10 ^ 70 +
        9548899146763257233870542135532689473732200026878399033117810093110202) * 10 ^ 70 +
        4722518099981123520820255196383891807618999192595344843257327398640633) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_105 :
    recurrence2Scalar2Main.coeff 105 =
      -(((270491688530121 * 10 ^ 70 +
        5872616025072480920526523612649933258600934811767094873032412931244224) * 10 ^ 70 +
        4888080866932019747166662312972384785040240276355616795453721494442432) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_106 :
    recurrence2Scalar2Main.coeff 106 =
      (((1411649696493261 * 10 ^ 70 +
        3410255702363756000595341274507149075137030325910958344293119742039427) * 10 ^ 70 +
        7161117101153837808918590229392870831804933834354640172633901617798742) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_107 :
    recurrence2Scalar2Main.coeff 107 =
      -(((6546801337469017 * 10 ^ 70 +
        0154767033530170386447716218095508616787891410409038819051153582605367) * 10 ^ 70 +
        7986666567664317548283848157066570357356712379017697793654980437178525) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_108 :
    recurrence2Scalar2Main.coeff 108 =
      (((27191515996179012 * 10 ^ 70 +
        1471221310986874058531676141163307895669995107815750656084283823000565) * 10 ^ 70 +
        7418168600941725724125070883876726370853775417537489572432666069343321) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_109 :
    recurrence2Scalar2Main.coeff 109 =
      -(((96774868001203307 * 10 ^ 70 +
        0482430287523192862844394920993684798430370641556150476154462696418813) * 10 ^ 70 +
        8115706035401408297948310566618692388624493616967739190835119053792239) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_110 :
    recurrence2Scalar2Main.coeff 110 =
      (((268955145239699505 * 10 ^ 70 +
        2008246648050308110229155512821596094329557966231525998529517966311228) * 10 ^ 70 +
        6136969157999921033937298254883854196577338651848879480179009500995780) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_111 :
    recurrence2Scalar2Main.coeff 111 =
      -(((440481819650571093 * 10 ^ 70 +
        0801852123060705485155925046938296744473999750302390969932402604901518) * 10 ^ 70 +
        0676895197395705265503181203903163701904871638869316965069591638861361) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_112 :
    recurrence2Scalar2Main.coeff 112 =
      -(((450944165789034084 * 10 ^ 70 +
        4864767141509014624970698455662998929991419366793489796554300343036580) * 10 ^ 70 +
        5537520233881208060948604987366779378136939250425751105082591327996695) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_113 :
    recurrence2Scalar2Main.coeff 113 =
      (((5371241629953495991 * 10 ^ 70 +
        6619924085245617838153316851603109695944974146751961088949578553605868) * 10 ^ 70 +
        8755048458682881356351869508027988266633135702639056624708293211060233) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_114 :
    recurrence2Scalar2Main.coeff 114 =
      -(((8902679344999947390 * 10 ^ 70 +
        1481688707325825704657968858068732182814384638203038081925867576077216) * 10 ^ 70 +
        1214672445762316135133137940847735086653386720210550931360350283840452) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_115 :
    recurrence2Scalar2Main.coeff 115 =
      -(((83057492718088624027 * 10 ^ 70 +
        1224469456490807539603072755227470339882238002210502464079347083467086) * 10 ^ 70 +
        0468501672835082639224792076277821647644365194455487975734656480869414) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_116 :
    recurrence2Scalar2Main.coeff 116 =
      (((751632929655532352457 * 10 ^ 70 +
        9408757279226660078248937144460674279487783046229008998698584693278487) * 10 ^ 70 +
        9345285018172635017189012248555804676418697546941332174323229527587206) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_117 :
    recurrence2Scalar2Main.coeff 117 =
      -(((3258213788154652648524 * 10 ^ 70 +
        8735858516934370687550653076402400852922423499184984748705680665233335) * 10 ^ 70 +
        8711267500179481961109390363326429141214594134771785691780353858167308) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_118 :
    recurrence2Scalar2Main.coeff 118 =
      (((6938439881987786550790 * 10 ^ 70 +
        9511376215558298778453462353628743127902001842667705232295465790395770) * 10 ^ 70 +
        2336497647853970623603723054122807068530341641504792809863988447294283) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_119 :
    recurrence2Scalar2Main.coeff 119 =
      (((14118191629802404709485 * 10 ^ 70 +
        2818492525655951721750167952331123960206708121370188769705525985278500) * 10 ^ 70 +
        7596118561058526929951863662964232052945225457159763940665948237861855) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_120 :
    recurrence2Scalar2Main.coeff 120 =
      -(((212723220454337360758802 * 10 ^ 70 +
        0218320943513971648887311889174598924999610843543852229691593346751796) * 10 ^ 70 +
        4915113869267603547472976821455854464962872289211133787665042441818705) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_121 :
    recurrence2Scalar2Main.coeff 121 =
      (((1128025539701975188688926 * 10 ^ 70 +
        1343689454047061936179931246679190552818638563834252789794446585915579) * 10 ^ 70 +
        1963564068765307130833671752069653794977607861392867434626910978575352) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_122 :
    recurrence2Scalar2Main.coeff 122 =
      -(((3626121252669976166597441 * 10 ^ 70 +
        7165836055104681539316240300554836425666750722370011533699488775901259) * 10 ^ 70 +
        2572495711213773164685735716518000420757483355339221812995422065367093) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_123 :
    recurrence2Scalar2Main.coeff 123 =
      (((4029658895247337459267054 * 10 ^ 70 +
        4528042109609880283284684436247180790079246014607476596784836820157899) * 10 ^ 70 +
        3344589853051070704508408448210316292618788411361339374907824145319542) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_124 :
    recurrence2Scalar2Main.coeff 124 =
      (((35298347676045526661943578 * 10 ^ 70 +
        0115237707488565128298099167049777776028282171822623058602160873416630) * 10 ^ 70 +
        2712993776652739108573650097584280055783913247746684087511771017460656) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_125 :
    recurrence2Scalar2Main.coeff 125 =
      -(((280531446873040803418505263 * 10 ^ 70 +
        7032244053811903288667939294527263391543846144454235945264776536514840) * 10 ^ 70 +
        3940812854925099282846476307403433450845234353656278713816491965497186) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_126 :
    recurrence2Scalar2Main.coeff 126 =
      (((1095838059515918501733284497 * 10 ^ 70 +
        7616860868742589908052637769973386918544840369178913739882434154812891) * 10 ^ 70 +
        5108145396115325085562634625259528155226399559525872717041474792780522) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_127 :
    recurrence2Scalar2Main.coeff 127 =
      -(((2026646295313540755383663439 * 10 ^ 70 +
        7838315264810355558708003598301490358347692138133976029939237050571537) * 10 ^ 70 +
        4696335737614551161064963410543454078548811235357643877751765606699238) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_128 :
    recurrence2Scalar2Main.coeff 128 =
      -(((4129123046933622548440349010 * 10 ^ 70 +
        0380486686628063781717891530966773947415785738039298699476567424762163) * 10 ^ 70 +
        9939310780616537215837617467238022497286826763099264954310618139471796) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_129 :
    recurrence2Scalar2Main.coeff 129 =
      (((46335006778369258002019556759 * 10 ^ 70 +
        3474679060337488500399968182877429164746108146521257341180416640831759) * 10 ^ 70 +
        5952929018413053763721271131837750380541950530707957521344213220556345) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_130 :
    recurrence2Scalar2Main.coeff 130 =
      -(((178863255719968698597248545784 * 10 ^ 70 +
        1377533502805185970700040466741890853005400927479721311624046924817523) * 10 ^ 70 +
        0006821603506825328690750959387712776296925670032197018918954706383465) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_131 :
    recurrence2Scalar2Main.coeff 131 =
      (((386082759235756225885018566067 * 10 ^ 70 +
        9580686101873023808950215261288625228260221406850551215995247733573641) * 10 ^ 70 +
        9308851007909904083724381029583862277102816045653653093985002157627388) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_132 :
    recurrence2Scalar2Main.coeff 132 =
      -(((352449508920830040632821713840 * 10 ^ 70 +
        6273706376037527453703772784798313488969812433516799629161670018063426) * 10 ^ 70 +
        1454424907745491161910389349884752117164591923088377960901727105458801) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_133 :
    recurrence2Scalar2Main.coeff 133 =
      -(((643566432246781539191298390337 * 10 ^ 70 +
        7497925988981182452966046370799609576072384618842520280281505737019749) * 10 ^ 70 +
        0152656964539094777864561424683680352830171930134072180387077823807377) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_134 :
    recurrence2Scalar2Main.coeff 134 =
      (((6626277951320958781799249129082 * 10 ^ 70 +
        4543427510799771411692756911665002433270050846069981878669020969917958) * 10 ^ 70 +
        3454065708060656414784434451030018213867155335534860136215510607943199) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 0 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_135 :
    recurrence2Scalar2Main.coeff 135 =
      -(((54485586686939198498952599373763 * 10 ^ 70 +
        4743892221971204680797036637326688993412608376049192105883084564903873) * 10 ^ 70 +
        1321164189810052878425772215850870483653328069665098682692686987591264) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_136 :
    recurrence2Scalar2Main.coeff 136 =
      (((309526800913479912006433288556406 * 10 ^ 70 +
        2149070164569158427399078485287220533259734545966017914468650070681320) * 10 ^ 70 +
        3578363202890467207457415991277006293298658260413313345405519843732238) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_137 :
    recurrence2Scalar2Main.coeff 137 =
      -(((945290292108872641528855725439743 * 10 ^ 70 +
        3517792967443205374394879029770132466246886673990397481179384073748268) * 10 ^ 70 +
        7867898120942625258319968268001546969771443848073428026101649669745737) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_138 :
    recurrence2Scalar2Main.coeff 138 =
      (((169763285114945626836936548594403 * 10 ^ 70 +
        8494595245409050059689043492028430930236053000630504976369726520205522) * 10 ^ 70 +
        4278258614718078079248126894262991913758035846386372832466465868637687) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_139 :
    recurrence2Scalar2Main.coeff 139 =
      (((10611872884979399698253154130620584 * 10 ^ 70 +
        2514437562173748094242686336708879467977422683863621823143543265302542) * 10 ^ 70 +
        4882395272159961111158311612415118839197427486874781193442252143672804) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_140 :
    recurrence2Scalar2Main.coeff 140 =
      -(((33089263681457064873817674907662872 * 10 ^ 70 +
        5167047414019766326817676650265169620060181711526896428690951686804892) * 10 ^ 70 +
        6170003963483933779194391059773851456367326425645627107774888182522243) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_141 :
    recurrence2Scalar2Main.coeff 141 =
      -(((45908209715338228744861295835678066 * 10 ^ 70 +
        1656588851499292365714574278045454685435094896506160180134116511304100) * 10 ^ 70 +
        1267872703011144589362385735182514557323817475904610981425134455249617) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_142 :
    recurrence2Scalar2Main.coeff 142 =
      (((520210097179915534942563429737774788 * 10 ^ 70 +
        9641452217672601266267154607446394467435286761600726813869822807161672) * 10 ^ 70 +
        8837861379356949846424946351562692201613271851319223708893341146723118) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_143 :
    recurrence2Scalar2Main.coeff 143 =
      -(((102164427714624774254456583053635711 * 10 ^ 70 +
        6401912139696179011782584756738638253591932106669599013025035649615375) * 10 ^ 70 +
        7244235024394934623505123985573331324088605730879492449563494433225144) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_144 :
    recurrence2Scalar2Main.coeff 144 =
      -(((11767725587110638819383923378014754622 * 10 ^ 70 +
        6277397637188672482828176093706090676562783538384891307068051763518390) * 10 ^ 70 +
        7048160132899057158960508224569283378597943136157877226473606341156522) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_145 :
    recurrence2Scalar2Main.coeff 145 =
      (((54278452074130025735485116508205669232 * 10 ^ 70 +
        8551368966767638904503348851486129030103114100294561263088985148624948) * 10 ^ 70 +
        8354320270625750133492323484115013867872138217639282233257933092384118) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 0 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Main_coeff_146 :
    recurrence2Scalar2Main.coeff 146 =
      -(((27173337470222222866710661417093738957 * 10 ^ 70 +
        5328971513544227314490238202873040965304990720863674815788212396739409) * 10 ^ 70 +
        3375521457013598106196401829518706954572543352761752825951469773530423) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_147 :
    recurrence2Scalar2Main.coeff 147 =
      -(((780658494764747690016024948502562555514 * 10 ^ 70 +
        4705516603648887840909095640794803226594653670483289449135095440913868) * 10 ^ 70 +
        7106577287613963046912898790509663915390378815683203178771817602063764) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (148 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_148 :
    recurrence2Scalar2Main.coeff 148 =
      (((3705006199239753898883764555228773699553 * 10 ^ 70 +
        5383313123680731371450007734397092434646756484748037862584329404254954) * 10 ^ 70 +
        4629208096938770407116322507446710111130253971794896523251010762255863) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 21 = 19 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (149 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_149 :
    recurrence2Scalar2Main.coeff 149 =
      -(((3804426210447882939389722377704339076802 * 10 ^ 70 +
        9987841744811378578931908303967877764563242510117551508689156478220471) * 10 ^ 70 +
        9767348835925872997565887806999019076774477618188626667018230939657135) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 22 = 19 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (150 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_150 :
    recurrence2Scalar2Main.coeff 150 =
      -(((36359594917833095547330791554421090653149 * 10 ^ 70 +
        0135948646196871367641503539129281341297535645592228415771406390427131) * 10 ^ 70 +
        5306114728916842743270778324829223191444392845862691456975846151638470) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 23 = 19 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (151 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_151 :
    recurrence2Scalar2Main.coeff 151 =
      (((193072964510524146736787462491707936393675 * 10 ^ 70 +
        4662344836205460422386408764093386339426408855131946017091312275893690) * 10 ^ 70 +
        5005352366880257635813860010013269824924818838818699649003159540546045) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 24 = 19 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (152 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_152 :
    recurrence2Scalar2Main.coeff 152 =
      -(((267384981328010987703676831132499691133977 * 10 ^ 70 +
        9302211363535287316829070171709039956522719547159414326601334998664694) * 10 ^ 70 +
        1869586802207150520917399614643974583526065845247000523624550591532448) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 25 = 19 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (153 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_153 :
    recurrence2Scalar2Main.coeff 153 =
      -(((1441638645949383759390599662860639397142932 * 10 ^ 70 +
        1703483906128295940717941520531465825101646615635362766759089023712461) * 10 ^ 70 +
        0348900761221758878233868624479866591276438973726423270131640622261497) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 26 = 19 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (154 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_154 :
    recurrence2Scalar2Main.coeff 154 =
      (((8730960381700249696173712842165181926504409 * 10 ^ 70 +
        9263218558309758781517884105800348526781138826072390824638494725882263) * 10 ^ 70 +
        5953571576967832080519845055910524438958191620260697934876197330061406) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 27 = 19 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (155 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_155 :
    recurrence2Scalar2Main.coeff 155 =
      -(((14936164363001835161697355191382438638619850 * 10 ^ 70 +
        0763342379933923313508464303218437445954185223083736445814480412278199) * 10 ^ 70 +
        8433151318195741017675540097566172640492565840658581218231591217272002) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 28 = 19 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (156 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_156 :
    recurrence2Scalar2Main.coeff 156 =
      -(((48730265626786239023925741980105969123690663 * 10 ^ 70 +
        2560815872370466468050611664149477462073178952648671314806028030726412) * 10 ^ 70 +
        4909739250871840715913821316906835789583115257202155902676110895467950) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 29 = 19 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (157 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_157 :
    recurrence2Scalar2Main.coeff 157 =
      (((350963535823145499590395901656652486502609081 * 10 ^ 70 +
        6630031168719885107815436977992072187045926729887942401793425881843143) * 10 ^ 70 +
        3144943752838500656098497989478242881990873872552192377055378798897312) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 30 = 19 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (158 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_158 :
    recurrence2Scalar2Main.coeff 158 =
      -(((705880920158951093968040548102675201812341986 * 10 ^ 70 +
        5710438192888033948741901009536723302000645930953918605203273241965003) * 10 ^ 70 +
        2088074490278710569816748103104646309355559662821009640766374596844548) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 31 = 19 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (159 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_159 :
    recurrence2Scalar2Main.coeff 159 =
      -(((1449407974341019669923346311375676210563538826 * 10 ^ 70 +
        2153470319996621314411772729795754940736235757838318238667226048569026) * 10 ^ 70 +
        9820758306311579508517922624814253926394544617656683670245760747264331) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 32 = 19 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (160 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_160 :
    recurrence2Scalar2Main.coeff 160 =
      (((13123491895567280674438102088505034595338981397 * 10 ^ 70 +
        4264318515494519539242902714564775782368220478306508201350972115881856) * 10 ^ 70 +
        1862287008973405831461886963364664221776311229235443019217280592840252) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 33 = 19 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (161 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_161 :
    recurrence2Scalar2Main.coeff 161 =
      -(((30840263804366443953143927845138057921449826501 * 10 ^ 70 +
        2779411086599557751749816562849165990524755926955070653999681909621943) * 10 ^ 70 +
        5366665344392726092554432269358947502446785337922604312034684476650933) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 34 = 19 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (162 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_162 :
    recurrence2Scalar2Main.coeff 162 =
      -(((34828331176213477516396987348979394072980732403 * 10 ^ 70 +
        5623106062101144797196391927070294517317378536813719565706895267002782) * 10 ^ 70 +
        4336184555006246776595377056136925464074144602688878668471293690395313) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 35 = 19 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (163 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_163 :
    recurrence2Scalar2Main.coeff 163 =
      (((467983132084550456040991200583938409005979161812 * 10 ^ 70 +
        9759242426275161026756069857121991637626609037119365165237089088280672) * 10 ^ 70 +
        6722058010201563073497802533857171702560533176817410664233630696839538) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 36 = 19 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (164 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_164 :
    recurrence2Scalar2Main.coeff 164 =
      -(((1336229493481215088851260485445624902215518689756 * 10 ^ 70 +
        1668080056435247256716458955509268304407866099544985305040632298257795) * 10 ^ 70 +
        4026466871056601231866254164810357131556079684891437642690329040961495) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (165 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_165 :
    recurrence2Scalar2Main.coeff 165 =
      -(((134376134833256417009703926308426610105782363082 * 10 ^ 70 +
        9107584524875342310232091793476226008058532516743706076835604704690086) * 10 ^ 70 +
        8933932050705268779794058186381682901365194130818058834390357561821942) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 38 = 19 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (166 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_166 :
    recurrence2Scalar2Main.coeff 166 =
      (((14861871457020198867550452785169827782361657947572 * 10 ^ 70 +
        9967132112056967034171086058710276487441542492296828351223168748286309) * 10 ^ 70 +
        1884085835184585334596816049315279579032680518162902547736205784432715) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 39 = 19 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (167 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_167 :
    recurrence2Scalar2Main.coeff 167 =
      -(((54664854113128733950089935411702435186390827255323 * 10 ^ 70 +
        6288359904892876660874203113965882980744405907019500299153578114362931) * 10 ^ 70 +
        6037511981397673914863478366107846342552190623337254715793385671347231) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 40 = 19 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (168 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_168 :
    recurrence2Scalar2Main.coeff 168 =
      (((52937652315206331451626018213520077380371719048301 * 10 ^ 70 +
        9379507933359128901384898493150548720193249045300182229723952419535254) * 10 ^ 70 +
        1681655463939647893173422977586054769047688924909316173891172610300743) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 41 = 19 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (169 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_169 :
    recurrence2Scalar2Main.coeff 169 =
      (((356120918268205878304277686779267829151457826126850 * 10 ^ 70 +
        9883142763382247435846122309337954880347769123734185959379250819184449) * 10 ^ 70 +
        4284968452636461825457950827314699763616620241186780278525410460804781) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 42 = 19 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (170 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_170 :
    recurrence2Scalar2Main.coeff 170 =
      -(((1890736668630311484594832175022980606539351712143690 * 10 ^ 70 +
        0214903876966533998646258748143015660956052758578217528498902906815043) * 10 ^ 70 +
        1399275492466997006334403920280133982488044782340901364545225642534153) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 0 +
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
    rw [show 43 = 19 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (171 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_171 :
    recurrence2Scalar2Main.coeff 171 =
      (((3746234560853927071524454182785329870959243715578636 * 10 ^ 70 +
        3233545025599102425185445244184533194732746236231727601359202117462167) * 10 ^ 70 +
        6040907905872231651438377062006321594031784820372080561703147548891851) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 0 +
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
    rw [show 44 = 19 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (172 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_172 :
    recurrence2Scalar2Main.coeff 172 =
      (((3803897387504099881095473843378071563789003730042691 * 10 ^ 70 +
        0449956530987444026072391706450649190106770485756993093463974205442281) * 10 ^ 70 +
        8838751083515538910066234603949974171026097975774355688919392407126470) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 0 +
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
    rw [show 45 = 19 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (173 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_173 :
    recurrence2Scalar2Main.coeff 173 =
      -(((49756747913293379334345932894304461902551871365142393 * 10 ^ 70 +
        0413058299449755638882991962111004304559859776309183803021566984705702) * 10 ^ 70 +
        7468853674002123298305951020173453300401792913921105473050086442318136) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 0 +
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
    rw [show 46 = 19 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (174 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_174 :
    recurrence2Scalar2Main.coeff 174 =
      (((155065493619634024842212067477059304111825376130238023 * 10 ^ 70 +
        2751839111028426178479692950926271116390041945868898812074437759835653) * 10 ^ 70 +
        4849178226571002282674910366359318226763416019421432514267305650304340) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 0 +
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
    rw [show 47 = 19 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (175 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_175 :
    recurrence2Scalar2Main.coeff 175 =
      -(((142263302139801581071850377844160861492397021803144099 * 10 ^ 70 +
        6779706999397690209702931400249323621770751606676129186299197990908113) * 10 ^ 70 +
        8321594531451202950744601452709231880005896714269514867029629306422195) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 0 +
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
    rw [show 48 = 19 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (176 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_176 :
    recurrence2Scalar2Main.coeff 176 =
      -(((832882274823618544724622950958310640649673248308275206 * 10 ^ 70 +
        8759893727660584769121409790691616413727204287699713015079630845924055) * 10 ^ 70 +
        6580981943235010684918201915165360403727377626675932459112884571972945) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 0 +
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
    rw [show 49 = 19 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (177 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_177 :
    recurrence2Scalar2Main.coeff 177 =
      (((4413929309351417067482660261573221600160418539902625643 * 10 ^ 70 +
        5493045062190240769644588210474492258636737823848194757643182707669858) * 10 ^ 70 +
        6418697530272012051529479929967083378020133406772767840633420647756862) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 0 +
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
    rw [show 50 = 19 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (178 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_178 :
    recurrence2Scalar2Main.coeff 178 =
      -(((9684796343207333334817581606993529337667383336655080197 * 10 ^ 70 +
        7119951653048419030133234088835933872403153359227285795167088085247263) * 10 ^ 70 +
        9551934174574417481347613034844679374817258070723466830339906000178637) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 0 +
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
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (179 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_179 :
    recurrence2Scalar2Main.coeff 179 =
      -(((282260917899151081588048408644450514816270396482996557 * 10 ^ 70 +
        7598798328021308578303571661189302728952002161830327263898697186057685) * 10 ^ 70 +
        9977081233217137105597207556595887828915935866839932043102108454396295) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 0 +
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
    rw [show 52 = 19 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (180 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_180 :
    recurrence2Scalar2Main.coeff 180 =
      (((81425357215319724822794250961147492919305469265901862671 * 10 ^ 70 +
        6521953287223018221465031974782819129343623212821356217726783140141496) * 10 ^ 70 +
        3213658008288055926111213916254324905594757772289462569915456772182488) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 0 +
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
    rw [show 53 = 19 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (181 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_181 :
    recurrence2Scalar2Main.coeff 181 =
      -(((308862979799554889494607823250576013184656590465503519297 * 10 ^ 70 +
        0755917842985844804331985387484034110274427653957313099246714162416405) * 10 ^ 70 +
        4025311443604729166590655735108182340911429839022319002119955818330702) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 0 +
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
    rw [show 54 = 19 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (182 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_182 :
    recurrence2Scalar2Main.coeff 182 =
      (((527744015280276195154724415059888588997768986752030209117 * 10 ^ 70 +
        4433197833597473473174358166547956108537887851540945417290463513310657) * 10 ^ 70 +
        0509422312774846269819231643425019966498969787636210239282976720152164) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 0 +
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
    rw [show 55 = 19 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (183 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_183 :
    recurrence2Scalar2Main.coeff 183 =
      (((419263697759710007008427096429584726149972127356702063083 * 10 ^ 70 +
        8020381280937083358386424569098787346017637743497166818257629863982407) * 10 ^ 70 +
        2513139718301499902783070683369663017574381158937292611402569658942727) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 0 +
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
    rw [show 56 = 19 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (184 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_184 :
    recurrence2Scalar2Main.coeff 184 =
      -(((5714546914872151676753573568591464806214238568716551017457 * 10 ^ 70 +
        8855851933828295235575157095800662143851039528625065450674711007258889) * 10 ^ 70 +
        2938613039826787229148879733721038512443977343928327319959926845922012) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 0 +
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
    rw [show 57 = 19 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (185 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_185 :
    recurrence2Scalar2Main.coeff 185 =
      (((18764759670320657310853357758786492133056189446837592744564 * 10 ^ 70 +
        1125604270612112060976820186246263930662630208268195964892002797311234) * 10 ^ 70 +
        9489533303599867504349574697273083754109623682400878228145618363394446) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 0 +
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
    rw [show 58 = 19 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (186 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_186 :
    recurrence2Scalar2Main.coeff 186 =
      -(((29275691792024957230969708037001600804456271033819117343038 * 10 ^ 70 +
        8600446437479316620138395433349953960077248717373877228699542522528001) * 10 ^ 70 +
        3291764219708833819243991565709984009347093314177726546561973493644737) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 0 +
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
    rw [show 59 = 19 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (187 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_187 :
    recurrence2Scalar2Main.coeff 187 =
      -(((25801914646185671232892470428220134915659945570532933746498 * 10 ^ 70 +
        1800635170526650397322941981134096497467267180402974129540095895004018) * 10 ^ 70 +
        9328492984153421521686332990080302778916664213333352399017404410017093) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 0 +
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
    rw [show 60 = 19 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (188 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_188 :
    recurrence2Scalar2Main.coeff 188 =
      (((311924119030704272773748043043632331721421840494914750154987 * 10 ^ 70 +
        9854955046159630076449405180205645771053384848967947801688859950748484) * 10 ^ 70 +
        5728068006767877073024959671861000862155612210356693893870431826257256) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 0 +
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
    rw [show 61 = 19 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (189 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_189 :
    recurrence2Scalar2Main.coeff 189 =
      -(((1019557048247799845667138511952189600432157183117041408318045 * 10 ^ 70 +
        0241800906426371879717329643337581190281603899784258885925553680906198) * 10 ^ 70 +
        6023765564538497444181767728011321148987268443138281764053179575844287) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 0 +
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
    rw [show 62 = 19 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (190 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_190 :
    recurrence2Scalar2Main.coeff 190 =
      (((1751788352511627712061916435055281840251016291544069901217735 * 10 ^ 70 +
        5130919282240061906455839687722886245602109833059278377946389808256613) * 10 ^ 70 +
        5062176092594206099697069592306016090789422220635958192144960348567435) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 0 +
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
    rw [show 63 = 19 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (191 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_191 :
    recurrence2Scalar2Main.coeff 191 =
      (((245757585795853263979002144991979672119931720178974725169166 * 10 ^ 70 +
        2100932675069903256305931426443652389038159505919971148019836419631156) * 10 ^ 70 +
        6399893891971801990069808962274388960777684679421783719622269463666939) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 0 +
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
    rw [show 64 = 19 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (192 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_192 :
    recurrence2Scalar2Main.coeff 192 =
      -(((12779083898079634373604155349151846795305549368520390216883746 * 10 ^ 70 +
        8873002974971357717081917851526820635319165137876432239871310415736827) * 10 ^ 70 +
        8488684290656915486614154287808262029960645861278830284901666249062249) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 0 +
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
    rw [show 65 = 19 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (193 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_193 :
    recurrence2Scalar2Main.coeff 193 =
      (((47749348049122264133587870865637025599453511673914435455596775 * 10 ^ 70 +
        9280463737993619556424120193064512602812614679430783103372865302864000) * 10 ^ 70 +
        8659764120763568609464558412220304525731405036178390436282067454563652) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 0 +
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
    rw [show 66 = 19 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (194 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_194 :
    recurrence2Scalar2Main.coeff 194 =
      -(((101332373013057264330392766020920733165745139411514764916225515 * 10 ^ 70 +
        3470607924735392130922057633597385557246096379649574018836010633915445) * 10 ^ 70 +
        7760439356115612237466417059330938052184329188505476844385525914378892) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 0 +
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
    rw [show 67 = 19 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (195 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_195 :
    recurrence2Scalar2Main.coeff 195 =
      (((86409044495734338979412640015449596735539251883608125287263176 * 10 ^ 70 +
        3665449512991272747742701860815570637843417587952782161735641967871193) * 10 ^ 70 +
        6772322084145911931300086231033341437953167560016929725503967685790966) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 0 +
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
    rw [show 68 = 19 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (196 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_196 :
    recurrence2Scalar2Main.coeff 196 =
      (((302065012393389476567417241773661048173623625856827577338002708 * 10 ^ 70 +
        4848623954089781606864853058978749174820857197642018485309332486328753) * 10 ^ 70 +
        1103944435389084384868042740518797891691633390498045915335835055950945) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 0 +
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
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (197 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_197 :
    recurrence2Scalar2Main.coeff 197 =
      -(((1700665608941478855747992923717194381988638737196853149867202223 * 10 ^ 70 +
        9765010161924555937901589728378812259573321651434965510358518039163643) * 10 ^ 70 +
        3321559858464771335759959532872806238608681862471173535780431408281308) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 0 +
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
    rw [show 70 = 19 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (198 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_198 :
    recurrence2Scalar2Main.coeff 198 =
      (((4750102864385744927121382524566696369112510863471979697916986564 * 10 ^ 70 +
        2594124764635905713309308946566889546363564884335627738778293539690762) * 10 ^ 70 +
        2703785099014904161775271566079543211615711210947115222862852609654303) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 0 +
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
    rw [show 71 = 19 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (199 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_199 :
    recurrence2Scalar2Main.coeff 199 =
      -(((8276792933613928494710548025423178445736258680130000253267034802 * 10 ^ 70 +
        1916091095030157800083439629652908978102452074459283142292931477900741) * 10 ^ 70 +
        7370714239230554812844177206278101568151853795250784751135124503924514) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 0 +
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
    rw [show 72 = 19 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (200 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_200 :
    recurrence2Scalar2Main.coeff 200 =
      (((4351665628494353518893883072750681819736788921878993101325244322 * 10 ^ 70 +
        6023582665360628749592416933490892814681070770756471989949434717850134) * 10 ^ 70 +
        9205751861082528263997887277737718103100405004796448287846429174866002) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 0 +
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
    rw [show 73 = 19 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (201 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_201 :
    recurrence2Scalar2Main.coeff 201 =
      (((30417056618114303230820623783202305627155771418844966163942408225 * 10 ^ 70 +
        2855142542841494740626525643938788593289017853473408405549660045376874) * 10 ^ 70 +
        9285502720227713553897446021333496062629746711366070741842237532058003) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 0 +
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
    rw [show 74 = 19 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (202 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_202 :
    recurrence2Scalar2Main.coeff 202 =
      -(((141813599372466701435126296033649790256053936993629774261972335724 * 10 ^ 70 +
        5450611453741952341232391409584220299385412151236283800247076641267853) * 10 ^ 70 +
        0305157093952875087026985956899207899931728110446347533082004035601635) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 0 +
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
    rw [show 75 = 19 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (203 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_203 :
    recurrence2Scalar2Main.coeff 203 =
      (((380539302842687688030952967357452823245778844269758725909504092054 * 10 ^ 70 +
        3483196534211119976857996237630171647435570179559413967648681002457181) * 10 ^ 70 +
        4976828217110158166888363522323206456177858346709340032860143629060847) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 0 +
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
    rw [show 76 = 19 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (204 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_204 :
    recurrence2Scalar2Main.coeff 204 =
      -(((705685990994243521310074082522434866850370421336003189832256232293 * 10 ^ 70 +
        8996527013272743627275169073618515189230199773347322694145253958437255) * 10 ^ 70 +
        8777219004053505833990291302198686216874057104150697557283646700436979) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 0 +
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
    rw [show 77 = 19 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (205 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_205 :
    recurrence2Scalar2Main.coeff 205 =
      (((716880237352304732854407424683648424081205995924493111021704243833 * 10 ^ 70 +
        1794221245737922343364273545628696930470444078018325177234584490178577) * 10 ^ 70 +
        9703201706505818694186930748776784386372884301276035717671759609814856) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 0 +
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
    rw [show 78 = 19 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (206 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_206 :
    recurrence2Scalar2Main.coeff 206 =
      (((874476997541895897076393514126786744509220265852681461053658079895 * 10 ^ 70 +
        3123058209442698098556778542315313571691540500346096376880876711105573) * 10 ^ 70 +
        5845043126717164832379663540481586263750206166325419760257920162197238) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 0 +
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
    rw [show 79 = 19 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (207 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_207 :
    recurrence2Scalar2Main.coeff 207 =
      -(((6966913257256878494847516467250014559735822100371906351594805324811 * 10 ^ 70 +
        6466636782534134710344793344521473607228669124311818121050067203663811) * 10 ^ 70 +
        5232250312687062901873931310828076568134182697170838946721582784280053) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 0 +
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
    rw [show 80 = 19 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (208 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_208 :
    recurrence2Scalar2Main.coeff 208 =
      (((22398316981636520477508719874176530500538988297842053949466795983087 * 10 ^ 70 +
        2237605341794425069257193641897857366247127961126248382681229248712009) * 10 ^ 70 +
        2360205885768694839150004277637106705327942538756348700324517305844491) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 0 +
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
    rw [show 81 = 19 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (209 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_209 :
    recurrence2Scalar2Main.coeff 209 =
      -(((52157025179579309729954019220602222661783765623320816825786242575343 * 10 ^ 70 +
        9784683951268080631143400348797305773747417891175092420634664854709880) * 10 ^ 70 +
        9423007788892553544209498833412620220847348219618401824154172978388727) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 0 +
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
    rw [show 82 = 19 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (210 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_210 :
    recurrence2Scalar2Main.coeff 210 =
      (((93809966824879548951314064131206031818552396935415725005274002724321 * 10 ^ 70 +
        6564853166087796878131821767055613964094724701452808174225517847066858) * 10 ^ 70 +
        7830954094519128464907069051333823486451307315217726136774028391362188) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 0 +
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
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (211 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_211 :
    recurrence2Scalar2Main.coeff 211 =
      -(((117985684555904281998903582437774123794735670153466693763366006177058 * 10 ^ 70 +
        9376466688256131763204368889067862380120007246793766929796956947105807) * 10 ^ 70 +
        1403546268369171462176073002118691877892030538912979717135094435882380) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 0 +
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
    rw [show 84 = 19 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (212 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_212 :
    recurrence2Scalar2Main.coeff 212 =
      (((28825674995447750842229553304296711889267866579477882339270041373701 * 10 ^ 70 +
        5231809578775670762656579821109479580312246362149600586867243276108144) * 10 ^ 70 +
        2273512914531441658044226690534265264964322670565364458057395578744035) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 0 +
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
    rw [show 85 = 19 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (213 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_213 :
    recurrence2Scalar2Main.coeff 213 =
      (((402543771420275385653109176598890397245784152856324604980408056178997 * 10 ^ 70 +
        4489633385670834565714226419687687572405519597176688126615009026819618) * 10 ^ 70 +
        2052468614225962951115074788620213624778273014213043292078616237993574) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 0 +
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
    rw [show 86 = 19 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (214 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_214 :
    recurrence2Scalar2Main.coeff 214 =
      -(((1630364296126719095068197515268451633084471650996436321829526020587727 * 10 ^ 70 +
        7168893313663347235035430221216908137969688942045302439000505915436957) * 10 ^ 70 +
        1457195702206812443086369207624910107981737699036487502296138682927295) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 0 +
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
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (215 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_215 :
    recurrence2Scalar2Main.coeff 215 =
      (((4431805637966150981492499505046989131394227571198189265866233740512096 * 10 ^ 70 +
        9740777355894467900166554226554600226087136054108234134199147166018631) * 10 ^ 70 +
        3859670923229620271962507464462711717928345093360291588411218799842707) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 0 +
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
    rw [show 88 = 19 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (216 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_216 :
    recurrence2Scalar2Main.coeff 216 =
      -(((9955764340208975306872182362673182805619844217224086314870740822492243 * 10 ^ 70 +
        4441035463412933173806075539036193190069507017994073602331723510434844) * 10 ^ 70 +
        8339512600961379630742561602899184372015794258591697603805869365836673) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 0 +
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
    rw [show 89 = 19 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (217 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_217 :
    recurrence2Scalar2Main.coeff 217 =
      ((((1 * 10 ^ 70 +
        9624764259384223647660641234771616055263185885182987175167494679657002) * 10 ^ 70 +
        9286791482739226642075799791060940294166067501940332823942546395305486) * 10 ^ 70 +
        6339221821026258153937938218491677098885171787242273126695255063512429) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 0 +
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
    rw [show 90 = 19 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (218 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_218 :
    recurrence2Scalar2Main.coeff 218 =
      -((((3 * 10 ^ 70 +
        4749528694256858977495872261620922242406836932679440565893431440386390) * 10 ^ 70 +
        9657947575112903419797738731196203207715882260912968040175099727293290) * 10 ^ 70 +
        2265642959017236810889433372581908123965496875831562438894777940823488) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 0 +
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
    rw [show 91 = 19 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (219 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_219 :
    recurrence2Scalar2Main.coeff 219 =
      ((((5 * 10 ^ 70 +
        5699622326685161213144765649838809117036952063937965144976954622445277) * 10 ^ 70 +
        5905942908379615401355698442609057582549995177123671843681078831514415) * 10 ^ 70 +
        0187485969929912184322586940735264138923480163207777969031801344018617) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 0 +
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
    rw [show 92 = 19 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (220 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_220 :
    recurrence2Scalar2Main.coeff 220 =
      -((((8 * 10 ^ 70 +
        0516097366352115151099629365912180683076323539605870747221322565128983) * 10 ^ 70 +
        3564778422221824766834446760215852792004367745652872631641574585768164) * 10 ^ 70 +
        7236831099762649337609543477637048217181570089072394966683180108849725) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 0 +
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
    rw [show 93 = 19 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (221 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_221 :
    recurrence2Scalar2Main.coeff 221 =
      ((((10 * 10 ^ 70 +
        2983499457315300938420602309771572656020340509883746633657724855835271) * 10 ^ 70 +
        6961846093982971140794570647247510047989835540635280503398018672121022) * 10 ^ 70 +
        0455761025282503462143781809839068373587779254782384852732223956509967) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 0 +
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
    rw [show 94 = 19 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (222 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_222 :
    recurrence2Scalar2Main.coeff 222 =
      -((((11 * 10 ^ 70 +
        0408837454530057500573129022190229494210049076767805782119984610499921) * 10 ^ 70 +
        0387734200662171542112943054081554538286822198400648852251341723473454) * 10 ^ 70 +
        2197711159443090630359005677742104473617816391358150079573350461295266) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 0 +
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
    rw [show 95 = 19 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (223 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_223 :
    recurrence2Scalar2Main.coeff 223 =
      ((((8 * 10 ^ 70 +
        1654059390482931250444552730627892000905525731142782615825178989473927) * 10 ^ 70 +
        5726837374514115422457234374573163552300580173697680911035536806584835) * 10 ^ 70 +
        2019600663991007799579101493577033990441861437704928580226270313073538) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 0 +
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
    rw [show 96 = 19 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (224 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_224 :
    recurrence2Scalar2Main.coeff 224 =
      ((((1 * 10 ^ 70 +
        3746179357205959697284229155194465405893301574180522424375233459182385) * 10 ^ 70 +
        4564745259593609736813770237594616888871203755322095635640106339747462) * 10 ^ 70 +
        2622739319563425235592588742386002261578280990397187592206164480107926) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 0 +
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
    rw [show 97 = 19 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (225 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_225 :
    recurrence2Scalar2Main.coeff 225 =
      -((((21 * 10 ^ 70 +
        4405784520472290980190774701979084668190548408251243535979528580329924) * 10 ^ 70 +
        2547110007171082423805993769356106278777285497348343462757054566346295) * 10 ^ 70 +
        0957654368749663311489398319170742532987678871441339928522662533662030) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 0 +
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
    rw [show 98 = 19 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (226 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_226 :
    recurrence2Scalar2Main.coeff 226 =
      ((((56 * 10 ^ 70 +
        3008668536872346447911447092349502775864836141602747107820190168372166) * 10 ^ 70 +
        0347347945732227054118770647295674276086374193857745537927099593220054) * 10 ^ 70 +
        0339884595933225288492386483879787065266997907519258552725683969858993) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 0 +
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
    rw [show 99 = 19 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (227 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_227 :
    recurrence2Scalar2Main.coeff 227 =
      -((((109 * 10 ^ 70 +
        9002734832082889153577632784833927412409733422605619955469416141014171) * 10 ^ 70 +
        9057614627310388356111791116548761118374379559581866852437903881665619) * 10 ^ 70 +
        5571704201728328711878640402341928652850301111547123887278013862074661) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 0 +
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
    rw [show 100 = 19 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (228 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_228 :
    recurrence2Scalar2Main.coeff 228 =
      ((((184 * 10 ^ 70 +
        8608566619885904207915358127991288239559542329319062249775172765761855) * 10 ^ 70 +
        9476918285989048144103963257120479502466782028424417977907126638350396) * 10 ^ 70 +
        6497422558174317670845663354582612059903999608210168281283493758571749) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 0 +
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
    rw [show 101 = 19 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (229 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_229 :
    recurrence2Scalar2Main.coeff 229 =
      -((((281 * 10 ^ 70 +
        3745967789596369050254876118680592579791628088883448683850888321977295) * 10 ^ 70 +
        5864605155484600582581137520018214463635516464475843908341328294472162) * 10 ^ 70 +
        1442395261277495371291331595364805685174570783741314512975069301098599) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 0 +
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
    rw [show 102 = 19 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (230 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_230 :
    recurrence2Scalar2Main.coeff 230 =
      ((((396 * 10 ^ 70 +
        2423973454234374329583667149116870227974622213783121702823967366802765) * 10 ^ 70 +
        6142606913596297778298540433566443565918985275287400121449887391968615) * 10 ^ 70 +
        1159701641078223510201078998226770224385855332152645210761007557023902) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 0 +
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
    rw [show 103 = 19 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (231 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_231 :
    recurrence2Scalar2Main.coeff 231 =
      -((((522 * 10 ^ 70 +
        3587821426002001437046456390520251140733397583143215902488876556307154) * 10 ^ 70 +
        9817802072912582847932550379941030653488402497014487783746495183780177) * 10 ^ 70 +
        1867958985685304387762618536763231290678158741475420209183732860209744) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 0 +
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
    rw [show 104 = 19 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (232 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_232 :
    recurrence2Scalar2Main.coeff 232 =
      ((((648 * 10 ^ 70 +
        9057628230206691892878878680389891612419303759067733144901221638447792) * 10 ^ 70 +
        8924781807777457204852660493910318843585783206063885319782475030991261) * 10 ^ 70 +
        5450528752149641927577217593569654922167738033927124888358005524182014) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 0 +
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
    rw [show 105 = 19 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (233 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_233 :
    recurrence2Scalar2Main.coeff 233 =
      -((((762 * 10 ^ 70 +
        3923049801531545759462514764550691055199372833483924008487645674852979) * 10 ^ 70 +
        2869164561739028970574494147431504073430177949576942138775535511681359) * 10 ^ 70 +
        0074895818420596810501190244633263554489762866454830758269646473745195) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 0 +
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
    rw [show 106 = 19 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
