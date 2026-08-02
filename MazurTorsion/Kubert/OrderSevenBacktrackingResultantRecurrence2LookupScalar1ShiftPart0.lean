/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B0_coeff_0
  recurrence2B0_coeff_1
  recurrence2B0_coeff_2
  recurrence2B0_coeff_3
  recurrence2B0_coeff_4
  recurrence2B0_coeff_5
  recurrence2B0_coeff_6
  recurrence2B0_coeff_7
  recurrence2B0_coeff_8
  recurrence2B0_coeff_9
  recurrence2B0_coeff_10
  recurrence2B0_coeff_11
  recurrence2B0_coeff_12
  recurrence2B0_coeff_13
  recurrence2B0_coeff_14
  recurrence2B0_coeff_15
  recurrence2B0_coeff_16
  recurrence2B0_coeff_17
  recurrence2B0_coeff_18
  recurrence2B0_coeff_19
  recurrence2B0_coeff_20
  recurrence2B0_coeff_21
  recurrence2B0_coeff_22
  recurrence2B0_coeff_23
  recurrence2B0_coeff_24
  recurrence2B0_coeff_25
  recurrence2B0_coeff_26
  recurrence2B0_coeff_27
  recurrence2B0_coeff_28
  recurrence2B0_coeff_29
  recurrence2B0_coeff_30
  recurrence2B0_coeff_31
  recurrence2B0_coeff_32
  recurrence2B0_coeff_33
  recurrence2B0_coeff_34
  recurrence2B0_coeff_35
  recurrence2B0_coeff_36
  recurrence2B0_coeff_37
  recurrence2B0_coeff_38
  recurrence2B0_coeff_39
  recurrence2B0_coeff_40
  recurrence2B0_coeff_41
  recurrence2B0_coeff_42
  recurrence2B0_coeff_43
  recurrence2B0_coeff_44
  recurrence2B0_coeff_45
  recurrence2B0_coeff_46
  recurrence2B0_coeff_47
  recurrence2B0_coeff_48
  recurrence2B0_coeff_49
  recurrence2B0_coeff_50
  recurrence2B0_coeff_51
  recurrence2B0_coeff_52
  recurrence2B0_coeff_53
  recurrence2B0_coeff_54
  recurrence2B0_coeff_55
  recurrence2B0_coeff_56
  recurrence2B0_coeff_57
  recurrence2B0_coeff_58
  recurrence2B0_coeff_59
  recurrence2B0_coeff_60
  recurrence2B0_coeff_61
  recurrence2B0_coeff_62
  recurrence2B0_coeff_63
  recurrence2B0_coeff_64
  recurrence2B0_coeff_65
  recurrence2B0_coeff_66
  recurrence2B0_coeff_67
  recurrence2B0_coeff_68
  recurrence2B0_coeff_69
  recurrence2B0_coeff_70
  recurrence2B0_coeff_71
  recurrence2B0_coeff_72
  recurrence2B0_coeff_73
  recurrence2B0_coeff_74
  recurrence2B0_coeff_75
  recurrence2B0_coeff_76
  recurrence2B0_coeff_77
  recurrence2B0_coeff_78
  recurrence2B0_coeff_79
  recurrence2B0_coeff_80
  recurrence2B0_coeff_81
  recurrence2B0_coeff_82
  recurrence2B0_coeff_83
  recurrence2B0_coeff_84
  recurrence2B0_coeff_85
  recurrence2B0_coeff_86
  recurrence2B0_coeff_87
  recurrence2B0_coeff_88
  recurrence2B0_coeff_89
  recurrence2B0_coeff_90
  recurrence2B0_coeff_91
  recurrence2B0_coeff_92
  recurrence2B0_coeff_93
  recurrence2B0_coeff_94
  recurrence2B0_coeff_95
  recurrence2B0_coeff_96
  recurrence2B0_coeff_97
  recurrence2B0_coeff_98
  recurrence2B0_coeff_99
  recurrence2B0_coeff_100
  recurrence2B0_coeff_101
  recurrence2B0_coeff_102
  recurrence2B0_coeff_103
  recurrence2B0_coeff_104
  recurrence2B0_coeff_105
  recurrence2B0_coeff_106
  recurrence2B0_coeff_107
  recurrence2B0_coeff_108
  recurrence2B0_coeff_109
  recurrence2B0_coeff_110
  recurrence2B0_coeff_111
  recurrence2B0_coeff_112
  recurrence2B0_coeff_113
  recurrence2B0_coeff_114
  recurrence2B0_coeff_115
  recurrence2B0_coeff_116
  recurrence2B0_coeff_117
  recurrence2B0_coeff_118
  recurrence2B0_coeff_119
  recurrence2B0_coeff_120
  recurrence2B0_coeff_121
  recurrence2B0_coeff_122
  recurrence2B0_coeff_123
  recurrence2B0_coeff_124
  recurrence2B0_coeff_125
  recurrence2B0_coeff_126
  recurrence2B0_coeff_127
  recurrence2B0_coeff_128
  recurrence2B0_coeff_129
  recurrence2B0_coeff_130
  recurrence2B0_coeff_131
  recurrence2B0_coeff_132
  recurrence2B0_coeff_133
  recurrence2B0_coeff_134
  recurrence2B0_coeff_135
  recurrence2B0_coeff_136
  recurrence2B0_coeff_137
  recurrence2B0_coeff_138
  recurrence2B0_coeff_139
  recurrence2B0_coeff_140
  recurrence2B0_coeff_141
  recurrence2B0_coeff_142
  recurrence2B0_coeff_143
  recurrence2B0_coeff_144
  recurrence2B0_coeff_145
  recurrence2B0_coeff_146
  recurrence2B0_coeff_147
  recurrence2B0_coeff_148
  recurrence2B0_coeff_149
  recurrence2B0_coeff_150
  recurrence2B0_coeff_151
  recurrence2B0_coeff_152
  recurrence2B0_coeff_153
  recurrence2B0_coeff_154
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

theorem recurrence2Scalar1Shift_coeff_0 :
    recurrence2Scalar1Shift.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_1 :
    recurrence2Scalar1Shift.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_2 :
    recurrence2Scalar1Shift.coeff 2 =
      (310272 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_3 :
    recurrence2Scalar1Shift.coeff 3 =
      (-6866834496 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_4 :
    recurrence2Scalar1Shift.coeff 4 =
      (3301698573280 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_5 :
    recurrence2Scalar1Shift.coeff 5 =
      (-157209563968245296 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_6 :
    recurrence2Scalar1Shift.coeff 6 =
      (-34566550554750265888 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_7 :
    recurrence2Scalar1Shift.coeff 7 =
      (-249403642765872182157796 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_8 :
    recurrence2Scalar1Shift.coeff 8 =
      (89513508338739205290862424 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_9 :
    recurrence2Scalar1Shift.coeff 9 =
      (316325674088117056455931867200 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_10 :
    recurrence2Scalar1Shift.coeff 10 =
      (-372490779550000886685339682747424 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_11 :
    recurrence2Scalar1Shift.coeff 11 =
      (372795893081886650774080689901566990 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_12 :
    recurrence2Scalar1Shift.coeff 12 =
      (-222377956789602437579628603374495212282 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_13 :
    recurrence2Scalar1Shift.coeff 13 =
      (99072812274473847370415218597039746529486 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_14 :
    recurrence2Scalar1Shift.coeff 14 =
      (-33198643442823568803678315832753725913884842 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_15 :
    recurrence2Scalar1Shift.coeff 15 =
      (8540677074655333025373585360047698552893321976 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_16 :
    recurrence2Scalar1Shift.coeff 16 =
      (-1710244370752074889351392740020446233616941350651 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_17 :
    recurrence2Scalar1Shift.coeff 17 =
      (266475970836653330278873331416923010225479565615929 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_18 :
    recurrence2Scalar1Shift.coeff 18 =
      (-31897755067622523273779025332598011049108736249168391 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_19 :
    recurrence2Scalar1Shift.coeff 19 =
      (2800177202746573673417872620170003096390316349650946475 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_20 :
    recurrence2Scalar1Shift.coeff 20 =
      (-152341070862629074652108250356021926048215302748603238234 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_21 :
    recurrence2Scalar1Shift.coeff 21 =
      (-189295366011196310703322064060571596507865186739543371019 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_22 :
    recurrence2Scalar1Shift.coeff 22 =
      (1088100020612692787628393358779132340220145897181105822060314 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_23 :
    recurrence2Scalar1Shift.coeff 23 =
      (-137452864656509020609995123083424574956280481926876498927786434 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_24 :
    recurrence2Scalar1Shift.coeff 24 =
      (10910501380298811619547857112509382305333785793948384239497132443 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_25 :
    recurrence2Scalar1Shift.coeff 25 =
      (-641522909976205280116565258503107046061775566874221906111459382189 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_26 :
    recurrence2Scalar1Shift.coeff 26 =
      (29295893435972361988600906025709009428130261093895160524565063184551 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_27 :
    recurrence2Scalar1Shift.coeff 27 =
      (-1041573125066530888870503038547401171107579240330131698895596635717477 : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_28 :
    recurrence2Scalar1Shift.coeff 28 =
      ((2 * 10 ^ 70 +
        6261461370089742043635113773989539527411889514403019027918930382386887) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_29 :
    recurrence2Scalar1Shift.coeff 29 =
      -((15 * 10 ^ 70 +
        1287054266642265859348991329016441618509637402882256524586201100554610) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_30 :
    recurrence2Scalar1Shift.coeff 30 =
      -((3516 * 10 ^ 70 +
        4440875009044024215913698170125293867901983766510207191896457897482197) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_31 :
    recurrence2Scalar1Shift.coeff 31 =
      ((288390 * 10 ^ 70 +
        8880027394503544831645826681843079584897983058530796230034166915221128) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_32 :
    recurrence2Scalar1Shift.coeff 32 =
      -((14769219 * 10 ^ 70 +
        3561945119309785318835171320727241615311189126782062987280282195958143) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_33 :
    recurrence2Scalar1Shift.coeff 33 =
      ((570280754 * 10 ^ 70 +
        2895547748191864917367320239815505911029582714161000289179597400269294) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_34 :
    recurrence2Scalar1Shift.coeff 34 =
      -((17557712891 * 10 ^ 70 +
        2369612584485065888352434869254849795328003331712360790430078852089391) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_35 :
    recurrence2Scalar1Shift.coeff 35 =
      ((452342013583 * 10 ^ 70 +
        5733308910892091662080742162611341349659145502917429997442374360670395) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_36 :
    recurrence2Scalar1Shift.coeff 36 =
      -((10179235767776 * 10 ^ 70 +
        5391936638865779556377009200855764563555130948941493692598739915577051) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_37 :
    recurrence2Scalar1Shift.coeff 37 =
      ((183552008339327 * 10 ^ 70 +
        3321316601135416532763268374626392220219616865934823500389349613808069) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_38 :
    recurrence2Scalar1Shift.coeff 38 =
      -((713440619932174 * 10 ^ 70 +
        6268391268645163137678554374960931064512005679238930410978223194810538) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_39 :
    recurrence2Scalar1Shift.coeff 39 =
      -((140188660480466882 * 10 ^ 70 +
        8198495878332298428091514052519511506114338982364369974825332194236112) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_40 :
    recurrence2Scalar1Shift.coeff 40 =
      ((7306839524128138168 * 10 ^ 70 +
        3037094584868156125203113939858931704764563247057941326589966659819363) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_41 :
    recurrence2Scalar1Shift.coeff 41 =
      -((199221138055599059482 * 10 ^ 70 +
        7728630948956195278623636556164724747521849069444177385734570479153437) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_42 :
    recurrence2Scalar1Shift.coeff 42 =
      ((2677086746877060489470 * 10 ^ 70 +
        3026650683325077984735989127845025554272834482972376592340660517059271) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_43 :
    recurrence2Scalar1Shift.coeff 43 =
      ((13192405069247114415627 * 10 ^ 70 +
        1648517202744194544594004479764640018611760299491922499534737263155468) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_44 :
    recurrence2Scalar1Shift.coeff 44 =
      -((835223600526687886668425 * 10 ^ 70 +
        6822687802852614930121246273588543037203284071133188320166623593506131) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_45 :
    recurrence2Scalar1Shift.coeff 45 =
      -((34200012386365938633505959 * 10 ^ 70 +
        6457251568159248705688947860740498644469880234946669986993232163918306) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_46 :
    recurrence2Scalar1Shift.coeff 46 =
      ((3487865850356737376224311507 * 10 ^ 70 +
        3690758043909801650095672804948389266301460395401778549289123068197318) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_47 :
    recurrence2Scalar1Shift.coeff 47 =
      -((153659779165619195206424596542 * 10 ^ 70 +
        6899598411917749053791055239225363169872415710855504996740770938978496) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_48 :
    recurrence2Scalar1Shift.coeff 48 =
      ((4848206478995394982977548089404 * 10 ^ 70 +
        3449361556525779753821851434716882305192009700052207700504056194369286) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_49 :
    recurrence2Scalar1Shift.coeff 49 =
      -((124915378857288797755717459933772 * 10 ^ 70 +
        6145990706121762393921508076072630782667253338953394318584114266906575) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_50 :
    recurrence2Scalar1Shift.coeff 50 =
      ((2805631168687125232365121677499277 * 10 ^ 70 +
        6434758887385890302338705033731794676104083585937605454581187369473133) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_51 :
    recurrence2Scalar1Shift.coeff 51 =
      -((57156429309304650295068094085245047 * 10 ^ 70 +
        3532373628157559210224386330251159957048561917965734984371658402019377) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_52 :
    recurrence2Scalar1Shift.coeff 52 =
      ((1079188566744736918577494474254051127 * 10 ^ 70 +
        3619215521474620637285441381494246027250774188039699663635557507322354) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_53 :
    recurrence2Scalar1Shift.coeff 53 =
      -((18990079485225826434322841613952727548 * 10 ^ 70 +
        6270918870252177856306772192540389706033894342726442649061759960425548) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_54 :
    recurrence2Scalar1Shift.coeff 54 =
      ((309371884823064943751440417842198606756 * 10 ^ 70 +
        2755491489631419157448613059413587878956658401845132436107511034847794) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_55 :
    recurrence2Scalar1Shift.coeff 55 =
      -((4602327557933323746287277946055904408226 * 10 ^ 70 +
        0816670028153416408218242610329845208274780963621994769061317986584041) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_56 :
    recurrence2Scalar1Shift.coeff 56 =
      ((61318116980479740961055042524447734701806 * 10 ^ 70 +
        6011812801788875210430964775210577054329341058991694287904034432764405) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_57 :
    recurrence2Scalar1Shift.coeff 57 =
      -((707877594219969798667355657598150304434817 * 10 ^ 70 +
        8679915615843288267764092378577811654440248531885520550950158725296430) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_58 :
    recurrence2Scalar1Shift.coeff 58 =
      ((6495991853711933893039540561304751079042835 * 10 ^ 70 +
        8782422695153023815920226217462531273968598740604944172529023756009038) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_59 :
    recurrence2Scalar1Shift.coeff 59 =
      -((30376236357116347703393674023759593653040195 * 10 ^ 70 +
        9077028013270051298877696543826897221093644473261781361120383914034705) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_60 :
    recurrence2Scalar1Shift.coeff 60 =
      -((523160304047700903141563236460864604811177103 * 10 ^ 70 +
        7820371325069923599757495817755669523599872338571749496671213785169425) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_61 :
    recurrence2Scalar1Shift.coeff 61 =
      ((21201267895698468152471958909260270472966212445 * 10 ^ 70 +
        8659253776492061737073564725562329411581866787302770412147883745917308) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_62 :
    recurrence2Scalar1Shift.coeff 62 =
      -((490999208553871705280071135488820063119923352284 * 10 ^ 70 +
        7569133155027765721521190272474755147765061869338192423987735000813603) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_63 :
    recurrence2Scalar1Shift.coeff 63 =
      ((9458139530926474129365397973780746754247129735638 * 10 ^ 70 +
        8557956510765371469076122914583427617611691323130853472125069942344114) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_64 :
    recurrence2Scalar1Shift.coeff 64 =
      -((164213972132964289993249183450770054941261534740500 * 10 ^ 70 +
        3661776946926935292020440390447166652785112139768339105260831291018676) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_65 :
    recurrence2Scalar1Shift.coeff 65 =
      ((2642814419557762756884623856162312561639794218237905 * 10 ^ 70 +
        4116574624389366037444714988091312650786402991121598370303546272853580) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_66 :
    recurrence2Scalar1Shift.coeff 66 =
      -((39905269450141166163421522087843003726836431005362728 * 10 ^ 70 +
        3695364205920454998286722979376675825636617113674491307796897462230084) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_67 :
    recurrence2Scalar1Shift.coeff 67 =
      ((568835666743448699532174744424211010955463291139786377 * 10 ^ 70 +
        7628142440464721832462072196362698177512111061890426579268282124058532) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_68 :
    recurrence2Scalar1Shift.coeff 68 =
      -((7682314737165241710988684850950495368197309015458386288 * 10 ^ 70 +
        4650561220690328476814718682706895486721264444364199347033987639863961) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_69 :
    recurrence2Scalar1Shift.coeff 69 =
      ((98513563814887818235877280781885739299025388504505517063 * 10 ^ 70 +
        1978149499379589725158273376249061374441825333148318264270956734861338) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_70 :
    recurrence2Scalar1Shift.coeff 70 =
      -((1201128939228146987605110369842390756856409098838420195641 * 10 ^ 70 +
        1982781463159673907578266453225603986459548864757820702567039791883760) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_71 :
    recurrence2Scalar1Shift.coeff 71 =
      ((13937141619163117337225821840652100031839282686700825912169 * 10 ^ 70 +
        5021828651037300688476982435571359061619953324208567921371275445514735) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_72 :
    recurrence2Scalar1Shift.coeff 72 =
      -((154024007754331658633161706356742072797665376906763152072855 * 10 ^ 70 +
        1999046455958316796728330058702162114528616157664056397145972335972476) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_73 :
    recurrence2Scalar1Shift.coeff 73 =
      ((1622542674366702412967520443906098599153676137414703656322803 * 10 ^ 70 +
        9240066266458848257618691133410396591156423544993188546351718371090331) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_74 :
    recurrence2Scalar1Shift.coeff 74 =
      -((16308434271361053750318107751008868888638622146319240153840685 * 10 ^ 70 +
        6671931033312019544869430521397611888923915597613122855085559596736497) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_75 :
    recurrence2Scalar1Shift.coeff 75 =
      ((156564523123171634046093697860308613227269468503735395528144565 * 10 ^ 70 +
        4564442054791121112067911488261716278313552433968242025997884219595299) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_76 :
    recurrence2Scalar1Shift.coeff 76 =
      -((1437151280980505771464293743749454552692909285217545768661034003 * 10 ^ 70 +
        3073003551053707246872046796536705098000584372131757385185950654063964) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_77 :
    recurrence2Scalar1Shift.coeff 77 =
      ((12626243658982935853367534969424024919397700939916055350369077950 * 10 ^ 70 +
        8053276391910442901051577959912161592869226066836109364035328301336187) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_78 :
    recurrence2Scalar1Shift.coeff 78 =
      -((106265957145959510785128762301524213476504073102585083889201221895 * 10 ^ 70 +
        9108697304233680162054571739292583322840246905541858655294869481250160) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_79 :
    recurrence2Scalar1Shift.coeff 79 =
      ((857430627240706556484671389161169950045554040399604208704149832814 * 10 ^ 70 +
        0361290687820909652960185820389069156733406084448128777330476607317696) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_80 :
    recurrence2Scalar1Shift.coeff 80 =
      -((6637275967864751432642307909390076953443586525517241237693484488539 * 10 ^ 70 +
        5225971741128473253119893504853305658654827474509217433799255453107689) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_81 :
    recurrence2Scalar1Shift.coeff 81 =
      ((49323065680198931510216066423162911361932253647007125635483547310022 * 10 ^ 70 +
        6079699374049331387272611679530558785341007258493118151547942925974374) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_82 :
    recurrence2Scalar1Shift.coeff 82 =
      -((352091177717691747367356570624584762267847265398291957597876910273265 * 10 ^ 70 +
        6517975709224833825584647941944289661604386042687140881661042163526437) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_83 :
    recurrence2Scalar1Shift.coeff 83 =
      ((2415854132369087613604366291870847022470528178110128730987110502540403 * 10 ^ 70 +
        1806020926554379316727145591370056908409266919296076925097812725192158) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_84 :
    recurrence2Scalar1Shift.coeff 84 =
      -(((1 * 10 ^ 70 +
        5941847075750540278461636292256730854945145385998618644752971366397957) * 10 ^ 70 +
        6854821059568194919604490855840371591263601399775204624269500018343917) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_85 :
    recurrence2Scalar1Shift.coeff 85 =
      (((10 * 10 ^ 70 +
        1218259132280503187157427037842149549240012813504479607716564333991609) * 10 ^ 70 +
        1456722631946566106081084150439551575216749690264426391963388057149072) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_86 :
    recurrence2Scalar1Shift.coeff 86 =
      -(((61 * 10 ^ 70 +
        8551348818087722419334777507516637704071295493471744877255328654439906) * 10 ^ 70 +
        4495330997879716947839192813184721780417591026811148062355106876969372) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_87 :
    recurrence2Scalar1Shift.coeff 87 =
      (((363 * 10 ^ 70 +
        8953460982193594361496166857536094865232481802817417927668217567487496) * 10 ^ 70 +
        5116010387689510562166121752294014851155635908431062138003116635984065) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_88 :
    recurrence2Scalar1Shift.coeff 88 =
      -(((2061 * 10 ^ 70 +
        1190641101727948108027794663826591442480565346681503476110783444296133) * 10 ^ 70 +
        4686986289786672600976517605001199423759893554356132364590787637974382) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_89 :
    recurrence2Scalar1Shift.coeff 89 =
      (((11240 * 10 ^ 70 +
        1468903513908936368985292179390482346732652821021776792482059093216484) * 10 ^ 70 +
        3363079492988062225346696415878577286416736551052747812338928798350025) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_90 :
    recurrence2Scalar1Shift.coeff 90 =
      -(((59018 * 10 ^ 70 +
        5849668081271386330558822756784665164369460421017975925744361140284291) * 10 ^ 70 +
        9011821135683726481977910690702346038801568924514457785799036598093793) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_91 :
    recurrence2Scalar1Shift.coeff 91 =
      (((298361 * 10 ^ 70 +
        0374117681494643982844778200168321202032206578622106728527494174395824) * 10 ^ 70 +
        7049493312145709565653917184495782462391211283236724558605895521915851) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_92 :
    recurrence2Scalar1Shift.coeff 92 =
      -(((1451997 * 10 ^ 70 +
        4398548908494021534384444623809363487422606982348111613057213605645487) * 10 ^ 70 +
        6794328762429849053561434626414952700354871544600814425319877245324938) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_93 :
    recurrence2Scalar1Shift.coeff 93 =
      (((6799411 * 10 ^ 70 +
        3330144005163362377417756100280565572553719542220554199608393628816124) * 10 ^ 70 +
        7216082544411951851202378240147394635073930298156983561417571653451396) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_94 :
    recurrence2Scalar1Shift.coeff 94 =
      -(((30610358 * 10 ^ 70 +
        6571956714602526691549735553815811323808441345327174049973894195029650) * 10 ^ 70 +
        2309981055555251488819650490462645416723454661650931604394989425635766) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_95 :
    recurrence2Scalar1Shift.coeff 95 =
      (((132284928 * 10 ^ 70 +
        9596718529236243766972080232782735332279912389066026763341173167115722) * 10 ^ 70 +
        0693875858657572237969267013873249086070584776757701276526290947896473) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_96 :
    recurrence2Scalar1Shift.coeff 96 =
      -(((547640838 * 10 ^ 70 +
        0544732517087077487427788723416142705616726418184659851743851556356731) * 10 ^ 70 +
        6054401350773017058542049125907460326905667413505459700978138056652825) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_97 :
    recurrence2Scalar1Shift.coeff 97 =
      (((2166385111 * 10 ^ 70 +
        8042603644074078134166522768373392476525080053949593950804813150051823) * 10 ^ 70 +
        3633344612381209507497735436930085470653980346654123769789213114405778) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_98 :
    recurrence2Scalar1Shift.coeff 98 =
      -(((8166365327 * 10 ^ 70 +
        1378507047584990868730449474990982067202742218220727669939189442590554) * 10 ^ 70 +
        6098257837904697283938073780100466966432669829226837302119767659143304) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_99 :
    recurrence2Scalar1Shift.coeff 99 =
      (((29240403716 * 10 ^ 70 +
        7770549406675395882169984377354937998907166203475477736353916790391220) * 10 ^ 70 +
        3781912835043890653405249808923840337765045592281744172414059412079179) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_100 :
    recurrence2Scalar1Shift.coeff 100 =
      -(((98957608475 * 10 ^ 70 +
        1568886910989372146316349538425428421575907487645861928972692199894747) * 10 ^ 70 +
        9192287232234717861245840764856416990039740815156694323206778053271339) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_101 :
    recurrence2Scalar1Shift.coeff 101 =
      (((313226212363 * 10 ^ 70 +
        2966057663349874423927735439610734130088054840118914807369652203523355) * 10 ^ 70 +
        3267269080410976683184840542881288454507269876720607900911174263550027) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_102 :
    recurrence2Scalar1Shift.coeff 102 =
      -(((904087163858 * 10 ^ 70 +
        4465625880615351091008149376594267747105622394089850921256797547241528) * 10 ^ 70 +
        6311355605943005784218755578979208006792689055014174792838027512874145) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_103 :
    recurrence2Scalar1Shift.coeff 103 =
      (((2228923234140 * 10 ^ 70 +
        9495147304025455585765011644050138363160214791253966113750931535510884) * 10 ^ 70 +
        2565758326010184522463657042915574720592074715832236269358379287815450) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_104 :
    recurrence2Scalar1Shift.coeff 104 =
      -(((3747529266135 * 10 ^ 70 +
        0602983601610667259879974685238620198551244486054482610863928207215983) * 10 ^ 70 +
        6559294789969998926543641951811319756472454384917464445012465070708908) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_105 :
    recurrence2Scalar1Shift.coeff 105 =
      -(((2335843247938 * 10 ^ 70 +
        9434652438604794242468972253170337395133168893981367973391243120293167) * 10 ^ 70 +
        1537360853464236648830428684786707414091790719706507844015099815915490) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_106 :
    recurrence2Scalar1Shift.coeff 106 =
      (((57266112503370 * 10 ^ 70 +
        9691368597031589513544373518130999056220002268021256968777491444303076) * 10 ^ 70 +
        4800600479730960499975667621282376585730576062433196704142408347836292) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_107 :
    recurrence2Scalar1Shift.coeff 107 =
      -(((315446315670737 * 10 ^ 70 +
        9567483376825740758555964023556599537731800599905013304598605974024784) * 10 ^ 70 +
        1418184871678136647581355087662507829938485242546673865201015292120251) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_108 :
    recurrence2Scalar1Shift.coeff 108 =
      (((1222241170663195 * 10 ^ 70 +
        0549700776141098076776943479063714127917597642509714909057816389535652) * 10 ^ 70 +
        1998282885686938753553824787955790415805480055103615301626086881405719) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_109 :
    recurrence2Scalar1Shift.coeff 109 =
      -(((3854002500506184 * 10 ^ 70 +
        7632536773881844611067177056150013803561192196273699368855940823639931) * 10 ^ 70 +
        0066962790544456548364719821810812367603677066545523516163830624198782) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_110 :
    recurrence2Scalar1Shift.coeff 110 =
      (((11469577877298175 * 10 ^ 70 +
        0511336586383305254482526735184555513038161592014230892448376203690707) * 10 ^ 70 +
        8668156322470748965511932494039299706562933868372892576605032771917270) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_111 :
    recurrence2Scalar1Shift.coeff 111 =
      -(((42573573053180606 * 10 ^ 70 +
        4112167809481008665175647167820952230897965130890339526666454987854799) * 10 ^ 70 +
        8605077345892666414958426940230898175721197038494372062780055553973196) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_112 :
    recurrence2Scalar1Shift.coeff 112 =
      (((215058905187210283 * 10 ^ 70 +
        7733293231636087297163062659087748103660479996557976196292977842570001) * 10 ^ 70 +
        2240280018062099542057937765395060387980768625086896607137603729078459) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_113 :
    recurrence2Scalar1Shift.coeff 113 =
      -(((1110231886146950343 * 10 ^ 70 +
        4398610096748780974928907809054134846540886494626839050110271256162402) * 10 ^ 70 +
        4576267775643276850070440379105656898072684025780696937994973511611385) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_114 :
    recurrence2Scalar1Shift.coeff 114 =
      (((4578912041511971572 * 10 ^ 70 +
        2582412658622681987678009712087615979141018029632442085705965612540266) * 10 ^ 70 +
        2989234066351841133795185019369068932869410014481388926230161116316446) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_115 :
    recurrence2Scalar1Shift.coeff 115 =
      -(((11690424970296180441 * 10 ^ 70 +
        7686929997028907031613533200091386261868004725961826653733193857926515) * 10 ^ 70 +
        3051768664397982726056983745549491058190755408287866149446841884983694) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_116 :
    recurrence2Scalar1Shift.coeff 116 =
      -(((6267938745199328500 * 10 ^ 70 +
        2057725279753823493123878350009475224790072287145348487614509347737824) * 10 ^ 70 +
        3562261853430134200207493144415940823127641457885150851159300761828962) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_117 :
    recurrence2Scalar1Shift.coeff 117 =
      (((246019974802014982550 * 10 ^ 70 +
        0146481168759269786327246000327126462981995235568921825456617277950075) * 10 ^ 70 +
        9376100424628956324037044840100567371552825263777165563532242397028006) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_118 :
    recurrence2Scalar1Shift.coeff 118 =
      -(((1361181933419323173137 * 10 ^ 70 +
        0730468335878609284644558212511920193585871811471293092266199881550764) * 10 ^ 70 +
        3244040813408453621011003627122168280120846654735205954719634030419828) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_119 :
    recurrence2Scalar1Shift.coeff 119 =
      (((3744110856050672450493 * 10 ^ 70 +
        0818777427373720693092262710923859948582105615460975678792748655223547) * 10 ^ 70 +
        0719655471471368657932093913403889634604334508288534452527791777388428) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_120 :
    recurrence2Scalar1Shift.coeff 120 =
      (((1106507744134741454055 * 10 ^ 70 +
        1349583227441607753741732943063268599519904356927404010172538331533371) * 10 ^ 70 +
        9799663197225292479070043454204950005787131169614917548335415950529624) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_121 :
    recurrence2Scalar1Shift.coeff 121 =
      -(((66932990277988467052704 * 10 ^ 70 +
        9871548065955543374138210610804474660315223493994507187235494242724988) * 10 ^ 70 +
        8711146877043089138827754082835857848855374470805445962991121919940730) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_122 :
    recurrence2Scalar1Shift.coeff 122 =
      (((368370309155950935349325 * 10 ^ 70 +
        7728700381076253667990688312088278293607154642356348877523265437519861) * 10 ^ 70 +
        3239120251766289958143628376809931035215172533681351108468972513127036) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_123 :
    recurrence2Scalar1Shift.coeff 123 =
      -(((1125287765347765117456369 * 10 ^ 70 +
        4312275351821486148139014527396494969100043563166708684888506091175902) * 10 ^ 70 +
        7443482926032597361749429343146342148937335564648412948469228203882437) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_124 :
    recurrence2Scalar1Shift.coeff 124 =
      (((1126268980188048899661833 * 10 ^ 70 +
        0038420479297862428902591978860276860981842411926439558920579654562630) * 10 ^ 70 +
        6283580255098380942350413552011474282982101874119127206293781323154091) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_125 :
    recurrence2Scalar1Shift.coeff 125 =
      (((10257345217649689498314753 * 10 ^ 70 +
        0050582448219316117661372305589334878578273537615341526455149445392902) * 10 ^ 70 +
        8437761071046304105825706523399787045591956658268708008812349988833171) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_126 :
    recurrence2Scalar1Shift.coeff 126 =
      -(((80497864512720554306525465 * 10 ^ 70 +
        5224741640439317889307427366000623871362210576298114838158619869590806) * 10 ^ 70 +
        4319632169205973789099277713288579168550014721955731084153116838450424) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_127 :
    recurrence2Scalar1Shift.coeff 127 =
      (((331041432225520638251970768 * 10 ^ 70 +
        7912518633463427463281463616753214026860297957121683337948674846218779) * 10 ^ 70 +
        0372027849174816053989057136250504621135492914986579242037080597842928) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_128 :
    recurrence2Scalar1Shift.coeff 128 =
      -(((715163518158036124319752832 * 10 ^ 70 +
        7519774821480211387909498503018701944812191658136688112172873283321748) * 10 ^ 70 +
        7153149875066672481922115231169078238064382308517364345746227280102383) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_129 :
    recurrence2Scalar1Shift.coeff 129 =
      -(((835434174283137432488343193 * 10 ^ 70 +
        0445844464113391280877793824681725500993801371917350968244940575544112) * 10 ^ 70 +
        7113014952672510543831454291715485767303289827149772998317426663867288) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_130 :
    recurrence2Scalar1Shift.coeff 130 =
      (((13543639959294569738160756276 * 10 ^ 70 +
        6184305468856247364674852844453605772386944961875696215449469658460385) * 10 ^ 70 +
        8385863418621928494609876501027649661748774831751316719169597179850492) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_131 :
    recurrence2Scalar1Shift.coeff 131 =
      -(((51077990391366724495825390856 * 10 ^ 70 +
        4846546978277681967748594511386383273980165131413943761244608913251509) * 10 ^ 70 +
        6364156487286396086227502961529519093319946207004269906231727182425418) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_132 :
    recurrence2Scalar1Shift.coeff 132 =
      (((71358608537557488790685649835 * 10 ^ 70 +
        0299431931140737819289343349321257107986921963026896455547636871690222) * 10 ^ 70 +
        0560845606824140220132960732248989084919402490169008674183090470122083) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_133 :
    recurrence2Scalar1Shift.coeff 133 =
      (((77932576260329938820607988282 * 10 ^ 70 +
        2786874291012368138953016687899542459102086972846999509023383267887349) * 10 ^ 70 +
        2503244036639351930861975969830245060481767737296806073166288039611590) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_134 :
    recurrence2Scalar1Shift.coeff 134 =
      (((356864810624574323932437137918 * 10 ^ 70 +
        9733441442285804207446916015307161068711513946387520999960408390052079) * 10 ^ 70 +
        2480067267295300931793350843964398102024418146024173730617608717697956) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_135 :
    recurrence2Scalar1Shift.coeff 135 =
      -(((6864289430779536014953056497142 * 10 ^ 70 +
        2563318533377598110052185901385215190972176873784736850317206750200462) * 10 ^ 70 +
        8389008914019662886065870554958361069028722742554993572851219566695067) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_136 :
    recurrence2Scalar1Shift.coeff 136 =
      (((18784300281694937387659747677073 * 10 ^ 70 +
        8231867547854190482713069153909740980429680191683896933413222772779402) * 10 ^ 70 +
        9394542011273766365629996552267679044168455007691223025677100695860400) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_137 :
    recurrence2Scalar1Shift.coeff 137 =
      (((106943071162819328694161065393965 * 10 ^ 70 +
        3716374472995497559164677553326562689134072198588136747233382843761779) * 10 ^ 70 +
        7207739756975474164574346100101929905054781314167846881782005604533019) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_138 :
    recurrence2Scalar1Shift.coeff 138 =
      -(((1055514723677548783927262738496647 * 10 ^ 70 +
        5977300495419592252641919285334646805624902021267894865199248668242669) * 10 ^ 70 +
        6816454220968776280107905473870616638549703492368209312476095748895750) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_139 :
    recurrence2Scalar1Shift.coeff 139 =
      (((3365548612531011313458116509900139 * 10 ^ 70 +
        0527948166879241853502492280032313836965160446245781249372022582418476) * 10 ^ 70 +
        1820286785121438689095969034754040654960256714421084627455120526479798) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_140 :
    recurrence2Scalar1Shift.coeff 140 =
      (((1979946697721656440965277452607914 * 10 ^ 70 +
        7958939825014479409816931347807952851057087710809096347932418713335757) * 10 ^ 70 +
        9028912498954797081202038978337516755630912814018032343237071767842326) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_141 :
    recurrence2Scalar1Shift.coeff 141 =
      -(((60255272430276269558545368782646335 * 10 ^ 70 +
        3055417486853073197143020646405484233218715334539608512994593117829969) * 10 ^ 70 +
        8722896334538657407987507277291525276395721665647015365752202558038636) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_142 :
    recurrence2Scalar1Shift.coeff 142 =
      (((216362848521794426597593224899254110 * 10 ^ 70 +
        5892447177598909721111781388869788927177235290321638145953515280335760) * 10 ^ 70 +
        0288432346545850235929326570536973853139619848682323893467998916356275) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_143 :
    recurrence2Scalar1Shift.coeff 143 =
      -(((1585636123695715718619376617068871 * 10 ^ 70 +
        5660587061125081404067989887810250897521213471684532083372707776075557) * 10 ^ 70 +
        2239612352415920536428557780968707352588490153539600919253501774760826) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_144 :
    recurrence2Scalar1Shift.coeff 144 =
      -(((2884027893057669051477861938597859450 * 10 ^ 70 +
        2152036978502844563941889316774885502490893440637886450231349760689876) * 10 ^ 70 +
        0621439318756207790296467147724120947136622972119682771886539849305102) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_145 :
    recurrence2Scalar1Shift.coeff 145 =
      (((10122438055779914415031797231606787771 * 10 ^ 70 +
        3289028075157900737164693888990364921563538562158172423715486538495296) * 10 ^ 70 +
        3932065955317403957436070578553338414154306001050785032453708385473838) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_146 :
    recurrence2Scalar1Shift.coeff 146 =
      (((3715368566491658818855728175777934181 * 10 ^ 70 +
        5073330202408980522425314166489058978986122731768535103065834805207614) * 10 ^ 70 +
        1295130349398483365510246366201084098796579519141990862257418810132733) : ℚ) := by
  unfold recurrence2Scalar1Shift
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

theorem recurrence2Scalar1Shift_coeff_147 :
    recurrence2Scalar1Shift.coeff 147 =
      -(((149969431779396145123878755953368372551 * 10 ^ 70 +
        6911210905028671826452732551599446205449662512112996829010623869145033) * 10 ^ 70 +
        2477309660578302371001896041572274377286322271870709451184259786367707) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_148 :
    recurrence2Scalar1Shift.coeff 148 =
      (((476190878200581163417639713543955090219 * 10 ^ 70 +
        4755226333324277800582552611753601001981446042509630293659683787289559) * 10 ^ 70 +
        9944188695080332677552205907116667244981842615188162796015403665994856) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_149 :
    recurrence2Scalar1Shift.coeff 149 =
      (((323994943227364457659596897693063286725 * 10 ^ 70 +
        9986882100549873382126430610667443070167930471615886552876345791191197) * 10 ^ 70 +
        0517163354179411673972038635355512755245590308639992695224632461331325) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_150 :
    recurrence2Scalar1Shift.coeff 150 =
      -(((7410503083732124236557560355926716386934 * 10 ^ 70 +
        0959999302722949608447779019635716502416978703888907879665162809608788) * 10 ^ 70 +
        3874502265233934862723568545463397942612641593757425766279075150446304) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_151 :
    recurrence2Scalar1Shift.coeff 151 =
      (((21826482473566664932364807726249881361712 * 10 ^ 70 +
        1589666442831068448254732350274383922807145860239118086099979615288565) * 10 ^ 70 +
        0785552388887661960926950617069523781509200419576959354112170534771807) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_152 :
    recurrence2Scalar1Shift.coeff 152 =
      (((18806813619352429909729671846047153817755 * 10 ^ 70 +
        4244042264965612184379679336701542847967708932159264773620788868218932) * 10 ^ 70 +
        4415388754232545014374676248225669495367005255502528399992584470217136) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_153 :
    recurrence2Scalar1Shift.coeff 153 =
      -(((345143834050133398628171443640426474864274 * 10 ^ 70 +
        2476919979026715075456302028436905487787091629074863878633889394646290) * 10 ^ 70 +
        5574698316254213541669663844515234604418068218794699310815099398893541) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Shift_coeff_154 :
    recurrence2Scalar1Shift.coeff 154 =
      (((979657012875872484446286038214742266703822 * 10 ^ 70 +
        2461349911889677524114229381798300705178617928874446105231640668831412) * 10 ^ 70 +
        1073923701610794940234547233518918840058232660810553651320188899240713) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_155 :
    recurrence2Scalar1Shift.coeff 155 =
      (((886990317553417365340326079102889722403428 * 10 ^ 70 +
        3485513170805482829383718500811227782583837647602068159557611407961313) * 10 ^ 70 +
        9746948229228646903379519017499391097463814372271744651759034996648256) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (156 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_156 :
    recurrence2Scalar1Shift.coeff 156 =
      -(((15589233748526093483384983207191922098328156 * 10 ^ 70 +
        5708571628820793838816359674699388235869143283408155421914178470654048) * 10 ^ 70 +
        7150921329751549208758476748056447720093267160829452762878677154122916) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 29 = 27 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (157 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_157 :
    recurrence2Scalar1Shift.coeff 157 =
      (((46035707375859882669916432932738522719530436 * 10 ^ 70 +
        0637967144010813619688789538574251069856774376904761682387096166265195) * 10 ^ 70 +
        4168912328324689267755949356246875490830012531705787540191060161981510) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 30 = 27 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (158 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_158 :
    recurrence2Scalar1Shift.coeff 158 =
      (((22142169091010871485334738454193585926296238 * 10 ^ 70 +
        2219688386379161470278184870833406279253271398417126564030872076589017) * 10 ^ 70 +
        8421163027996693527948456285724873017089903141807235234861574292409715) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 31 = 27 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (159 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_159 :
    recurrence2Scalar1Shift.coeff 159 =
      -(((643971369409455896330066124950108607547529957 * 10 ^ 70 +
        0894768667670536250354892665249617330848416627395238399105742607021685) * 10 ^ 70 +
        3065743290741230023606071315851630599260570087779889016085783601122585) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 32 = 27 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (160 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_160 :
    recurrence2Scalar1Shift.coeff 160 =
      (((2165128139851453263258489515387902443626227674 * 10 ^ 70 +
        8226606513746886640158950077652087356685053935819247288336468132734645) * 10 ^ 70 +
        3694212365322063615513111711717695609740862707724196901959461706539643) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 33 = 27 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (161 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_161 :
    recurrence2Scalar1Shift.coeff 161 =
      -(((650679071797269329048492666663346648169868271 * 10 ^ 70 +
        5022273739802654957140349008538401138870643215876576054950678657575686) * 10 ^ 70 +
        2160092452312739890276676765372447293689579135156959648889139774428334) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 34 = 27 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (162 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_162 :
    recurrence2Scalar1Shift.coeff 162 =
      -(((22443834002416588365733528769099420790632531145 * 10 ^ 70 +
        8650331387975975921256988342030588138863835674345251885987705369679168) * 10 ^ 70 +
        3408447547350557155642381683221493769736025968624605473433280173499464) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 35 = 27 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (163 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_163 :
    recurrence2Scalar1Shift.coeff 163 =
      (((92966824065307781179311106749323414578710709034 * 10 ^ 70 +
        1361342290698882740817668388773051990831221314780292975027582414957842) * 10 ^ 70 +
        0389637717920891936754818888465104653393357847231393261608484244992826) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 36 = 27 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (164 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_164 :
    recurrence2Scalar1Shift.coeff 164 =
      -(((107265744927887245643085483391415581528376730975 * 10 ^ 70 +
        5776559872929034693267768841346809556359478575515905349456207064771812) * 10 ^ 70 +
        2552242541112383168874399057251587976743586025385111497252973149425373) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 37 = 27 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (165 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_165 :
    recurrence2Scalar1Shift.coeff 165 =
      -(((595390139376457092622470288088090112606515832448 * 10 ^ 70 +
        3700422056781712566571822460780346403107054975034754679617793318744000) * 10 ^ 70 +
        3040437469053315151807872720261734542224659567954618281780466238255289) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 38 = 27 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (166 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_166 :
    recurrence2Scalar1Shift.coeff 166 =
      (((3408538964072156855035266622309015045699736104321 * 10 ^ 70 +
        7422604290556580941672506932892931845457534030951683595437264469293846) * 10 ^ 70 +
        0792951726801970509422991721749105936064950190299262749625455830675790) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 39 = 27 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (167 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_167 :
    recurrence2Scalar1Shift.coeff 167 =
      -(((6818367262245516794490646341963396705315205707592 * 10 ^ 70 +
        2328765185461233969237544821236960809644855695188247797727256334614229) * 10 ^ 70 +
        3051415112596258469219564419315752127152036220392312220392025159336483) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 40 = 27 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (168 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_168 :
    recurrence2Scalar1Shift.coeff 168 =
      -(((8721694667701095384220789250434751279410308153540 * 10 ^ 70 +
        9103626826504303600050621763148309236020291543107810877106461623640959) * 10 ^ 70 +
        0584685756606733100626037783267702170301615537979152827084876403579107) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 41 = 27 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (169 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_169 :
    recurrence2Scalar1Shift.coeff 169 =
      (((101302537739292624382549817470854261424589063728256 * 10 ^ 70 +
        3026280211785199165039709850688360249977022156227983805148693765384003) * 10 ^ 70 +
        2665117994370880927014836478895190637833152780835067842334037376407289) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 42 = 27 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (170 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_170 :
    recurrence2Scalar1Shift.coeff 170 =
      -(((299663067914350216652652164772621190020576859293972 * 10 ^ 70 +
        5915012580357120376026767934454604342964136094788774005900943545129370) * 10 ^ 70 +
        2951802167853971985771761642950059265397862578738251426072916122886023) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 43 = 27 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (171 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_171 :
    recurrence2Scalar1Shift.coeff 171 =
      (((162450252686980207943927544314498158687340659294593 * 10 ^ 70 +
        2042390058601247454184189966776767204803592706619068713980715464276266) * 10 ^ 70 +
        6326614696784288194990264012983758008744881499301102243796765016897333) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 44 = 27 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (172 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_172 :
    recurrence2Scalar1Shift.coeff 172 =
      (((2222911371892065603072569784132997867103495564678483 * 10 ^ 70 +
        8649287343806419534137023856411804462867859823890967058836965713425336) * 10 ^ 70 +
        8726826765568955743940913827088057878207358745920887614684855888903775) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 45 = 27 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (173 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_173 :
    recurrence2Scalar1Shift.coeff 173 =
      -(((9966025575126411306127249015743202195334459432331672 * 10 ^ 70 +
        6659996040044604391058256506180242544271289192257101456831088143535012) * 10 ^ 70 +
        4765990002343919153334918227472719495351565181159354650593522679807506) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 46 = 27 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (174 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_174 :
    recurrence2Scalar1Shift.coeff 174 =
      (((17522568292879007538200552479607370064976768901887472 * 10 ^ 70 +
        9703037494043086982087682134652513204889457810641266467462972221109338) * 10 ^ 70 +
        1277926594706573743367595540178258945209189901738397774556649630613578) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 47 = 27 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (175 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_175 :
    recurrence2Scalar1Shift.coeff 175 =
      (((23254174632860596998677397422312270023969201491066283 * 10 ^ 70 +
        7232081913394119576415135254998810403405486327926016474260991094163774) * 10 ^ 70 +
        0147734555375448601917591422684886648106348589272390420835881810990180) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 48 = 27 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (176 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_176 :
    recurrence2Scalar1Shift.coeff 176 =
      -(((244417521471003856794668660391864250623052224745442118 * 10 ^ 70 +
        6433613145686400300965183653529668750974003624299918494579889575587005) * 10 ^ 70 +
        4704478405535367333089205187627604922273835742682783310853511734736507) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 49 = 27 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (177 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_177 :
    recurrence2Scalar1Shift.coeff 177 =
      (((730096202504125109500039931198630331738715154809541574 * 10 ^ 70 +
        0981293343686701860489605759970066679157588728706842957962635144398937) * 10 ^ 70 +
        6934763067661306000745934901245217796035177665544783512666743199148866) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 50 = 27 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (178 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_178 :
    recurrence2Scalar1Shift.coeff 178 =
      -(((689047925274101235986807919681218976984317505616616929 * 10 ^ 70 +
        2736136317679568064823389884762013033764408410398805709367134693642241) * 10 ^ 70 +
        4869911018199551728931062552206446777677619462295430432245256947644880) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (179 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_179 :
    recurrence2Scalar1Shift.coeff 179 =
      -(((3542015753836774697872379745616527055894824561699532524 * 10 ^ 70 +
        6095624584582239732701047820507081861989314217108365661255988565802267) * 10 ^ 70 +
        9881975241911630091103888945652844986100214361727620813863658874571772) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 52 = 27 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (180 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_180 :
    recurrence2Scalar1Shift.coeff 180 =
      (((19325463630617371959333399248976476920740068489848893431 * 10 ^ 70 +
        7950283123339859186490031261273683055200452213757260501217172823997829) * 10 ^ 70 +
        6266246425443289373696608452873683235013426594388144189242420749613362) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 53 = 27 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (181 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_181 :
    recurrence2Scalar1Shift.coeff 181 =
      -(((45228107552762663801464364949041145771895846327899268599 * 10 ^ 70 +
        3404242711265237345910440217271020079079184963701097825386407121403688) * 10 ^ 70 +
        0876887129545566477267623389627992871165807554388944287472649393439795) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 54 = 27 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (182 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_182 :
    recurrence2Scalar1Shift.coeff 182 =
      (((18369247115629740771448706357053355300507692609690198483 * 10 ^ 70 +
        2362322293220202338000585317763331478778393262823970562828296322538481) * 10 ^ 70 +
        6205796117623520960641510615047796623945532745411494245621662709518791) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 55 = 27 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (183 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_183 :
    recurrence2Scalar1Shift.coeff 183 =
      (((287070405650256075524028624462515387071640866001167456095 * 10 ^ 70 +
        1031875006655385405987313140698559875265762167883998257789250859568252) * 10 ^ 70 +
        3641302611556971292687877168782970367421879128372665732269814985536062) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 56 = 27 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (184 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_184 :
    recurrence2Scalar1Shift.coeff 184 =
      -(((1248535514815045415873730304655401378247579246719579887476 * 10 ^ 70 +
        4402331141029558345248413486971598988108871021261638448479151828118510) * 10 ^ 70 +
        9283261462112197257364686968226890712452953998451951958078313050342988) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 57 = 27 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (185 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_185 :
    recurrence2Scalar1Shift.coeff 185 =
      (((2619658967681088626413067703807365021715565823520796596586 * 10 ^ 70 +
        6640019964646903054591005689908965481765974539977122610302915602048155) * 10 ^ 70 +
        8248040871302298419259777965460179893035594514816865736761039189785275) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 58 = 27 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (186 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_186 :
    recurrence2Scalar1Shift.coeff 186 =
      -(((733088739895802789571914975576636029993789130110767093722 * 10 ^ 70 +
        7214407055246195757507090732586113640775643720045854479843180784888860) * 10 ^ 70 +
        7085118892945211924081806379656431372957647949748528241487417521134851) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 59 = 27 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (187 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_187 :
    recurrence2Scalar1Shift.coeff 187 =
      -(((16486739110796690907529953639944623675363714388008670313250 * 10 ^ 70 +
        6476168228901685633304805389820606059500424339235074365556884942819799) * 10 ^ 70 +
        3966514110117851218800970432705412594611933830317449434877478524916265) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 60 = 27 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (188 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_188 :
    recurrence2Scalar1Shift.coeff 188 =
      (((68953939978707725027454586553831417213123980218509373452113 * 10 ^ 70 +
        6908156328905351408455517156691353027127625470655388155364772152501043) * 10 ^ 70 +
        8724802090137977457755557579202500029026718542830170979742669800674183) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 61 = 27 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (189 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_189 :
    recurrence2Scalar1Shift.coeff 189 =
      -(((148967641967146029332960418902349729952487550714191899400371 * 10 ^ 70 +
        0268936681769637640699078007065769941638534074786201218947726364189983) * 10 ^ 70 +
        1599498440873521210377373982681674431027804994683460578722828861247302) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 62 = 27 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (190 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_190 :
    recurrence2Scalar1Shift.coeff 190 =
      (((93481402046024998103014500112789593557513043560734649027125 * 10 ^ 70 +
        8797867870554273055640041181256373783582301806103995513252953749580576) * 10 ^ 70 +
        5028296307112103500513097542193962342300868408314767430196116640807129) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 63 = 27 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (191 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_191 :
    recurrence2Scalar1Shift.coeff 191 =
      (((661639847450109389544831642019700294110262714922003050769282 * 10 ^ 70 +
        2006986271952568010784547146418615134343518035917365500321095576434492) * 10 ^ 70 +
        7847538875675949803859509146056172332222835537847801165773799589165066) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 64 = 27 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (192 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_192 :
    recurrence2Scalar1Shift.coeff 192 =
      -(((3188266108726376662244641539538236906147243699915858577715991 * 10 ^ 70 +
        7618948272065439064720063515370086525152180547726494962637725647528657) * 10 ^ 70 +
        2906431859299969800387468369040903333314249835707711302769896054661075) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 65 = 27 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (193 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_193 :
    recurrence2Scalar1Shift.coeff 193 =
      (((7946277162688838449529748463371949961076455189598252934615987 * 10 ^ 70 +
        7168102218395368048408965482550138026689193428942584583946559810876415) * 10 ^ 70 +
        6620024374018259930045380896727562891255581622282027080354271133753578) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 66 = 27 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (194 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_194 :
    recurrence2Scalar1Shift.coeff 194 =
      -(((9998117862484109462476750552147970420107245541204721805411101 * 10 ^ 70 +
        4975212136300351255517878150017757126426572540801205726242469801092002) * 10 ^ 70 +
        1292085703952831462358667178912302218413590719148506557163391952452003) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 67 = 27 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (195 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_195 :
    recurrence2Scalar1Shift.coeff 195 =
      -(((12061401358978954363838035692857829789395576355263491896111596 * 10 ^ 70 +
        4357647084840694932063347118023681299809807279945780927700413907969594) * 10 ^ 70 +
        2234170319067185187724590897478274400884320090305918402609298643980762) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 68 = 27 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (196 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_196 :
    recurrence2Scalar1Shift.coeff 196 =
      (((109310034217451895953243465362088403914031917398190424032810068 * 10 ^ 70 +
        8837531325741924863938712235213348240068542099339432703664961631878610) * 10 ^ 70 +
        6069806385697886457116928110907550393815866630382588236099263337581017) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (197 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_197 :
    recurrence2Scalar1Shift.coeff 197 =
      -(((348601551614760209354710737546850773224641810430454707712776862 * 10 ^ 70 +
        3357009955527402346203027893944767010553650181680082354833409672964331) * 10 ^ 70 +
        4574155476839859717054765172012427298107890938537192974261236514253788) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 70 = 27 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (198 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_198 :
    recurrence2Scalar1Shift.coeff 198 =
      (((688454378113464575884155152405352467107781773516423581573057247 * 10 ^ 70 +
        9215887800835318492509763279525655743963164795898883036120275615854009) * 10 ^ 70 +
        4056895718130356440550627935827003725469040193084704697535612883331676) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 71 = 27 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (199 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_199 :
    recurrence2Scalar1Shift.coeff 199 =
      -(((598088800617504848897726500908842486608390784325046616023673968 * 10 ^ 70 +
        5837080369836226243386819217741177614751332311279602974401657192364814) * 10 ^ 70 +
        3403238947797974884689890198243377267599010894940061520837836727805949) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 72 = 27 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (200 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_200 :
    recurrence2Scalar1Shift.coeff 200 =
      -(((1685112187379745567148729456764180314443613377206683579815046883 * 10 ^ 70 +
        7534270169266898579095595347306056863594567845439759371750428094408128) * 10 ^ 70 +
        0864440884754584737835092693598589003696973938910899163272540402357940) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 73 = 27 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (201 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_201 :
    recurrence2Scalar1Shift.coeff 201 =
      (((9912082417426194538909488161353213715518100585401878896014192659 * 10 ^ 70 +
        7362554105717443862729821020544570497329764325682402657147555881159365) * 10 ^ 70 +
        0452050896927877277796214593732138208693447923910512928997619069803796) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 74 = 27 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (202 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_202 :
    recurrence2Scalar1Shift.coeff 202 =
      -(((28857461867257253956537922565048525752470034853326335410783785367 * 10 ^ 70 +
        9917256180462377078762604663747849512271479829181897531530194424456123) * 10 ^ 70 +
        7794422719031466897411659443018184586586236112728936010980210185393011) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 75 = 27 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (203 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_203 :
    recurrence2Scalar1Shift.coeff 203 =
      (((57114957268739537572816815957172804020336058774608849876118687405 * 10 ^ 70 +
        3206279089303374189552135355145461643805835826536839945957651611959253) * 10 ^ 70 +
        9376005158520209643049526174794158160102789257826042335912383631624446) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 76 = 27 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (204 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_204 :
    recurrence2Scalar1Shift.coeff 204 =
      -(((65573722861799217713957366881611132043991025320062496984922198318 * 10 ^ 70 +
        3901030134909939105893350775476485872205933593378565839241272444665629) * 10 ^ 70 +
        0843025177263450078965258031899422769309531398996272836219022439477435) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 77 = 27 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (205 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_205 :
    recurrence2Scalar1Shift.coeff 205 =
      -(((46966331916749797093682706291302132953210841179784372961418229801 * 10 ^ 70 +
        0407492990189366885610605441717395224203389051790184594642068489300744) * 10 ^ 70 +
        9449023329044006334635201165985558317493455918495323460855742237846995) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 78 = 27 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (206 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_206 :
    recurrence2Scalar1Shift.coeff 206 =
      (((516666272439456061738418862697662913636950552503648061267023061077 * 10 ^ 70 +
        0869916353133907351068278448993301857131475729975539471687168879443410) * 10 ^ 70 +
        2262742442230194851833041967081666536675868461751389464464064859062525) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 79 = 27 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (207 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_207 :
    recurrence2Scalar1Shift.coeff 207 =
      -(((1746263144302360832637855678368976451151653501286500115173960085758 * 10 ^ 70 +
        2385709703630428487478730431285820894448142713404650425960089462653306) * 10 ^ 70 +
        5547362391617976220826370635791369167623118848240857263418689748334813) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 80 = 27 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (208 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_208 :
    recurrence2Scalar1Shift.coeff 208 =
      (((4152803985897118126592084493388014190937023099519635189030767251660 * 10 ^ 70 +
        8200873715088379304589176964817429851248317583205233308215117493267845) * 10 ^ 70 +
        3082847109804544658315043137296966235033149579672508734489571989234048) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 81 = 27 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (209 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_209 :
    recurrence2Scalar1Shift.coeff 209 =
      -(((7502508301286458791843966701334695901829939709830472578074047876822 * 10 ^ 70 +
        1679074993016199240020528256097665984066883480166476723354693176901661) * 10 ^ 70 +
        0472760668310530869528807163553285458188806398958267884500730038924338) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 82 = 27 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (210 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_210 :
    recurrence2Scalar1Shift.coeff 210 =
      (((9181227303517182236331247786959388267427711939007983555103182737401 * 10 ^ 70 +
        1285894082033339338466943282588482075315111347408869639041805386118440) * 10 ^ 70 +
        3944482090748556099520231658604351377352915796645593654675887962149980) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (211 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_211 :
    recurrence2Scalar1Shift.coeff 211 =
      -(((703819663533889639969891576660150048038702796175830082225763264421 * 10 ^ 70 +
        3382446313235478561658838017214301223704941232549105277350051982633818) * 10 ^ 70 +
        2610743511970584577862444656982780454296442309133034777022679691366429) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 84 = 27 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (212 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_212 :
    recurrence2Scalar1Shift.coeff 212 =
      -(((38028523091129704734211138474046345366048381000895050769596011997426 * 10 ^ 70 +
        5488322719731911250210648514421214935173367935930884435440072997204777) * 10 ^ 70 +
        3458617310986386678905612200311124644342150842475322498608140731685009) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 85 = 27 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (213 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_213 :
    recurrence2Scalar1Shift.coeff 213 =
      (((146224040271168691494075383853284418935442445586469277176676516945038 * 10 ^ 70 +
        2656965274576546493659835721921216573058027798623646640842281776920282) * 10 ^ 70 +
        4731808643026760400786019470274710862166059895319826073013379534108360) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 86 = 27 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (214 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_214 :
    recurrence2Scalar1Shift.coeff 214 =
      -(((388683459798017568098236258917101831290639772895804498363054902462622 * 10 ^ 70 +
        2186156054513959713920358604213115441396112227583918355276376329539004) * 10 ^ 70 +
        4038764815424823073779803810391455947842486751472632339161885825168507) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 87 = 27 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (215 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_215 :
    recurrence2Scalar1Shift.coeff 215 =
      (((854681737544603260538946339158594826224733881279674816913673079032908 * 10 ^ 70 +
        7334379813113919430004758187342414506028083734933857560675346143956856) * 10 ^ 70 +
        4909908507765657969189687319829001242844639798419955589340099427218942) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 88 = 27 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (216 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_216 :
    recurrence2Scalar1Shift.coeff 216 =
      -(((1637662985067158951550185620904255133890780207889948055935646183952436 * 10 ^ 70 +
        2229528093467572762803559085576965781688282029282942042969313141619779) * 10 ^ 70 +
        8720298174162866693462890140141287339546863907093874571042864106981732) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 89 = 27 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (217 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_217 :
    recurrence2Scalar1Shift.coeff 217 =
      (((2779532905202633315337614569590348013569661181554221947439187172760368 * 10 ^ 70 +
        1076882642250053057326866617595999562725291917785607302128637189879932) * 10 ^ 70 +
        5925242705310107948020427635217162013099181095887765528786896707454826) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 90 = 27 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (218 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_218 :
    recurrence2Scalar1Shift.coeff 218 =
      -(((4162031687384066921628405456324263484289185531770486438948452103635509 * 10 ^ 70 +
        2204060622448003857504245235454193304523839831770858381245043382790882) * 10 ^ 70 +
        5183373181011776426791279491493356503414245839784653866137062303901641) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 91 = 27 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (219 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_219 :
    recurrence2Scalar1Shift.coeff 219 =
      (((5333712307931112269683202737361717299034586397903918686976322995269733 * 10 ^ 70 +
        9225963174534502820014538307831629024207202214075077322688022112522184) * 10 ^ 70 +
        5166081283415289252668331387727507652045611325249117406014187782058934) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 92 = 27 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (220 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_220 :
    recurrence2Scalar1Shift.coeff 220 =
      -(((5278171641336104773487019753934803408593847186668110297782237803374945 * 10 ^ 70 +
        8092922429301536156825356600656651053171195951876133601510573681751619) * 10 ^ 70 +
        5546391354661949959266149546534161614545472977845988979264619742841555) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 93 = 27 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (221 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_221 :
    recurrence2Scalar1Shift.coeff 221 =
      (((2158568845801317503165898230307271675474794742644200912035618917213872 * 10 ^ 70 +
        8151802390456347142673520362324353060298324678825716552217149059081749) * 10 ^ 70 +
        3840871250848102576451866056030911445874927442189372644574358088903718) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 94 = 27 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (222 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_222 :
    recurrence2Scalar1Shift.coeff 222 =
      (((6888855195337571396947930486365521132898931981305253284606454497672786 * 10 ^ 70 +
        9852444337086443113084878449107053209899206523865839677653027102263978) * 10 ^ 70 +
        2566261598404533350449802956949142337306998837216420406374048949683944) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 95 = 27 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (223 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_223 :
    recurrence2Scalar1Shift.coeff 223 =
      -((((2 * 10 ^ 70 +
        5804369158969007176679681159950795013749078646126592810803973113412073) * 10 ^ 70 +
        3540524917552257163188042457657072577287785093929018677530138737127348) * 10 ^ 70 +
        5311907460176768530158072716066927977549660317938251535639516519428372) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 96 = 27 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (224 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_224 :
    recurrence2Scalar1Shift.coeff 224 =
      ((((5 * 10 ^ 70 +
        9373691779196742731823742776932546509200317397345865010608300247506400) * 10 ^ 70 +
        1766652524531964847019147309383546495403516745774731271677873039392449) * 10 ^ 70 +
        9738563463178531328176293770052141740894940554476670910588645800310849) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 97 = 27 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (225 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_225 :
    recurrence2Scalar1Shift.coeff 225 =
      -((((11 * 10 ^ 70 +
        2614329071507127118604056640817948069631312487002649251956069347133141) * 10 ^ 70 +
        6644599272393243036249880019393020976031166676430725646605592002761010) * 10 ^ 70 +
        0001094646438489309183400011581842944767116274401533929364568014900781) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 98 = 27 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (226 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_226 :
    recurrence2Scalar1Shift.coeff 226 =
      ((((18 * 10 ^ 70 +
        9749100844957729406980307232598144424636932853758930047871628837343532) * 10 ^ 70 +
        5163096738501377210619945086535998358994003951983346574513555200538911) * 10 ^ 70 +
        7217667136219634564404838228426200754909685318749178375133030455204755) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 99 = 27 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (227 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_227 :
    recurrence2Scalar1Shift.coeff 227 =
      -((((29 * 10 ^ 70 +
        2855701498511922381543251619242722764773082363807118078751627727633778) * 10 ^ 70 +
        7781585798707203697665630118029159128716612325637455099505823990635074) * 10 ^ 70 +
        4543546929688335883179711665969595799216152353490164627608569646555861) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 100 = 27 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (228 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_228 :
    recurrence2Scalar1Shift.coeff 228 =
      ((((42 * 10 ^ 70 +
        0424117001740409497632790408201772835138026704530444328760652197319845) * 10 ^ 70 +
        2926879521232773792745119241627880409032569316371834178070604502893349) * 10 ^ 70 +
        1937883455622944825023067178596235372705354903601879039504091871714817) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 101 = 27 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (229 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_229 :
    recurrence2Scalar1Shift.coeff 229 =
      -((((56 * 10 ^ 70 +
        6177679701107528239690697053000390026485002388850135785682680205498589) * 10 ^ 70 +
        1507002293116254854352627117135794967351590254991869648962831350725534) * 10 ^ 70 +
        0290311449403527776006846252090725812555516266397217544554994109080020) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 102 = 27 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (230 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_230 :
    recurrence2Scalar1Shift.coeff 230 =
      ((((71 * 10 ^ 70 +
        8566528858394473867793273227416912670060951189206592506640796917151104) * 10 ^ 70 +
        3447946079979795366347084173566027376480672231556563046821459026369809) * 10 ^ 70 +
        8776012342246927814094201742373707727376933902047673064375429181677879) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 102 = 26 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (231 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_231 :
    recurrence2Scalar1Shift.coeff 231 =
      -((((86 * 10 ^ 70 +
        1281612045528606235770345838544827361145028047759422171207006617678390) * 10 ^ 70 +
        6947524328008958452343596177767922574619080775847988681255291986978048) * 10 ^ 70 +
        9548707991441217251313487706725193303066471356472914787560149571714562) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 2 +
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
    rw [show 102 = 25 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (232 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_232 :
    recurrence2Scalar1Shift.coeff 232 =
      ((((97 * 10 ^ 70 +
        4949948583393093077591424553607827124092946439081400925762878551603438) * 10 ^ 70 +
        6919897692360769887421236270783273535901941820029340300928438715509056) * 10 ^ 70 +
        4864002599149748112663463194495881760376848243545693259210401617918818) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 3 +
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
    rw [show 102 = 24 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (233 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_233 :
    recurrence2Scalar1Shift.coeff 233 =
      -((((103 * 10 ^ 70 +
        9887395062551281412987670946824809175129853724497895771893673326282568) * 10 ^ 70 +
        8501878803766387138914471941968946827196203879108678738370074179296631) * 10 ^ 70 +
        1414214509539125408112784758014877100310538980348283447859512036458272) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 4 +
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
    rw [show 102 = 23 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (234 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_234 :
    recurrence2Scalar1Shift.coeff 234 =
      ((((103 * 10 ^ 70 +
        9475072519042855632550419061552920960357579657335493459903841576395363) * 10 ^ 70 +
        5516632766874966019237472237862191789306948012889554641917110574493190) * 10 ^ 70 +
        5333794218300212824592182043859192296974992339934902745440614323510577) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 5 +
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
    rw [show 102 = 22 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
