/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B3_coeff_0
  recurrence2B3_coeff_1
  recurrence2B3_coeff_2
  recurrence2B3_coeff_3
  recurrence2B3_coeff_4
  recurrence2B3_coeff_5
  recurrence2B3_coeff_6
  recurrence2B3_coeff_7
  recurrence2B3_coeff_8
  recurrence2B3_coeff_9
  recurrence2B3_coeff_10
  recurrence2B3_coeff_11
  recurrence2B3_coeff_12
  recurrence2B3_coeff_13
  recurrence2B3_coeff_14
  recurrence2B3_coeff_15
  recurrence2B3_coeff_16
  recurrence2B3_coeff_17
  recurrence2B3_coeff_18
  recurrence2B3_coeff_19
  recurrence2B3_coeff_20
  recurrence2B3_coeff_21
  recurrence2B3_coeff_22
  recurrence2B3_coeff_23
  recurrence2B3_coeff_24
  recurrence2B3_coeff_25
  recurrence2B3_coeff_26
  recurrence2B3_coeff_27
  recurrence2B3_coeff_28
  recurrence2B3_coeff_29
  recurrence2B3_coeff_30
  recurrence2B3_coeff_31
  recurrence2B3_coeff_32
  recurrence2B3_coeff_33
  recurrence2B3_coeff_34
  recurrence2B3_coeff_35
  recurrence2B3_coeff_36
  recurrence2B3_coeff_37
  recurrence2B3_coeff_38
  recurrence2B3_coeff_39
  recurrence2B3_coeff_40
  recurrence2B3_coeff_41
  recurrence2B3_coeff_42
  recurrence2B3_coeff_43
  recurrence2B3_coeff_44
  recurrence2B3_coeff_45
  recurrence2B3_coeff_46
  recurrence2B3_coeff_47
  recurrence2B3_coeff_48
  recurrence2B3_coeff_49
  recurrence2B3_coeff_50
  recurrence2B3_coeff_51
  recurrence2B3_coeff_52
  recurrence2B3_coeff_53
  recurrence2B3_coeff_54
  recurrence2B3_coeff_55
  recurrence2B3_coeff_56
  recurrence2B3_coeff_57
  recurrence2B3_coeff_58
  recurrence2B3_coeff_59
  recurrence2B3_coeff_60
  recurrence2B3_coeff_61
  recurrence2B3_coeff_62
  recurrence2B3_coeff_63
  recurrence2B3_coeff_64
  recurrence2B3_coeff_65
  recurrence2B3_coeff_66
  recurrence2B3_coeff_67
  recurrence2B3_coeff_68
  recurrence2B3_coeff_69
  recurrence2B3_coeff_70
  recurrence2B3_coeff_71
  recurrence2B3_coeff_72
  recurrence2B3_coeff_73
  recurrence2B3_coeff_74
  recurrence2B3_coeff_75
  recurrence2B3_coeff_76
  recurrence2B3_coeff_77
  recurrence2B3_coeff_78
  recurrence2B3_coeff_79
  recurrence2B3_coeff_80
  recurrence2B3_coeff_81
  recurrence2B3_coeff_82
  recurrence2B3_coeff_83
  recurrence2B3_coeff_84
  recurrence2B3_coeff_85
  recurrence2B3_coeff_86
  recurrence2B3_coeff_87
  recurrence2B3_coeff_88
  recurrence2B3_coeff_89
  recurrence2B3_coeff_90
  recurrence2B3_coeff_91
  recurrence2B3_coeff_92
  recurrence2B3_coeff_93
  recurrence2B3_coeff_94
  recurrence2B3_coeff_95
  recurrence2B3_coeff_96
  recurrence2B3_coeff_97
  recurrence2B3_coeff_98
  recurrence2B3_coeff_99
  recurrence2B3_coeff_100
  recurrence2B3_coeff_101
  recurrence2B3_coeff_102
  recurrence2B3_coeff_103
  recurrence2B3_coeff_104
  recurrence2B3_coeff_105
  recurrence2B3_coeff_106
  recurrence2B3_coeff_107
  recurrence2B3_coeff_108
  recurrence2B3_coeff_109
  recurrence2B3_coeff_110
  recurrence2B3_coeff_111
  recurrence2B3_coeff_112
  recurrence2B3_coeff_113
  recurrence2B3_coeff_114
  recurrence2B3_coeff_115
  recurrence2B3_coeff_116
  recurrence2B3_coeff_117
  recurrence2B3_coeff_118
  recurrence2B3_coeff_119
  recurrence2B3_coeff_120
  recurrence2B3_coeff_121
  recurrence2B3_coeff_122
  recurrence2B3_coeff_123
  recurrence2B3_coeff_124
  recurrence2B3_coeff_125
  recurrence2B3_coeff_126
  recurrence2B3_coeff_127
  recurrence2B3_coeff_128
  recurrence2B3_coeff_129
  recurrence2B3_coeff_130
  recurrence2B3_coeff_131
  recurrence2B3_coeff_132
  recurrence2B3_coeff_133
  recurrence2B3_coeff_134
  recurrence2B3_coeff_135
  recurrence2B3_coeff_136
  recurrence2B3_coeff_137
  recurrence2B3_coeff_138
  recurrence2B3_coeff_139
  recurrence2B3_coeff_140
  recurrence2B3_coeff_141
  recurrence2B3_coeff_142
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

theorem recurrence2Scalar4Shift_coeff_0 :
    recurrence2Scalar4Shift.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_1 :
    recurrence2Scalar4Shift.coeff 1 =
      (-18616320 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_2 :
    recurrence2Scalar4Shift.coeff 2 =
      (-86085473280 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_3 :
    recurrence2Scalar4Shift.coeff 3 =
      (-653845232887728 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_4 :
    recurrence2Scalar4Shift.coeff 4 =
      (-1759627223865466168 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_5 :
    recurrence2Scalar4Shift.coeff 5 =
      (-5089912252186246527920 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_6 :
    recurrence2Scalar4Shift.coeff 6 =
      (36384057211809888422344 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_7 :
    recurrence2Scalar4Shift.coeff 7 =
      (2536510807817426456476115760 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_8 :
    recurrence2Scalar4Shift.coeff 8 =
      (-1490108743313765272220937059608 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_9 :
    recurrence2Scalar4Shift.coeff 9 =
      (3063948890803397330597364255138264 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_10 :
    recurrence2Scalar4Shift.coeff 10 =
      (-1272909368524094231027237140120394160 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_11 :
    recurrence2Scalar4Shift.coeff 11 =
      (830159471203764364250132330193286012084 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_12 :
    recurrence2Scalar4Shift.coeff 12 =
      (-335747645432826665752924540534773821441974 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_13 :
    recurrence2Scalar4Shift.coeff 13 =
      (103468708523233241926323915034642975241344414 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_14 :
    recurrence2Scalar4Shift.coeff 14 =
      (-23739216294813522485372260375062102643165969694 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_15 :
    recurrence2Scalar4Shift.coeff 15 =
      (4111270808710063716625779350387751626869899609664 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_16 :
    recurrence2Scalar4Shift.coeff 16 =
      (-541156875506926247790155007350157110686847756372052 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_17 :
    recurrence2Scalar4Shift.coeff 17 =
      (50643720829429837382794737563517163562263582771217595 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_18 :
    recurrence2Scalar4Shift.coeff 18 =
      (-2802129552868454518251234141501131930005936794135819876 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_19 :
    recurrence2Scalar4Shift.coeff 19 =
      (-28204354260149165988318160364044275592637140884438089734 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_20 :
    recurrence2Scalar4Shift.coeff 20 =
      (24303370803551539293735984305645142681838451544656896879848 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_21 :
    recurrence2Scalar4Shift.coeff 21 =
      (-2777673435013683380823351399124169752905025979256072168951085 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_22 :
    recurrence2Scalar4Shift.coeff 22 =
      (183353575087504018685363604685851747656550192057573290421641944 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_23 :
    recurrence2Scalar4Shift.coeff 23 =
      (-6943738583518476430993736937765083595548839825111701117997925134 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_24 :
    recurrence2Scalar4Shift.coeff 24 =
      (46954165765694654818600740250394242970849456307436363161974976679 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_25 :
    recurrence2Scalar4Shift.coeff 25 =
      (9566092535251612766053383750754036494633627414618312545635010991999 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_26 :
    recurrence2Scalar4Shift.coeff 26 =
      (-225802715413063673463428208008508487634335786557546093964568430436283 : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_27 :
    recurrence2Scalar4Shift.coeff 27 =
      -((4 * 10 ^ 70 +
        8718270911865048952234558284034881966388641220365228077118482407000154) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_28 :
    recurrence2Scalar4Shift.coeff 28 =
      ((627 * 10 ^ 70 +
        2379260068730934938850056804662122286550045629606624099476972917497735) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_29 :
    recurrence2Scalar4Shift.coeff 29 =
      -((44615 * 10 ^ 70 +
        6409084310027048243234133529751464528988718460813332105807938147177283) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_30 :
    recurrence2Scalar4Shift.coeff 30 =
      ((2324541 * 10 ^ 70 +
        0600384320691129093855118021776311609909809058292941340232109691870191) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_31 :
    recurrence2Scalar4Shift.coeff 31 =
      -((94360625 * 10 ^ 70 +
        2220077528885186678516945001186203775116438300806484294886377764604280) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_32 :
    recurrence2Scalar4Shift.coeff 32 =
      ((2826476416 * 10 ^ 70 +
        2292990929735743355778703590509132394427705946236297278708161801330410) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_33 :
    recurrence2Scalar4Shift.coeff 33 =
      -((38387715470 * 10 ^ 70 +
        4388941965741945893563592543658302593777334144408812426095042257398110) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_34 :
    recurrence2Scalar4Shift.coeff 34 =
      -((2220803296096 * 10 ^ 70 +
        9158269388672582496382439725809651341078738039179673906263185510453816) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_35 :
    recurrence2Scalar4Shift.coeff 35 =
      ((221724065360911 * 10 ^ 70 +
        2972363089323915523406901924720041555975034680099547240629737604802606) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_36 :
    recurrence2Scalar4Shift.coeff 36 =
      -((11600859248608932 * 10 ^ 70 +
        8411287165600902333353977188847750345015754227968435988329220067585840) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_37 :
    recurrence2Scalar4Shift.coeff 37 =
      ((442262459690611246 * 10 ^ 70 +
        2669915869794750635325021124963177275395723576612251949452181088719688) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_38 :
    recurrence2Scalar4Shift.coeff 38 =
      -((13069370847345907978 * 10 ^ 70 +
        7810972912357237757050373157053855132481226130669509204921355575610267) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_39 :
    recurrence2Scalar4Shift.coeff 39 =
      ((303433502976192050803 * 10 ^ 70 +
        9099024334351808010553619997448228518048324059870467043420199410449100) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_40 :
    recurrence2Scalar4Shift.coeff 40 =
      -((5691483725261066663271 * 10 ^ 70 +
        6846128381805940094458250121979535228506446728397926219718844796786314) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_41 :
    recurrence2Scalar4Shift.coeff 41 =
      ((105747362947552271948778 * 10 ^ 70 +
        7693635853292990356153211520798597322792378264066522614686397979447348) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_42 :
    recurrence2Scalar4Shift.coeff 42 =
      -((3131147637032718221827385 * 10 ^ 70 +
        9808487051784021999216365959831647354595689091235817663043588198254198) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_43 :
    recurrence2Scalar4Shift.coeff 43 =
      ((132564427630225772967349624 * 10 ^ 70 +
        9315590454530997721581610580002428893851070497855000220445908401877139) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_44 :
    recurrence2Scalar4Shift.coeff 44 =
      -((5192610546125521711509556219 * 10 ^ 70 +
        0366543689663567661685312411433445576917762180859757219506067457121877) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_45 :
    recurrence2Scalar4Shift.coeff 45 =
      ((167669243010062071473824599825 * 10 ^ 70 +
        2933227220873236114969092606465794739587967100377571648347218507456949) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_46 :
    recurrence2Scalar4Shift.coeff 46 =
      -((4492996626652958094265418245929 * 10 ^ 70 +
        4854751640664824603469396501011824498321772114563574748163803385448461) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_47 :
    recurrence2Scalar4Shift.coeff 47 =
      ((102001536510693622673366268481835 * 10 ^ 70 +
        6294986358727542488592830115000385357755992355308177866579336112489770) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_48 :
    recurrence2Scalar4Shift.coeff 48 =
      -((1990787691052707496499039611595772 * 10 ^ 70 +
        8394528356830320790339765659473082572572825486033569048374016293288240) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_49 :
    recurrence2Scalar4Shift.coeff 49 =
      ((33487735383266991591158956561820876 * 10 ^ 70 +
        8932171736328751069130450571587106120913775258755711565660938123615089) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_50 :
    recurrence2Scalar4Shift.coeff 50 =
      -((474548599248266520577454270489400707 * 10 ^ 70 +
        1588936832960973213040767248875248598453618117309143979950270541262296) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_51 :
    recurrence2Scalar4Shift.coeff 51 =
      ((5117385967113750864089424093850970964 * 10 ^ 70 +
        9893296585007007098661876670447449447876239647652627075098642832258699) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_52 :
    recurrence2Scalar4Shift.coeff 52 =
      -((20640911620768007235620309831964200371 * 10 ^ 70 +
        4385762354539517720117751814796657424510951909099519776359062011545646) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_53 :
    recurrence2Scalar4Shift.coeff 53 =
      -((893771073554016419533661616845937192308 * 10 ^ 70 +
        4177935536665627688877463402378224728146169688437342570103527327836927) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_54 :
    recurrence2Scalar4Shift.coeff 54 =
      ((34971207294076245970313242029678821272543 * 10 ^ 70 +
        8329117251928420917993496023454961242188488417663613335231955771847153) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_55 :
    recurrence2Scalar4Shift.coeff 55 =
      -((846711912687671046298438242678177418730317 * 10 ^ 70 +
        1897523329590915108310872060609815857358257056912234062311167677510114) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_56 :
    recurrence2Scalar4Shift.coeff 56 =
      ((16447307732368636055325531124529708438164980 * 10 ^ 70 +
        5903407382953410444133546667594537807056605891739310338621053374346110) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_57 :
    recurrence2Scalar4Shift.coeff 57 =
      -((271627251696055035717500240711064490501588060 * 10 ^ 70 +
        3082558196654696550996137355438535732874537065735899181314680118400218) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_58 :
    recurrence2Scalar4Shift.coeff 58 =
      ((3853584179635834177003216116384668967854001880 * 10 ^ 70 +
        2306894758577135537214396780184909528836772629215296556683021715411698) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_59 :
    recurrence2Scalar4Shift.coeff 59 =
      -((45958626356006936924832221426535085169385503904 * 10 ^ 70 +
        6014110354757140428364262899023641521333398662975391792983003525794576) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_60 :
    recurrence2Scalar4Shift.coeff 60 =
      ((421458207009349833903524214229884304864464133855 * 10 ^ 70 +
        6566854315157077816573885502070830023265734129913704855438198356551480) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_61 :
    recurrence2Scalar4Shift.coeff 61 =
      -((1788411920507960956227054019221628535944017569248 * 10 ^ 70 +
        5972774741236681739273426109220718483683249346037040818595464945953805) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_62 :
    recurrence2Scalar4Shift.coeff 62 =
      -((36264821904544926445444022930707346283098176441863 * 10 ^ 70 +
        0009708227565854735564677308591812978827878658947232317395776831623171) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_63 :
    recurrence2Scalar4Shift.coeff 63 =
      ((1275449695891102683654543696401573249003781063866238 * 10 ^ 70 +
        5844641257429072484146101761224586564574285554497328053496141557780389) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_64 :
    recurrence2Scalar4Shift.coeff 64 =
      -((25837383561160767682892781909917554480795364595300301 * 10 ^ 70 +
        8921144900501314709134066774020246848898786704946743639906708993271823) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_65 :
    recurrence2Scalar4Shift.coeff 65 =
      ((424215958502251176944037710743909968121031584458748896 * 10 ^ 70 +
        4571118180695013678412756154324644727044050226672332720332199997386776) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_66 :
    recurrence2Scalar4Shift.coeff 66 =
      -((6127711475247397840378733249411441084844598795900504569 * 10 ^ 70 +
        9269082916463770264393774934300861774689222670277871871158503771094138) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_67 :
    recurrence2Scalar4Shift.coeff 67 =
      ((80510190575719300374775687424710202516599350365568885145 * 10 ^ 70 +
        0759692084570338313271664017302993322135124852623688791517655560942603) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_68 :
    recurrence2Scalar4Shift.coeff 68 =
      -((978771239315441250007425743278439813257644964447506977172 * 10 ^ 70 +
        2342439884458902082826106941380748491091845976628856614660770270705848) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_69 :
    recurrence2Scalar4Shift.coeff 69 =
      ((11122934544334162511516490636569061214509380253358407946567 * 10 ^ 70 +
        2476369784349294294452505141165043675363217368232992997989591248756613) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_70 :
    recurrence2Scalar4Shift.coeff 70 =
      -((118960440448081582370155465817892658564381358452756981982771 * 10 ^ 70 +
        7918653986534356504591617984198804360961702737655701863579647589134582) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_71 :
    recurrence2Scalar4Shift.coeff 71 =
      ((1203193737429954970808689400346999518022266169910630762549908 * 10 ^ 70 +
        8418584995871027443619074423435694210192320849395370603869009482811409) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_72 :
    recurrence2Scalar4Shift.coeff 72 =
      -((11550585363941072001839548284481679790600017984705366570318163 * 10 ^ 70 +
        0076508448410760010382663895097269206564734382137962501797529520233576) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_73 :
    recurrence2Scalar4Shift.coeff 73 =
      ((105544003646416965649103726657281951867122124291397614496979547 * 10 ^ 70 +
        1996609819659576514197927013632661858190069378890496889013611708419271) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_74 :
    recurrence2Scalar4Shift.coeff 74 =
      -((919987511993084008768084339561999722534905150026963415719191955 * 10 ^ 70 +
        5167417064843915055102599948341207823495862336762518867280400596271365) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_75 :
    recurrence2Scalar4Shift.coeff 75 =
      ((7663082704302959409313043669199758802394082225043026618072226788 * 10 ^ 70 +
        2999693118541915868869663596719472119343174726464954214599280313411617) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_76 :
    recurrence2Scalar4Shift.coeff 76 =
      -((61080630221015856101723347594560757849740002581612114466862032204 * 10 ^ 70 +
        1093967617117578188359257780170631722602709172820045817361505242921605) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_77 :
    recurrence2Scalar4Shift.coeff 77 =
      ((466427294745392322168474266046735252168512719782952742783223786666 * 10 ^ 70 +
        8860271519020044367266917333290412566109650811068381006073179600178634) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_78 :
    recurrence2Scalar4Shift.coeff 78 =
      -((3415689194700677369841439416965423646195536695616904578660942928102 * 10 ^ 70 +
        0597495402948383852944071442954649512630653959620427468539428951048761) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_79 :
    recurrence2Scalar4Shift.coeff 79 =
      ((24008822641411806066159747725636710717429575455044946755254548936229 * 10 ^ 70 +
        0678917666699834241285439235134513426030327148674839173230471626252697) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_80 :
    recurrence2Scalar4Shift.coeff 80 =
      -((162106198337681446668507998902215377268100159134216117996621786235887 * 10 ^ 70 +
        6107766424933930581575658041219500565895981474007864210433453264621836) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_81 :
    recurrence2Scalar4Shift.coeff 81 =
      ((1052078565584501930139616964683102298058414793317931568106140523498612 * 10 ^ 70 +
        6586809990880484404492937594709887660277582925999876108506456916143888) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_82 :
    recurrence2Scalar4Shift.coeff 82 =
      -((6566495839810461840156483892279737165574756909686580919686689503022851 * 10 ^ 70 +
        4768296346432610099908743198003324514945115765704871741165578279032500) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_83 :
    recurrence2Scalar4Shift.coeff 83 =
      (((3 * 10 ^ 70 +
        9427664566338116476848059568516026073191042484167656754116616029108601) * 10 ^ 70 +
        6918295225310720518805007169467179200822757832633431456516897714184678) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_84 :
    recurrence2Scalar4Shift.coeff 84 =
      -(((22 * 10 ^ 70 +
        7787260741093260199316117820242277592881363429685379760070507936667962) * 10 ^ 70 +
        7557908092817143039542031727477484758729016191746111542174016141262572) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_85 :
    recurrence2Scalar4Shift.coeff 85 =
      (((126 * 10 ^ 70 +
        6339546704566372659112137904710737401919035696222146532356842226845049) * 10 ^ 70 +
        3430029873440316777835417392646020438200387252427202793066713941846383) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_86 :
    recurrence2Scalar4Shift.coeff 86 =
      -(((677 * 10 ^ 70 +
        4350467777540509230349782567591682844625486956307348852701923674266790) * 10 ^ 70 +
        2088358867893640472467049121852192908553717294149034984475772481220999) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_87 :
    recurrence2Scalar4Shift.coeff 87 =
      (((3487 * 10 ^ 70 +
        1269394038891769120436471241729617115557003134003193269590255728064305) * 10 ^ 70 +
        6079194888452834767893562544657408478340836101400557263298102736816367) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_88 :
    recurrence2Scalar4Shift.coeff 88 =
      -(((17270 * 10 ^ 70 +
        2325283440812849970014692551783425488824867843782205809907171520181960) * 10 ^ 70 +
        9914415022799093088934038113261352196911385119582643137922035872245001) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_89 :
    recurrence2Scalar4Shift.coeff 89 =
      (((82264 * 10 ^ 70 +
        6424710458043490918212733475246435006896966381434011641974938689636747) * 10 ^ 70 +
        1207106013288676064559146342900242651114265464276791314743181465642720) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_90 :
    recurrence2Scalar4Shift.coeff 90 =
      -(((376609 * 10 ^ 70 +
        1651052255027344796121992613631859451848223454243723851684802326760409) * 10 ^ 70 +
        5602180148090457041998961876639751663642128439860957560316051840971424) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_91 :
    recurrence2Scalar4Shift.coeff 91 =
      (((1654816 * 10 ^ 70 +
        8890006027401721179217198903331669325822110756121780466075609973708580) * 10 ^ 70 +
        4475340428224048817037035678342674029223940045628173844647875888402595) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_92 :
    recurrence2Scalar4Shift.coeff 92 =
      -(((6964723 * 10 ^ 70 +
        6536050681127024896794890253940440543733493389991287483831311247433238) * 10 ^ 70 +
        7414622681773369408577764959903419282924148125069434417079125076714223) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_93 :
    recurrence2Scalar4Shift.coeff 93 =
      (((28001232 * 10 ^ 70 +
        5600710828981232316529543856646221178912878109604018064935274668126741) * 10 ^ 70 +
        5296524838283918413399526196721610316685774998179101737422891746751593) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_94 :
    recurrence2Scalar4Shift.coeff 94 =
      -(((107192092 * 10 ^ 70 +
        7398757946489017181021658142474682316160805681055877922919507160179475) * 10 ^ 70 +
        7186693203990986003903796938410865178129713426083303339555009730919203) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_95 :
    recurrence2Scalar4Shift.coeff 95 =
      (((389235671 * 10 ^ 70 +
        3532731237198965446549254131421819068183864059290875753437127332640908) * 10 ^ 70 +
        5423770483075703856356269207249957870734997743852190774567090095876324) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_96 :
    recurrence2Scalar4Shift.coeff 96 =
      -(((1333826821 * 10 ^ 70 +
        9060140985847171959560827341776370540477501508954917492528827863968278) * 10 ^ 70 +
        1935874296472366679352301682521868531922417161984982497738010096861596) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_97 :
    recurrence2Scalar4Shift.coeff 97 =
      (((4273682332 * 10 ^ 70 +
        1345289257420916655057622008965511165436207484235343111576004231208421) * 10 ^ 70 +
        0085675630820666309181279715685870406734969823199933087024408613692924) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_98 :
    recurrence2Scalar4Shift.coeff 98 =
      -(((12535992643 * 10 ^ 70 +
        2286472439304068497446758696746039783436574392446846679701119441286874) * 10 ^ 70 +
        4983118662333650941487091019437363164164648350940015138477319174314141) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_99 :
    recurrence2Scalar4Shift.coeff 99 =
      (((31854691010 * 10 ^ 70 +
        4646711144772303905176923238998988038485983310557676191064307142583559) * 10 ^ 70 +
        3921939254507263598462679783183527259820886283788350549687194182355800) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_100 :
    recurrence2Scalar4Shift.coeff 100 =
      -(((58085038698 * 10 ^ 70 +
        0922636670654301932156448764699915495701979330514140630490843725940257) * 10 ^ 70 +
        5651517567605260603785799859337195594936368552941677061568534896152426) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_101 :
    recurrence2Scalar4Shift.coeff 101 =
      -(((11092594676 * 10 ^ 70 +
        5809366574079623054101329392458098494986478676412809392182233512113943) * 10 ^ 70 +
        9904635644841830660423188901972240552371684305249374983313165200052298) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_102 :
    recurrence2Scalar4Shift.coeff 102 =
      (((785662849463 * 10 ^ 70 +
        3233642211051996657369262364108989427391958792999920130612152100651545) * 10 ^ 70 +
        3793986599850694816099334987383660239059670142910711039287969081357503) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_103 :
    recurrence2Scalar4Shift.coeff 103 =
      -(((4793830861422 * 10 ^ 70 +
        0856133136521217910551777858759571748999464657212432362840765969332382) * 10 ^ 70 +
        9347286392224408399175978828709260493104261045210625832231000940539495) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_104 :
    recurrence2Scalar4Shift.coeff 104 =
      (((19947969992129 * 10 ^ 70 +
        0717022638777025888526825069076647587727214726782014132188115624870329) * 10 ^ 70 +
        1322899485783108514433569692367657406237546627346526521142248667973913) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_105 :
    recurrence2Scalar4Shift.coeff 105 =
      -(((64736614956644 * 10 ^ 70 +
        7761109761902787623779102613211407054182029763767287389388035750200869) * 10 ^ 70 +
        7392699571601088070631993356379439489554686033802277283369942752812343) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_106 :
    recurrence2Scalar4Shift.coeff 106 =
      (((176451414198773 * 10 ^ 70 +
        2097824728174848406585807218786652927539497134250520342396361839570583) * 10 ^ 70 +
        2444014326122990445962535980773701510010136779112343283317260536528312) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_107 :
    recurrence2Scalar4Shift.coeff 107 =
      -(((517121706558503 * 10 ^ 70 +
        8914747598944494213208677706057553928954190893697851803239419011604465) * 10 ^ 70 +
        2076217627036698591215563216449821537796072096028687099842088525931790) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_108 :
    recurrence2Scalar4Shift.coeff 108 =
      (((2361978978734687 * 10 ^ 70 +
        1457988381483228248000825735711187459608618213895641922562660757031612) * 10 ^ 70 +
        7370977646766327457874457703860649707944630579366706127787356005227531) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_109 :
    recurrence2Scalar4Shift.coeff 109 =
      -(((13458724863628941 * 10 ^ 70 +
        5079722525492674640548845949813878653321724358174778774730134908336662) * 10 ^ 70 +
        5979379592547841718006859917569821155457358474897314048028721521608581) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_110 :
    recurrence2Scalar4Shift.coeff 110 =
      (((64677959695512758 * 10 ^ 70 +
        1081977578682136796015737001506258161616636377202409624993703550963131) * 10 ^ 70 +
        7894479769295427532405765354980984816477024505271024752568561941884596) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_111 :
    recurrence2Scalar4Shift.coeff 111 =
      -(((212967242844476669 * 10 ^ 70 +
        5546210644478320634523177829610861629444521913693552708702960352099508) * 10 ^ 70 +
        9567908333110072906743550992565030716558135085816183300889384153895150) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_112 :
    recurrence2Scalar4Shift.coeff 112 =
      (((240443610218281143 * 10 ^ 70 +
        3749682964459354234995848009507814420447569578272391940041187384318873) * 10 ^ 70 +
        0153804671839625217547670915344577901554843268101876341824486420063394) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_113 :
    recurrence2Scalar4Shift.coeff 113 =
      (((2267541561773284908 * 10 ^ 70 +
        3939889365560510867857950977473745647955300886626559186113703359558274) * 10 ^ 70 +
        1273014568099426658433801465548723398512250163152453478259577162253809) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_114 :
    recurrence2Scalar4Shift.coeff 114 =
      -(((18142304755988123357 * 10 ^ 70 +
        6359201281556774420704914288991581926827856756943795915490201293500069) * 10 ^ 70 +
        8579289917925676900425442931678208307799605692561675543078808706843214) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_115 :
    recurrence2Scalar4Shift.coeff 115 =
      (((69848561368144745554 * 10 ^ 70 +
        7912369318312227722014748718417953173192448611669279521643000074343777) * 10 ^ 70 +
        5264424957651973552667747151462833680661456380512156177476042366516178) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_116 :
    recurrence2Scalar4Shift.coeff 116 =
      -(((104538215104260608071 * 10 ^ 70 +
        1289002736245954350709499876342423972392379074850405325328567732365569) * 10 ^ 70 +
        6522271651043704850842910115271106770564696594687553107812410389862037) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_117 :
    recurrence2Scalar4Shift.coeff 117 =
      -(((554178640417416113524 * 10 ^ 70 +
        2780822207231270495060352833300205211515964224922785819337679128767432) * 10 ^ 70 +
        4468316851116035802216937302049232847836910945765947395092271854770679) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_118 :
    recurrence2Scalar4Shift.coeff 118 =
      (((4908583810953193806921 * 10 ^ 70 +
        2888655718447371697238808842946976104847311574899305159724197993699921) * 10 ^ 70 +
        1300741937809683009465597628068916821339988992770286224007942825033500) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_119 :
    recurrence2Scalar4Shift.coeff 119 =
      -(((19494966363902960463452 * 10 ^ 70 +
        3182533786499838301573646917480859339935255482508839069548624111264922) * 10 ^ 70 +
        4489859488831817647208799142135301655734202544725116522214567692520263) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_120 :
    recurrence2Scalar4Shift.coeff 120 =
      (((37356095933660291681244 * 10 ^ 70 +
        2450260817010308205290856477457988102514783318220959608183674469809730) * 10 ^ 70 +
        7285691198783404198807618041186332709172248989444921230607176042060587) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_121 :
    recurrence2Scalar4Shift.coeff 121 =
      (((66961413538768803151430 * 10 ^ 70 +
        1962382403288320028154612133629128136602487210887860846952040675040956) * 10 ^ 70 +
        6624565126578316284112501653894181846150690242562154307858363500876442) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_122 :
    recurrence2Scalar4Shift.coeff 122 =
      -(((885786530516978850758237 * 10 ^ 70 +
        9689335581693778120268992081347726746780294051749842113229450012661847) * 10 ^ 70 +
        4663279170199862978530683508764812682639689597249092893650107537490387) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_123 :
    recurrence2Scalar4Shift.coeff 123 =
      (((4173993062915167481894119 * 10 ^ 70 +
        8970400578997139147496744609149954016921468507913750314030716159694848) * 10 ^ 70 +
        3555518697977040622815014101432831851977247104592317165050219677748997) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_124 :
    recurrence2Scalar4Shift.coeff 124 =
      -(((12931458246763335033313387 * 10 ^ 70 +
        7615602544278746443349480486516245651068702187173988453884818551057710) * 10 ^ 70 +
        2000704279368923033828849244827973093120857910197465037594428220472371) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_125 :
    recurrence2Scalar4Shift.coeff 125 =
      (((22987502208358228342450294 * 10 ^ 70 +
        2576618862129970086492173294853162298801566855708542795251572940992482) * 10 ^ 70 +
        6126125392946093384173617082157172611111214497593905172495176818936068) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_126 :
    recurrence2Scalar4Shift.coeff 126 =
      (((38266693231324898411679406 * 10 ^ 70 +
        1595100137795160126615462985558850076755357319867425467391726179447992) * 10 ^ 70 +
        7068303583998901136616813252226571989772049878071923447626711853092905) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_127 :
    recurrence2Scalar4Shift.coeff 127 =
      -(((597696774236022150793087238 * 10 ^ 70 +
        6778921576388474487303900602494925433869294305351477232299780741087646) * 10 ^ 70 +
        2062495744898144581892367581741177166272663447980957110445668084128144) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_128 :
    recurrence2Scalar4Shift.coeff 128 =
      (((3239354013177973669663001220 * 10 ^ 70 +
        3010258954604198110800696531260755372669792129069479796104760849273047) * 10 ^ 70 +
        8344174640954154890111354897264552311806630226210559752484863136980863) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_129 :
    recurrence2Scalar4Shift.coeff 129 =
      -(((10898757134750701258762371891 * 10 ^ 70 +
        3361472595839164836569274416005670696510276031997314894766802863037598) * 10 ^ 70 +
        3380069938475895860147255738932150527870385487002942290967384531213614) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_130 :
    recurrence2Scalar4Shift.coeff 130 =
      (((17619134640496159847366732283 * 10 ^ 70 +
        0316153067940015329637061426498787195866023810746829273340352504436476) * 10 ^ 70 +
        5683379526565369117156108508412448511225996395939031853374061007976298) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_131 :
    recurrence2Scalar4Shift.coeff 131 =
      (((43652147732076529651742815567 * 10 ^ 70 +
        1134668973626916406606018212494988887505135027693949711493566166528144) * 10 ^ 70 +
        3735369513879136239079542587498564752836716653396715970848399365379427) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_132 :
    recurrence2Scalar4Shift.coeff 132 =
      -(((428950049396132746726431214347 * 10 ^ 70 +
        9519543437957590360498349257655274107833561669824375750747891839390324) * 10 ^ 70 +
        6497582802397677927314301381002188951422477842573676023516101161548714) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_133 :
    recurrence2Scalar4Shift.coeff 133 =
      (((1685680619860373937091069666314 * 10 ^ 70 +
        6807977149841404090589571505369567335555542828056992189982878402879922) * 10 ^ 70 +
        3728414851910848632626974076968960233448549014882994566468923898934817) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_134 :
    recurrence2Scalar4Shift.coeff 134 =
      -(((4349503717467187809469273212607 * 10 ^ 70 +
        1341739778076233381375907282962102892488971594306589628654735295524652) * 10 ^ 70 +
        9774505733331525881645028315285962039994038486826168128483522373325451) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_135 :
    recurrence2Scalar4Shift.coeff 135 =
      (((7472702473090897706084362386714 * 10 ^ 70 +
        6895108569861340144513053630411362518796777360242848140464553708809335) * 10 ^ 70 +
        4372673697039030033272271819119791173211672853699320160159312183236176) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_136 :
    recurrence2Scalar4Shift.coeff 136 =
      (((1993933187291947925002007404791 * 10 ^ 70 +
        8013310747462155598029470586408219648672786927092743458882020082938575) * 10 ^ 70 +
        0943570347652230632081118123632139680923966566315352327266128117392797) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_137 :
    recurrence2Scalar4Shift.coeff 137 =
      -(((124584896516924649470684210120452 * 10 ^ 70 +
        8976580453049112327313026565040114110482014067728174661972274426847004) * 10 ^ 70 +
        7005204924509355062582191940902117070544679402568115403139579324450398) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_138 :
    recurrence2Scalar4Shift.coeff 138 =
      (((811841651110771166048842083277973 * 10 ^ 70 +
        4474575709902142652439856923513136490977929190270385833179912971071051) * 10 ^ 70 +
        4416794095986186397714933736026088825146528690976914259567291032114682) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_139 :
    recurrence2Scalar4Shift.coeff 139 =
      -(((2737201246020920611196492968188553 * 10 ^ 70 +
        0146153803420954707378702676687881328898671755288718531033635365143605) * 10 ^ 70 +
        4841977996714163371554365655980683729607900190181016388984059721289119) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_140 :
    recurrence2Scalar4Shift.coeff 140 =
      (((1371630350177929619045926209777776 * 10 ^ 70 +
        9137106865814841365508201678788688430510591152495230973065912707993602) * 10 ^ 70 +
        2308295890698159762552748054248589271631826054790827513641822116658252) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_141 :
    recurrence2Scalar4Shift.coeff 141 =
      (((34109710125882371443615013563891072 * 10 ^ 70 +
        2110820989553281927242720007670088345438482638707525834224426234954832) * 10 ^ 70 +
        2528264260321691057821520745246828991117878186822970722409035109065321) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

theorem recurrence2Scalar4Shift_coeff_142 :
    recurrence2Scalar4Shift.coeff 142 =
      -(((158612116352560686676497652046442734 * 10 ^ 70 +
        6488539582773680055500884510683017615930689952539743385442505353050807) * 10 ^ 70 +
        1690200220702762364112132151789159009522097076761919159775018495411517) : ℚ) := by
  unfold recurrence2Scalar4Shift
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

private theorem recurrence2Scalar4Shift_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_143 :
    recurrence2Scalar4Shift.coeff 143 =
      (((108419930357745536501013346989390345 * 10 ^ 70 +
        6411229707662690679082509682314064478728860048731159600822514520745878) * 10 ^ 70 +
        3903594731397371939102492247885287679448094980261073251398014051008176) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (144 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_144 :
    recurrence2Scalar4Shift.coeff 144 =
      (((2021318545246671598443759947002277468 * 10 ^ 70 +
        8151679501760341717657913140850669389300755599258967161001526091239596) * 10 ^ 70 +
        3995492136249832600094773958543050214539536527328203270124231900866424) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 17 = 15 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (145 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_145 :
    recurrence2Scalar4Shift.coeff 145 =
      -(((9884847012675419312024021149813949925 * 10 ^ 70 +
        3505928062414083587872398747920406568681823316993352845742156679418981) * 10 ^ 70 +
        9983971520185798257261382893559164168464818525942605280583169608232881) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 18 = 15 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (146 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_146 :
    recurrence2Scalar4Shift.coeff 146 =
      (((10357959916521959875267852075494662599 * 10 ^ 70 +
        4206912139521487826047431489173113107665790935831864453283238540844362) * 10 ^ 70 +
        6323528404925385809303203149546240453894725431166629701734331412041870) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 19 = 15 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (147 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_147 :
    recurrence2Scalar4Shift.coeff 147 =
      (((99564412451615466620416040414235612175 * 10 ^ 70 +
        3420203503201010868777860180774476595070349583946462333705760904929541) * 10 ^ 70 +
        4807594435680693939429999212462657488574310832377539359029035105668265) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 20 = 15 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (148 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_148 :
    recurrence2Scalar4Shift.coeff 148 =
      -(((546227923098740018700909568638871970786 * 10 ^ 70 +
        8799889341772079690959257610132663087180682047968647641888712652501849) * 10 ^ 70 +
        4151452275340892817332501022824456158301029816664404591215116922626952) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 21 = 15 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (149 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_149 :
    recurrence2Scalar4Shift.coeff 149 =
      (((875513374860753363040955115467210088889 * 10 ^ 70 +
        1913975636832018881790941490210110605666848914655245274945085579587705) * 10 ^ 70 +
        6129003636296767807897295227223917126934280079964893812286783761026820) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 22 = 15 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (150 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_150 :
    recurrence2Scalar4Shift.coeff 150 =
      (((3401451996932809738999458917788568600183 * 10 ^ 70 +
        7150757636191964892988313359711738506813379902032536960129701228466564) * 10 ^ 70 +
        5293618874948608344110830925212180583556848483951707428665140457673869) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 23 = 15 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (151 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_151 :
    recurrence2Scalar4Shift.coeff 151 =
      -(((23289825489057958019758539005142534718059 * 10 ^ 70 +
        2812154376166555691464133038134339923662438144849361768242213749502594) * 10 ^ 70 +
        2118068403261031613635598407508535973092220231804569039503666944805234) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 24 = 15 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (152 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_152 :
    recurrence2Scalar4Shift.coeff 152 =
      (((46148597423960214555185545278343747632925 * 10 ^ 70 +
        6946624665099231725384206755101364505475130238989091770004772506154891) * 10 ^ 70 +
        5664639186898165266273487370532906007403859730862122146963022319764901) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 25 = 15 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (153 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_153 :
    recurrence2Scalar4Shift.coeff 153 =
      (((97296630767805381291513602230612831773471 * 10 ^ 70 +
        0724896822986290193260123474571546818367834928126320514676293718387503) * 10 ^ 70 +
        1871259667137869863709386660402057805059933487153101510962827644851075) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 26 = 15 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (154 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_154 :
    recurrence2Scalar4Shift.coeff 154 =
      -(((852080630877178872895506230031752117607835 * 10 ^ 70 +
        8202759640587931521911667039313031283592576857183650742652624342961202) * 10 ^ 70 +
        8171090655613607349882191518201248307589601526039667718539799942619648) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 27 = 15 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (155 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_155 :
    recurrence2Scalar4Shift.coeff 155 =
      (((1876127067117239826268999761670823650370482 * 10 ^ 70 +
        4432027940263876371706133676408057912192399988697743089406172940308083) * 10 ^ 70 +
        3752042231233034394228815041179201239018289676883100688507262277409858) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 28 = 15 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (156 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_156 :
    recurrence2Scalar4Shift.coeff 156 =
      (((2857458522121874493482454917877703758261838 * 10 ^ 70 +
        6796234199479469093377095587066144404842222444104010610886784363821901) * 10 ^ 70 +
        9932488678171111668835837203516188149068838719169134931175475453851652) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 29 = 15 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (157 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_157 :
    recurrence2Scalar4Shift.coeff 157 =
      -(((30052461072181840827804224294407607869496547 * 10 ^ 70 +
        6319231734959257847513560022200327362947396413427750738111997004248936) * 10 ^ 70 +
        7289495364174025730248698161301047719668124991018870179461519468489342) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 30 = 15 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (158 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_158 :
    recurrence2Scalar4Shift.coeff 158 =
      (((70965473425768327358384177520974589881662388 * 10 ^ 70 +
        2593613598046638750596703954135055815886117601095050087427776052823485) * 10 ^ 70 +
        3681034726229623503366668713131383487864216401825372125284272330145317) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 31 = 15 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (159 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_159 :
    recurrence2Scalar4Shift.coeff 159 =
      (((86103177158371757512340164795243212286433857 * 10 ^ 70 +
        8589639482902323906178925966312809050013179191491288101689473534224433) * 10 ^ 70 +
        5927551967386361656139886794948915342724502059676395373386983679390431) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 32 = 15 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (160 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_160 :
    recurrence2Scalar4Shift.coeff 160 =
      -(((1082181852158121840723071935139182086455279132 * 10 ^ 70 +
        7753696420732647941916530970955480832068520806757339403624172774507953) * 10 ^ 70 +
        3680770087950434694672610994479476247775463896553525757389453679603029) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 33 = 15 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (161 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_161 :
    recurrence2Scalar4Shift.coeff 161 =
      (((2890854795062077784213333208352358802999451251 * 10 ^ 70 +
        3911289632346029598219206250006408915791529244396008794211833299665591) * 10 ^ 70 +
        7627483654859411602770793169332874678915195698867640945237993298764986) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 34 = 15 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (162 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_162 :
    recurrence2Scalar4Shift.coeff 162 =
      (((1442044665568601857081877866730042385576104950 * 10 ^ 70 +
        6033131179720316820385983715590371428872941306151495413184158152720573) * 10 ^ 70 +
        7917982768812455548093823933760839599933191628030920358225619270803804) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 35 = 15 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (163 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_163 :
    recurrence2Scalar4Shift.coeff 163 =
      -(((36781896709884275484131157953832813410991407192 * 10 ^ 70 +
        1038645502571677024798713486991428466830093625456699081586687690762828) * 10 ^ 70 +
        1276957460168705479309434079913238415141934479617076539954607488569644) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 36 = 15 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (164 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_164 :
    recurrence2Scalar4Shift.coeff 164 =
      (((121632310249555637426712626311072414559597416309 * 10 ^ 70 +
        1378084675566524730908094084687664576519378715503102702910797115459182) * 10 ^ 70 +
        3191136418637951090328646812386916215278875316723348871876682211051689) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (165 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_165 :
    recurrence2Scalar4Shift.coeff 165 =
      -(((70553379016254960550638034761694277246044440999 * 10 ^ 70 +
        8619152790056128569398846426635066811825406991384103746712697044629963) * 10 ^ 70 +
        9802213032230680457816638126385403074448023882939743652686260220266088) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 38 = 15 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (166 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_166 :
    recurrence2Scalar4Shift.coeff 166 =
      -(((985581658804627471407197084465565457811112499360 * 10 ^ 70 +
        2382591414009825063119578540400702157698107335479497944035303806538532) * 10 ^ 70 +
        0150074783860199549909801416059335263546293373464189679261896111117519) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 39 = 15 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (167 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_167 :
    recurrence2Scalar4Shift.coeff 167 =
      (((4452159693929128363356009099672895833799577545241 * 10 ^ 70 +
        0469693625232277990545090424867145164200634394702480342621765863605264) * 10 ^ 70 +
        7747712306799927461052013958652716851278759243802507628736914065159063) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 40 = 15 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (168 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_168 :
    recurrence2Scalar4Shift.coeff 168 =
      -(((7239239948300803105487677667458791540367864965945 * 10 ^ 70 +
        2870847012181367099371901095715494244556006601113955130205044474465296) * 10 ^ 70 +
        9537127398955429662092145878307785852530263800059930870780457937825257) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 41 = 15 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (169 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_169 :
    recurrence2Scalar4Shift.coeff 169 =
      -(((15194444414796040705709091335313232141048048071250 * 10 ^ 70 +
        1635705333171719528230110681327087976492640057196687708549375975802991) * 10 ^ 70 +
        8896010288616568145844170202353979870669824139383015743243566544719736) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 42 = 15 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (170 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_170 :
    recurrence2Scalar4Shift.coeff 170 =
      (((125340227630069243021803756266091223498867120439068 * 10 ^ 70 +
        8041547128320093916645264464653576263807970395026950917654065316981127) * 10 ^ 70 +
        8291985914005091501224209826156996668852106529509663125403125575296388) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 43 = 15 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (171 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_171 :
    recurrence2Scalar4Shift.coeff 171 =
      -(((334560326302547415854522837540608598865262862672407 * 10 ^ 70 +
        4215797242277708579673986572948364334211067656927352226626975326583190) * 10 ^ 70 +
        6694530143155059483682731472065640242293621747673649757568465969485162) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 44 = 15 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (172 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_172 :
    recurrence2Scalar4Shift.coeff 172 =
      (((137791903638307144791140118030946860492374853544293 * 10 ^ 70 +
        1911002670305081144082963154791314123111254599035042949664713842712588) * 10 ^ 70 +
        0429989444870315255336657666957541625300172520925989908462806906677109) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 45 = 15 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (173 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_173 :
    recurrence2Scalar4Shift.coeff 173 =
      (((2420976431968944912290697573212369884275288479863036 * 10 ^ 70 +
        4100901138338871723199698975400815888080683513965242576702699126059334) * 10 ^ 70 +
        1784793777080787212231396530203827605550923067959648000975883896561938) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 46 = 15 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (174 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_174 :
    recurrence2Scalar4Shift.coeff 174 =
      -(((10278270093061916721252540398901040585269003006079646 * 10 ^ 70 +
        6646130270199656923626598927918667776848067884336092171199581719805053) * 10 ^ 70 +
        5553370933344425917471512312903717949643932289805574328790496615245115) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 47 = 15 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (175 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_175 :
    recurrence2Scalar4Shift.coeff 175 =
      (((18038120610841587472962667463726025740516546238047397 * 10 ^ 70 +
        7579003040300875410422638985508172315409327650174128408882282213439592) * 10 ^ 70 +
        9252146689000428871459493261207694011922880592826924444211520223803457) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 48 = 15 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (176 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_176 :
    recurrence2Scalar4Shift.coeff 176 =
      (((18041156355619640164283957928671667056775604216930241 * 10 ^ 70 +
        5138551679426566222678139631714673255008310459549353638577149361483090) * 10 ^ 70 +
        6507973064303709646194980547595086750901437035742893177220857994618913) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 49 = 15 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (177 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_177 :
    recurrence2Scalar4Shift.coeff 177 =
      -(((215832999491779827598944849713353309494328366104532017 * 10 ^ 70 +
        1831405008054401486425002307479393801054540916446827043786119388053413) * 10 ^ 70 +
        4793389223210885773291848196499066824679209939789137261372919387834012) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 50 = 15 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (178 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_178 :
    recurrence2Scalar4Shift.coeff 178 =
      (((665824597958332351045753097872240465066190331257392823 * 10 ^ 70 +
        6135273787781107053649530771136020769426492215694586953958696387785013) * 10 ^ 70 +
        4812506894891778301048796712211018685669855621309278865685366415390677) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (179 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_179 :
    recurrence2Scalar4Shift.coeff 179 =
      -(((790869484200933648597426282875745788394222766216829073 * 10 ^ 70 +
        9102268747692990947310205922543562210204365411203400884990320662772455) * 10 ^ 70 +
        9180917981719423249083974559897073727879134406437291145421547387615458) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 52 = 15 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (180 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_180 :
    recurrence2Scalar4Shift.coeff 180 =
      -(((2229420738889432025073858045350336979883945841640483058 * 10 ^ 70 +
        5083190144914343138142490462169915097979279828962295285228724448032406) * 10 ^ 70 +
        2807184184782081612569287124325413363649823070789853837338593160624086) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 53 = 15 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (181 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_181 :
    recurrence2Scalar4Shift.coeff 181 =
      (((14526680550047390528941049287749600439788501321569575267 * 10 ^ 70 +
        2543664074758860014608449530835959215573110962986845804378837009045890) * 10 ^ 70 +
        4517628796454425615649452255231784791092791409584415245234955255327198) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 54 = 15 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (182 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_182 :
    recurrence2Scalar4Shift.coeff 182 =
      -(((38158445693141505328996861216709810406408231875060921251 * 10 ^ 70 +
        3270615697817934155443187803251666450869216900948460995535257517934489) * 10 ^ 70 +
        2144978481500744434982167311285978287343411807522097780360256381763223) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 55 = 15 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (183 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_183 :
    recurrence2Scalar4Shift.coeff 183 =
      (((36677614924570206173531587775417093119928601315657282892 * 10 ^ 70 +
        5363640460923718969260493641261919137323935469750663283689314013688060) * 10 ^ 70 +
        1726194453448200187817415519505595421100767180356706267722472528475755) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 56 = 15 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (184 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_184 :
    recurrence2Scalar4Shift.coeff 184 =
      (((139631300020505561035574559977690660832593835900453777494 * 10 ^ 70 +
        4798543362551711579620553724702686837558801801737433761571399993041583) * 10 ^ 70 +
        9261881033942329199480852278181939169818105819494656734578242608923842) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 57 = 15 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (185 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_185 :
    recurrence2Scalar4Shift.coeff 185 =
      -(((794209501127382386289644861692838894941177873034049019371 * 10 ^ 70 +
        7016317971749573275475948696159660263168945507984842300831880832746516) * 10 ^ 70 +
        9055214903284510763675137559413822958476633599028748693978814450419823) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 58 = 15 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (186 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_186 :
    recurrence2Scalar4Shift.coeff 186 =
      (((2037481516624352133079829212315498213657464946704164104019 * 10 ^ 70 +
        4254777825209655284129819459568531585414408177835291413653770370456550) * 10 ^ 70 +
        3727615050942030291661954191771702808202934126403835514634232508801430) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 59 = 15 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (187 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_187 :
    recurrence2Scalar4Shift.coeff 187 =
      -(((2260089237257892926270357523174335176880496949924776124167 * 10 ^ 70 +
        8151317351416078177233771951574376723976458805732020126729462213165848) * 10 ^ 70 +
        9583698683055509703507503878865721147596549934787006819796427611995172) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 60 = 15 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (188 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_188 :
    recurrence2Scalar4Shift.coeff 188 =
      -(((5233322646569849960173822965802286338961607173369690112710 * 10 ^ 70 +
        5734505392171708018692454472012551013458106447864855441544203236353665) * 10 ^ 70 +
        1290666164008474981076931953178580573076205108277259473947707603120323) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 61 = 15 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (189 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_189 :
    recurrence2Scalar4Shift.coeff 189 =
      (((35002384644545478029089898853434778740620371708785569760508 * 10 ^ 70 +
        7664810884930355776107520760930899839419854614079920506837174157638212) * 10 ^ 70 +
        8531334801957678964821898956949116189477676550138867400102556290017042) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 62 = 15 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (190 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_190 :
    recurrence2Scalar4Shift.coeff 190 =
      -(((99102079935362638978517320742051343305972508274765084738565 * 10 ^ 70 +
        2658568202316803220380268201902781535510140703018234829051613978315122) * 10 ^ 70 +
        4282277547799879784277786612056228237806192516993484031297510994782559) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 63 = 15 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (191 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_191 :
    recurrence2Scalar4Shift.coeff 191 =
      (((152778470363842121663879497835837475367809742351159948172761 * 10 ^ 70 +
        3092089623863695311716306626731528609820229120608855845303614242966461) * 10 ^ 70 +
        0084193460884283200611569194033979217130925669138842324842906344513568) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 64 = 15 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (192 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_192 :
    recurrence2Scalar4Shift.coeff 192 =
      (((42622597331428445003537106563192669645530489250865799015526 * 10 ^ 70 +
        5815401958086437951588811614880421494990321472193316225358528154279198) * 10 ^ 70 +
        8394365278647885033496901929451033237857033598535592145923865841626831) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 65 = 15 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (193 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_193 :
    recurrence2Scalar4Shift.coeff 193 =
      -(((1108176316892556890194767511471607538939153116838090144583406 * 10 ^ 70 +
        3051708278648302524093191826732860917652223613070177381239312949485703) * 10 ^ 70 +
        0607642603043160979960483014442238310355317077609754092523822398842748) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 66 = 15 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (194 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_194 :
    recurrence2Scalar4Shift.coeff 194 =
      (((3967287310818661371058342784316242854354287378304728959233209 * 10 ^ 70 +
        0579865925745752482717191508111247587778761345009618068374783293704023) * 10 ^ 70 +
        4255650978207206665015031511116069892682748103697806718157748071871454) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 67 = 15 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (195 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_195 :
    recurrence2Scalar4Shift.coeff 195 =
      -(((8528131848827713704372861852153561298649129436014225260712562 * 10 ^ 70 +
        7071115615044323088651353332050726417909307970528761967772266229240248) * 10 ^ 70 +
        3048492972253650690145526533169088480672402818346753253042660006768931) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 68 = 15 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (196 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_196 :
    recurrence2Scalar4Shift.coeff 196 =
      (((9341917669020349014738180003092612326816516920901630763817892 * 10 ^ 70 +
        9334398091190506336435966030535465385210243729412780347313710079475691) * 10 ^ 70 +
        5283881268403476263513788489468120716006414477252325798560271665686219) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (197 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_197 :
    recurrence2Scalar4Shift.coeff 197 =
      (((13234056965340719596169109628569644066085232238608347611439670 * 10 ^ 70 +
        4749807397956948293515701743932271521749824197624068049321896412602811) * 10 ^ 70 +
        2229872248523280251836956467817449607272754834521755372331824136708398) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 70 = 15 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (198 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_198 :
    recurrence2Scalar4Shift.coeff 198 =
      -(((102880642230624481798609416043226026135121984851300053617193539 * 10 ^ 70 +
        6232170210263543015106017546153208516341696272165788075303713780624773) * 10 ^ 70 +
        9096517146537669339658537129540042567918281991394183057056981556965539) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 71 = 15 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (199 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_199 :
    recurrence2Scalar4Shift.coeff 199 =
      (((319051702582347653912112364313047234330871922372118782173645246 * 10 ^ 70 +
        9559462039487816408165287880880096267657755374623158864240762717737343) * 10 ^ 70 +
        5804109855732073703408279085053009012953099036568957065299516288037924) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 72 = 15 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (200 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_200 :
    recurrence2Scalar4Shift.coeff 200 =
      -(((659997902108447249470933707955539487519588453048987821042552225 * 10 ^ 70 +
        0091317170138589730641497601998564817411839144782735614000425966231970) * 10 ^ 70 +
        8538614143612104737053867266847665661841142105630185623962323746095932) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 73 = 15 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (201 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_201 :
    recurrence2Scalar4Shift.coeff 201 =
      (((826523375628248415814202240210083760668753735365770210124234295 * 10 ^ 70 +
        5954477383735931159707338694987780674990350846623101641057953734263725) * 10 ^ 70 +
        0770494101955985629955860290394114014731917108046511845806745904095744) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 74 = 15 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (202 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_202 :
    recurrence2Scalar4Shift.coeff 202 =
      (((268360470607741488985375466817237910964099464816523253174963317 * 10 ^ 70 +
        1819225966916553351306600945211002852596734234212037370051614946946463) * 10 ^ 70 +
        1767697345980858593030270994016299834124203419418553238210295134091426) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 75 = 15 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (203 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_203 :
    recurrence2Scalar4Shift.coeff 203 =
      -(((5193245321086838167070949834149537643608500599959957560397885535 * 10 ^ 70 +
        8665214740321199702942359726135762255486989298328286900924701082459504) * 10 ^ 70 +
        4308069359018674972882111807222478963861017504301671830826490003547621) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 76 = 15 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (204 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_204 :
    recurrence2Scalar4Shift.coeff 204 =
      (((18345750438529610931380437124801759757749843658593670799468863670 * 10 ^ 70 +
        8725744758313621932517314422912040900019309443182245564905798902223833) * 10 ^ 70 +
        3904928762040562963630901205987670694580694669596963450925167810853473) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 77 = 15 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (205 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_205 :
    recurrence2Scalar4Shift.coeff 205 =
      -(((44301025481912905175586646457673576360374793832060372773879855688 * 10 ^ 70 +
        0373202398156448005861515930270420346605221593172187858703164043861716) * 10 ^ 70 +
        6137639411088609194004791862873933720750492941974505137206980031160120) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 78 = 15 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (206 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_206 :
    recurrence2Scalar4Shift.coeff 206 =
      (((80690049390591223425173722850045931212832012990759052577985728715 * 10 ^ 70 +
        6826548240627908835250208146490567232047711535861905461536804248325810) * 10 ^ 70 +
        4339888778756467510653673538850601915030834013555557830887731897115121) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 79 = 15 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (207 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_207 :
    recurrence2Scalar4Shift.coeff 207 =
      -(((100007632651447990319014897747128265285905637250794183489712308607 * 10 ^ 70 +
        1460319489487225276714697816910362824858003143504994286110226392136409) * 10 ^ 70 +
        5296263510580508851756676620303458955467180950156835121506969280829585) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 80 = 15 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (208 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_208 :
    recurrence2Scalar4Shift.coeff 208 =
      (((13777440814600569883304124972726668657062315383557319834350167884 * 10 ^ 70 +
        1735670847766130475105990331064593627401104802312674104992514198100034) * 10 ^ 70 +
        5226055733690688270577606460948794940238751728355118915439039915329017) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 81 = 15 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (209 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_209 :
    recurrence2Scalar4Shift.coeff 209 =
      (((384330804778115113451999917440108346659423561229921587219892590616 * 10 ^ 70 +
        1319693861197946527978641313626915158037412181572965539115836256318885) * 10 ^ 70 +
        9211775509895907033627660511750498390173594379015637001136872237920125) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (210 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_210 :
    recurrence2Scalar4Shift.coeff 210 =
      -(((1488165640670238782317002780218022012127274673864237220219444339850 * 10 ^ 70 +
        2740612848487665188963051188352502274699033203272039761096466782128059) * 10 ^ 70 +
        1318256328200117886187020844427971319898740383280760943234406442662129) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (211 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_211 :
    recurrence2Scalar4Shift.coeff 211 =
      (((3928775326638094291914742502976973513752338444505660792540143097147 * 10 ^ 70 +
        2070689148852856453438368124295467823511220300190330923939884387797411) * 10 ^ 70 +
        5945598207678643618709196337437327996388344673427557038828208199423818) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 84 = 15 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (212 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_212 :
    recurrence2Scalar4Shift.coeff 212 =
      -(((8532914843404104624978460029277269302431653783939049982401237327196 * 10 ^ 70 +
        7523993846282045556750667421045077102438366652594356191876568132574631) * 10 ^ 70 +
        2382024845865857245477247126420239505733284001712947092648336720494026) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 85 = 15 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (213 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_213 :
    recurrence2Scalar4Shift.coeff 213 =
      (((16073568929362138444366371877435073112528030556339983051458561346833 * 10 ^ 70 +
        0740347343371276879890088778070116878701117447977826607275056278869097) * 10 ^ 70 +
        8755065380588490205512885144156756947662251152840047614822118156365453) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 86 = 15 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (214 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_214 :
    recurrence2Scalar4Shift.coeff 214 =
      -(((26661758601730006129417186526139315987310691761899571726190935932406 * 10 ^ 70 +
        1298188241231066931578009577480341942674451395664406388434374190985879) * 10 ^ 70 +
        8304723396213528860059340171495594958862371377129102024689160348512385) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (215 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_215 :
    recurrence2Scalar4Shift.coeff 215 =
      (((38638407938448034922246725517316822848263734627567563118298194343582 * 10 ^ 70 +
        5930981479132010848298760070947015557480977310575037468077087773085859) * 10 ^ 70 +
        0957659937586668157385033119177129089605120485440188457006631177545341) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 88 = 15 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (216 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_216 :
    recurrence2Scalar4Shift.coeff 216 =
      -(((46915811157730499780291194072313460578563439877082812798287253323768 * 10 ^ 70 +
        3214746216895218126488485862064386772097113988150945516648771318157885) * 10 ^ 70 +
        0677119367263069228869497170365339694114580098872840107268480600801361) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 89 = 15 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (217 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_217 :
    recurrence2Scalar4Shift.coeff 217 =
      (((40917679726341016148759205179258835271006069518356739090427122251707 * 10 ^ 70 +
        2684457872982525572760766235467668067053632784301846595097053474626748) * 10 ^ 70 +
        1356034953392954690255131415054608893982689052355664098099458429804468) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 90 = 15 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (218 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_218 :
    recurrence2Scalar4Shift.coeff 218 =
      -(((2567960061104802135530853600895543991082191666741602888612815652686 * 10 ^ 70 +
        4211595109070195805197408235872227027295537864648723859971283140886085) * 10 ^ 70 +
        6127151299923237062148731333007996623369177492902715313020793160666858) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 91 = 15 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (219 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_219 :
    recurrence2Scalar4Shift.coeff 219 =
      -(((94882272982341255891761637602606441323270523351677981317832171325200 * 10 ^ 70 +
        2625176105771725940213278796278656455055177894250628089178831375401692) * 10 ^ 70 +
        9046860830822305327819639697404052636188377665319493731964310093038490) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 92 = 15 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (220 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_220 :
    recurrence2Scalar4Shift.coeff 220 =
      (((286151495081751617676204159989801262478607810103248798893087681280940 * 10 ^ 70 +
        8165550583204348120057617794004106964496604498216525824908332361403749) * 10 ^ 70 +
        9065179799695645553320532640987049698543575253480079003398674114311122) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 93 = 15 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (221 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_221 :
    recurrence2Scalar4Shift.coeff 221 =
      -(((610320037790941098849979941332198372705968826947972531772668020612510 * 10 ^ 70 +
        2521495556728346888648632030624802271046424202774587899994954557553556) * 10 ^ 70 +
        1177167119909437158118417568118628351051267300236323282834466516380809) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 94 = 15 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (222 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_222 :
    recurrence2Scalar4Shift.coeff 222 =
      (((1103712461135685285253837287108245518929873239169338234846712942082294 * 10 ^ 70 +
        0251481163496233339358645450906481970986641349852628102142624587955265) * 10 ^ 70 +
        1201652280472944426500981362790451551513015879418075279011785978641454) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 95 = 15 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (223 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_223 :
    recurrence2Scalar4Shift.coeff 223 =
      -(((1789551936949647950546497559448600318666705767343590240183699888331462 * 10 ^ 70 +
        0101846827660236449920337725992527948712750086030720943925110623451629) * 10 ^ 70 +
        2253140601669221940655981006784644751418216685298763166783828905683197) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 96 = 15 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (224 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_224 :
    recurrence2Scalar4Shift.coeff 224 =
      (((2665898986340770259981757556345200951337477788947697273012042658227720 * 10 ^ 70 +
        1204237777080786278732770594891425216874644903341352141388655888857587) * 10 ^ 70 +
        2173756187585166832889156715135197425672712775311436189561155527135082) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 97 = 15 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (225 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_225 :
    recurrence2Scalar4Shift.coeff 225 =
      -(((3694635631810303304831017485315241365779830292608298247325864236021878 * 10 ^ 70 +
        2927831344793771423024316043770246183714029277128969358948061856414769) * 10 ^ 70 +
        2158224349551091003772804545669106456542890076698898813883982430572725) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 98 = 15 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (226 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_226 :
    recurrence2Scalar4Shift.coeff 226 =
      (((4795053354832713641279171837883537321887786523127669535471051850596829 * 10 ^ 70 +
        4663679200434132778822532102005102814986989936928927948073472150539453) * 10 ^ 70 +
        4265502129787088910500963859470541524313913067976954021814819821243084) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 99 = 15 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (227 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_227 :
    recurrence2Scalar4Shift.coeff 227 =
      -(((5845481659448807250347887251569950139616716733547588448720226329807260 * 10 ^ 70 +
        3663558391679332846529515752031700131079861459217585665198537611360723) * 10 ^ 70 +
        0248450765077104098435463084268261339281966471138598908162352513642193) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 100 = 15 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (228 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_228 :
    recurrence2Scalar4Shift.coeff 228 =
      (((6695087413355434278963436130610979867061713792974687187440323555719355 * 10 ^ 70 +
        0971289941124919807085106086058696582812333754243025165782276629938246) * 10 ^ 70 +
        1728239075694753201524862572581389332143807365553795735896239588621984) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 101 = 15 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (229 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_229 :
    recurrence2Scalar4Shift.coeff 229 =
      -(((7185592857191140378901910868699009346327143883097330297266108718101655 * 10 ^ 70 +
        6634333712940207479897678789027724027608560421618891001367696716663626) * 10 ^ 70 +
        9794852124691484858428910995709624973592118350434249467223341407661278) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (230 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_230 :
    recurrence2Scalar4Shift.coeff 230 =
      (((7179747803390456370591800592224333098949730457500471884525271634010917 * 10 ^ 70 +
        9508234848458695181618392773461960292296322340004965685285609086075821) * 10 ^ 70 +
        6993566403621841645016386401781538534507547128005806725642601293277150) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 102 = 14 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (231 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_231 :
    recurrence2Scalar4Shift.coeff 231 =
      -(((6590820565115051223215244093325225291394135346052244044052505286299671 * 10 ^ 70 +
        7038384466984522801350527047204056262037631846078186693777802252991000) * 10 ^ 70 +
        9260674595616957323248682051220905339749202259696005505594231913419530) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 102 = 13 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Shift_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (232 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_232 :
    recurrence2Scalar4Shift.coeff 232 =
      (((5406068495469509730357788307194440990462258844981794942584063214649577 * 10 ^ 70 +
        5205270267115203227309921076530510938654174349625052690180340754536783) * 10 ^ 70 +
        5303911361340902350066032891167001556931232210139590014774575520046949) : ℚ) := by
  unfold recurrence2Scalar4Shift
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
    rw [show 102 = 12 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
