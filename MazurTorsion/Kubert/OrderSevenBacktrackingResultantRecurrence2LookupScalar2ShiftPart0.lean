/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B1_coeff_0
  recurrence2B1_coeff_1
  recurrence2B1_coeff_2
  recurrence2B1_coeff_3
  recurrence2B1_coeff_4
  recurrence2B1_coeff_5
  recurrence2B1_coeff_6
  recurrence2B1_coeff_7
  recurrence2B1_coeff_8
  recurrence2B1_coeff_9
  recurrence2B1_coeff_10
  recurrence2B1_coeff_11
  recurrence2B1_coeff_12
  recurrence2B1_coeff_13
  recurrence2B1_coeff_14
  recurrence2B1_coeff_15
  recurrence2B1_coeff_16
  recurrence2B1_coeff_17
  recurrence2B1_coeff_18
  recurrence2B1_coeff_19
  recurrence2B1_coeff_20
  recurrence2B1_coeff_21
  recurrence2B1_coeff_22
  recurrence2B1_coeff_23
  recurrence2B1_coeff_24
  recurrence2B1_coeff_25
  recurrence2B1_coeff_26
  recurrence2B1_coeff_27
  recurrence2B1_coeff_28
  recurrence2B1_coeff_29
  recurrence2B1_coeff_30
  recurrence2B1_coeff_31
  recurrence2B1_coeff_32
  recurrence2B1_coeff_33
  recurrence2B1_coeff_34
  recurrence2B1_coeff_35
  recurrence2B1_coeff_36
  recurrence2B1_coeff_37
  recurrence2B1_coeff_38
  recurrence2B1_coeff_39
  recurrence2B1_coeff_40
  recurrence2B1_coeff_41
  recurrence2B1_coeff_42
  recurrence2B1_coeff_43
  recurrence2B1_coeff_44
  recurrence2B1_coeff_45
  recurrence2B1_coeff_46
  recurrence2B1_coeff_47
  recurrence2B1_coeff_48
  recurrence2B1_coeff_49
  recurrence2B1_coeff_50
  recurrence2B1_coeff_51
  recurrence2B1_coeff_52
  recurrence2B1_coeff_53
  recurrence2B1_coeff_54
  recurrence2B1_coeff_55
  recurrence2B1_coeff_56
  recurrence2B1_coeff_57
  recurrence2B1_coeff_58
  recurrence2B1_coeff_59
  recurrence2B1_coeff_60
  recurrence2B1_coeff_61
  recurrence2B1_coeff_62
  recurrence2B1_coeff_63
  recurrence2B1_coeff_64
  recurrence2B1_coeff_65
  recurrence2B1_coeff_66
  recurrence2B1_coeff_67
  recurrence2B1_coeff_68
  recurrence2B1_coeff_69
  recurrence2B1_coeff_70
  recurrence2B1_coeff_71
  recurrence2B1_coeff_72
  recurrence2B1_coeff_73
  recurrence2B1_coeff_74
  recurrence2B1_coeff_75
  recurrence2B1_coeff_76
  recurrence2B1_coeff_77
  recurrence2B1_coeff_78
  recurrence2B1_coeff_79
  recurrence2B1_coeff_80
  recurrence2B1_coeff_81
  recurrence2B1_coeff_82
  recurrence2B1_coeff_83
  recurrence2B1_coeff_84
  recurrence2B1_coeff_85
  recurrence2B1_coeff_86
  recurrence2B1_coeff_87
  recurrence2B1_coeff_88
  recurrence2B1_coeff_89
  recurrence2B1_coeff_90
  recurrence2B1_coeff_91
  recurrence2B1_coeff_92
  recurrence2B1_coeff_93
  recurrence2B1_coeff_94
  recurrence2B1_coeff_95
  recurrence2B1_coeff_96
  recurrence2B1_coeff_97
  recurrence2B1_coeff_98
  recurrence2B1_coeff_99
  recurrence2B1_coeff_100
  recurrence2B1_coeff_101
  recurrence2B1_coeff_102
  recurrence2B1_coeff_103
  recurrence2B1_coeff_104
  recurrence2B1_coeff_105
  recurrence2B1_coeff_106
  recurrence2B1_coeff_107
  recurrence2B1_coeff_108
  recurrence2B1_coeff_109
  recurrence2B1_coeff_110
  recurrence2B1_coeff_111
  recurrence2B1_coeff_112
  recurrence2B1_coeff_113
  recurrence2B1_coeff_114
  recurrence2B1_coeff_115
  recurrence2B1_coeff_116
  recurrence2B1_coeff_117
  recurrence2B1_coeff_118
  recurrence2B1_coeff_119
  recurrence2B1_coeff_120
  recurrence2B1_coeff_121
  recurrence2B1_coeff_122
  recurrence2B1_coeff_123
  recurrence2B1_coeff_124
  recurrence2B1_coeff_125
  recurrence2B1_coeff_126
  recurrence2B1_coeff_127
  recurrence2B1_coeff_128
  recurrence2B1_coeff_129
  recurrence2B1_coeff_130
  recurrence2B1_coeff_131
  recurrence2B1_coeff_132
  recurrence2B1_coeff_133
  recurrence2B1_coeff_134
  recurrence2B1_coeff_135
  recurrence2B1_coeff_136
  recurrence2B1_coeff_137
  recurrence2B1_coeff_138
  recurrence2B1_coeff_139
  recurrence2B1_coeff_140
  recurrence2B1_coeff_141
  recurrence2B1_coeff_142
  recurrence2B1_coeff_143
  recurrence2B1_coeff_144
  recurrence2B1_coeff_145
  recurrence2B1_coeff_146
  recurrence2B1_coeff_147
  recurrence2B1_coeff_148
  recurrence2B1_coeff_149
  recurrence2B1_coeff_150
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

theorem recurrence2Scalar2Shift_coeff_0 :
    recurrence2Scalar2Shift.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_1 :
    recurrence2Scalar2Shift.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_2 :
    recurrence2Scalar2Shift.coeff 2 =
      (-30639360 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_3 :
    recurrence2Scalar2Shift.coeff 3 =
      (-534745352016 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_4 :
    recurrence2Scalar2Shift.coeff 4 =
      (-620674798134872 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_5 :
    recurrence2Scalar2Shift.coeff 5 =
      (-11418197174276105368 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_6 :
    recurrence2Scalar2Shift.coeff 6 =
      (2384109950161019549536 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_7 :
    recurrence2Scalar2Shift.coeff 7 =
      (-8342373451761820338365116 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_8 :
    recurrence2Scalar2Shift.coeff 8 =
      (-1812378605507060833273378752 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_9 :
    recurrence2Scalar2Shift.coeff 9 =
      (19660549659925200026410512094064 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_10 :
    recurrence2Scalar2Shift.coeff 10 =
      (-19337911760526632686221325979725972 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_11 :
    recurrence2Scalar2Shift.coeff 11 =
      (16824971678446981232829741686081064054 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_12 :
    recurrence2Scalar2Shift.coeff 12 =
      (-9188854940356392855852732433829781096912 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_13 :
    recurrence2Scalar2Shift.coeff 13 =
      (3759457601858054355081735496383164031307654 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_14 :
    recurrence2Scalar2Shift.coeff 14 =
      (-1151118405413128775116581289767509010030313526 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_15 :
    recurrence2Scalar2Shift.coeff 15 =
      (270302743341955979386472569007394313312911794680 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_16 :
    recurrence2Scalar2Shift.coeff 16 =
      (-49166243905767789708065888629341412510671450135667 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_17 :
    recurrence2Scalar2Shift.coeff 17 =
      (6882778072195135000382868609184940099429222882528746 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_18 :
    recurrence2Scalar2Shift.coeff 18 =
      (-723656170133465455598305468246667738603215190240640710 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_19 :
    recurrence2Scalar2Shift.coeff 19 =
      (52442830644631946538423790239741466188774843369411525639 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_20 :
    recurrence2Scalar2Shift.coeff 20 =
      (-1709861789112135246465205271971173805734604242280072021722 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_21 :
    recurrence2Scalar2Shift.coeff 21 =
      (-153839139118102138436911625875488975025990319750775590134919 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_22 :
    recurrence2Scalar2Shift.coeff 22 =
      (31100433519452612865436328984727503869866321719965202196381430 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_23 :
    recurrence2Scalar2Shift.coeff 23 =
      (-2955078921078864582587362379735891641763960149034077410764188016 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_24 :
    recurrence2Scalar2Shift.coeff 24 =
      (195785537294689977889919744584592878199345634430344884455691771018 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_25 :
    recurrence2Scalar2Shift.coeff 25 =
      (-9837942489700065925175937315458303281513556617766496347948046881128 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_26 :
    recurrence2Scalar2Shift.coeff 26 =
      (384712570728356784530284081192084035473337128025409119086343006598204 : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_27 :
    recurrence2Scalar2Shift.coeff 27 =
      -((1 * 10 ^ 70 +
        1446121550269349499868076784899760795374299996298257146640681124096508) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_28 :
    recurrence2Scalar2Shift.coeff 28 =
      ((20 * 10 ^ 70 +
        3955581127891715535524327169044130138789329953629732450629769329800439) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_29 :
    recurrence2Scalar2Shift.coeff 29 =
      ((394 * 10 ^ 70 +
        6348982565848008906177941765467497839882891726292939686925031574352260) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_30 :
    recurrence2Scalar2Shift.coeff 30 =
      -((63551 * 10 ^ 70 +
        7385303923578045342948376784899635488151040462958818820471300501880253) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_31 :
    recurrence2Scalar2Shift.coeff 31 =
      ((3881229 * 10 ^ 70 +
        8412248534982272953222235656931872741435232425885284022676157579269789) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_32 :
    recurrence2Scalar2Shift.coeff 32 =
      -((166615766 * 10 ^ 70 +
        6148694074551742988006375787422867906935871396185169464455586474207438) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_33 :
    recurrence2Scalar2Shift.coeff 33 =
      ((5601887328 * 10 ^ 70 +
        1644210916860104091962466446812918894739061620680898549971126434774433) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_34 :
    recurrence2Scalar2Shift.coeff 34 =
      -((164168382449 * 10 ^ 70 +
        0286258727443761426445363213819222823355930900957193820481936281214985) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_35 :
    recurrence2Scalar2Shift.coeff 35 =
      ((4959807142065 * 10 ^ 70 +
        1600210178955236543981277413248159790565252657356324581082454178957965) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_36 :
    recurrence2Scalar2Shift.coeff 36 =
      -((167045443773982 * 10 ^ 70 +
        9064675812984057237527348080739739593717034292595601626989605497877081) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_37 :
    recurrence2Scalar2Shift.coeff 37 =
      ((5470735784638216 * 10 ^ 70 +
        7194057442350709265759504464479799697998510562513466699431277987530180) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_38 :
    recurrence2Scalar2Shift.coeff 38 =
      -((148391253896546217 * 10 ^ 70 +
        9898871969946850451395677778450286363916164762167002053479512848027060) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_39 :
    recurrence2Scalar2Shift.coeff 39 =
      ((3109335852260633168 * 10 ^ 70 +
        0155957835552264027108864218445736357864868274120665244805544541411303) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_40 :
    recurrence2Scalar2Shift.coeff 40 =
      -((54617210936240068684 * 10 ^ 70 +
        2696289637362860165945883779391729226344454322580049760757328455095863) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_41 :
    recurrence2Scalar2Shift.coeff 41 =
      ((1264088883244646595617 * 10 ^ 70 +
        5352713801129232837369157521668871528346859190241489117101632695033954) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_42 :
    recurrence2Scalar2Shift.coeff 42 =
      -((47774796911062409063735 * 10 ^ 70 +
        4818456557116431321054409623845579708165240678738844425381191404738942) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_43 :
    recurrence2Scalar2Shift.coeff 43 =
      ((1770107279010636934079751 * 10 ^ 70 +
        1146730944005590433839147899737472306385965160778190647317261994047071) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_44 :
    recurrence2Scalar2Shift.coeff 44 =
      -((50956321396444875796203546 * 10 ^ 70 +
        6677717294167274549386189067840491742555967093965839273719344087972114) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_45 :
    recurrence2Scalar2Shift.coeff 45 =
      ((1104204152752554005408037146 * 10 ^ 70 +
        7064206517511048361598304587836325202572023545865123015089043432498527) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_46 :
    recurrence2Scalar2Shift.coeff 46 =
      -((17045869485603230471483008482 * 10 ^ 70 +
        6138990901272661769123818762043994514629784859327729789969572873223771) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_47 :
    recurrence2Scalar2Shift.coeff 47 =
      ((116849270889357251520008261510 * 10 ^ 70 +
        2772841013390073380416276080622207654929888256220418070713893124753212) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_48 :
    recurrence2Scalar2Shift.coeff 48 =
      ((3950000313079038616590946316461 * 10 ^ 70 +
        1343687988635082512959666247361961827417657279877822232786445251620338) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_49 :
    recurrence2Scalar2Shift.coeff 49 =
      -((231500000020365444430485235557149 * 10 ^ 70 +
        4569813785219599217169602120407458899673168967194013452730252084137461) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_50 :
    recurrence2Scalar2Shift.coeff 50 =
      ((8030920671814158029587590657148565 * 10 ^ 70 +
        0655044108597539472719287445140718590573347051476928327492769297288556) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_51 :
    recurrence2Scalar2Shift.coeff 51 =
      -((227705675059387695528835886035024863 * 10 ^ 70 +
        6563507657929955787345076307318985992307031337583029304317308651127896) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_52 :
    recurrence2Scalar2Shift.coeff 52 =
      ((5631045014602534857391249153614654600 * 10 ^ 70 +
        6256153460554439537032509893808786171324284229114807314161139118605774) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_53 :
    recurrence2Scalar2Shift.coeff 53 =
      -((124322442461715205220453290969963387875 * 10 ^ 70 +
        8579713086001535559436658670634169265637196989629398640113888917023753) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_54 :
    recurrence2Scalar2Shift.coeff 54 =
      ((2485435038092370307446553698254797737312 * 10 ^ 70 +
        8626265023231267186797410219885501761418924153387119859365577445712797) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_55 :
    recurrence2Scalar2Shift.coeff 55 =
      -((45467887128740407506663298389141944438706 * 10 ^ 70 +
        6027154809824897044021377499388768576200089419671454090840554267393793) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_56 :
    recurrence2Scalar2Shift.coeff 56 =
      ((765363891250251296825446481098778602763297 * 10 ^ 70 +
        3010572120200290657291541443032552941375301670766423935873774098246420) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_57 :
    recurrence2Scalar2Shift.coeff 57 =
      -((11822966223175245224715539286922518683547561 * 10 ^ 70 +
        9895677653680832943258709199621927992012534347816511233458638023155777) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_58 :
    recurrence2Scalar2Shift.coeff 58 =
      ((164969185509954581656781654924408684217122665 * 10 ^ 70 +
        7970005042709308318087936010636204267831021790621446087341984807815109) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_59 :
    recurrence2Scalar2Shift.coeff 59 =
      -((1996006906006141581457034176894986388200860003 * 10 ^ 70 +
        3451761792948069240428206724761568245568924670262574119112944295588122) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_60 :
    recurrence2Scalar2Shift.coeff 60 =
      ((18652825165490197828480246059831590039033996323 * 10 ^ 70 +
        7488837068961733999040412656003712702364222878283338986345845930970259) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_61 :
    recurrence2Scalar2Shift.coeff 61 =
      -((66778380423699728231407507224517283857068099104 * 10 ^ 70 +
        9616684381054332378520144061253444701110616342392333768805354139079621) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_62 :
    recurrence2Scalar2Shift.coeff 62 =
      -((2410921831322823616852990269361768613212722753972 * 10 ^ 70 +
        2851447425619262105173286449413650095053652196383263387573625254645682) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_63 :
    recurrence2Scalar2Shift.coeff 63 =
      ((83129328932182959635143814065704210367080113620813 * 10 ^ 70 +
        9582783801282271248782874274623235615334031813705537383471626310556424) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_64 :
    recurrence2Scalar2Shift.coeff 64 =
      -((1792038479274851819110132880727609341081114839259406 * 10 ^ 70 +
        5135805114890858842383820319644928298811923325601359832259452255813181) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_65 :
    recurrence2Scalar2Shift.coeff 65 =
      ((31806537929491054003153088687303411191714739232716304 * 10 ^ 70 +
        4266310983967362818878084807703052674473381181525989621111511805080978) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_66 :
    recurrence2Scalar2Shift.coeff 66 =
      -((499803849784767478393303904837384413427037552011314388 * 10 ^ 70 +
        9680365756888283613396977928297233407323977562812915792600639146659237) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_67 :
    recurrence2Scalar2Shift.coeff 67 =
      ((7169460384311588612936826579496983381762154448234793031 * 10 ^ 70 +
        4778135648651181008677452175049134193898219639266722193364466355114176) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_68 :
    recurrence2Scalar2Shift.coeff 68 =
      -((95389545251772832855358437387528000404510895446436542802 * 10 ^ 70 +
        3127764354393057832441722648625107402665555594002788633234579342726229) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_69 :
    recurrence2Scalar2Shift.coeff 69 =
      ((1188288980407361669238495572529759969105071222681595703733 * 10 ^ 70 +
        9139113346218888874972526680790634638589233836643556642899829815133102) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_70 :
    recurrence2Scalar2Shift.coeff 70 =
      -((13943619835422967741956941985941591187013508124946106664200 * 10 ^ 70 +
        8780455966587953034391593831945095360727974739251200929635789367242475) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_71 :
    recurrence2Scalar2Shift.coeff 71 =
      ((154770970884548426567206627998061848709386448721048730416748 * 10 ^ 70 +
        8539103586825073166366859523777386827871328128578026818290048407214779) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_72 :
    recurrence2Scalar2Shift.coeff 72 =
      -((1630188560479360282932877718168184556291243251139931138991499 * 10 ^ 70 +
        1523076792210168142802010992316285851763740086899463833646523410274483) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_73 :
    recurrence2Scalar2Shift.coeff 73 =
      ((16335036192687585719396096035104601153880926703011485338073879 * 10 ^ 70 +
        2024120580322328656745065546651337673985620196487508977675411854759692) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_74 :
    recurrence2Scalar2Shift.coeff 74 =
      -((156045165693984283672003622929164538074485685802683847489792696 * 10 ^ 70 +
        2015615946199478852804559986363838670631423875065761328300272958330477) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_75 :
    recurrence2Scalar2Shift.coeff 75 =
      ((1423627214328900300764938960098672082919659066263828526160522324 * 10 ^ 70 +
        6604860669312051163466957628348975147602709013248960418576744371383726) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_76 :
    recurrence2Scalar2Shift.coeff 76 =
      -((12422183301159873864480197842177071547894375015208577335174501898 * 10 ^ 70 +
        0321781446962230521245994262384727820431549018436791275056162092258230) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_77 :
    recurrence2Scalar2Shift.coeff 77 =
      ((103796594643458262135234497373911149275913937616668450550255143375 * 10 ^ 70 +
        3033641766420148738040524205976010910560255008746467232799657167453546) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_78 :
    recurrence2Scalar2Shift.coeff 78 =
      -((831358960075386552931968328255640947889688932639861374705574738102 * 10 ^ 70 +
        5396942612524517587375081069193506333195235662107280364739612570837922) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_79 :
    recurrence2Scalar2Shift.coeff 79 =
      ((6388304321729578252629816376971963144704278634183502165071848120053 * 10 ^ 70 +
        2644852357560131869757189857188874218546049840779550527905794361802861) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_80 :
    recurrence2Scalar2Shift.coeff 80 =
      -((47130650093387607201752500283573703216238173481218747550250220699940 * 10 ^ 70 +
        3560528915880285752614979573984814479592606676121869009341622262830236) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_81 :
    recurrence2Scalar2Shift.coeff 81 =
      ((334075059953538692007461242785037991102606443190852743698580743422440 * 10 ^ 70 +
        0304040198589670963668783509019358798314704198971262972542672945398580) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_82 :
    recurrence2Scalar2Shift.coeff 82 =
      -((2276586377443358973351736041883391831174244471780427642972881513823815 * 10 ^ 70 +
        7287070317679756508378741800949628730693697540778565030407888413220001) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_83 :
    recurrence2Scalar2Shift.coeff 83 =
      (((1 * 10 ^ 70 +
        4923338788693767078856223458304747387286028712655908794908472450073198) * 10 ^ 70 +
        2981314447969016796534138141410370352111124540542905622133728610815999) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_84 :
    recurrence2Scalar2Shift.coeff 84 =
      -(((9 * 10 ^ 70 +
        4142123828390364892549316441837219309614411420430553414692595713912616) * 10 ^ 70 +
        0563757076912328732148301131139523801694805357071578269042224518611134) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_85 :
    recurrence2Scalar2Shift.coeff 85 =
      (((57 * 10 ^ 70 +
        1708313202026739568669708367959536131994025139750177802929714309602871) * 10 ^ 70 +
        8097481210454300171286872113987475647213937330832887764381344987579171) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_86 :
    recurrence2Scalar2Shift.coeff 86 =
      -(((334 * 10 ^ 70 +
        2845970040868055590874620502530844446375698679163690870819357524537369) * 10 ^ 70 +
        8690483599212224912474556371118294510420399935363309588672327713053834) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_87 :
    recurrence2Scalar2Shift.coeff 87 =
      (((1882 * 10 ^ 70 +
        1007456708783159368757490096807866769365003855308792346741742860228247) * 10 ^ 70 +
        7156955128842250581300351330325644061069126785051598868458188841659980) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_88 :
    recurrence2Scalar2Shift.coeff 88 =
      -(((10203 * 10 ^ 70 +
        7500108107187663751551036005927328904451845536687091949227528675827178) * 10 ^ 70 +
        2908888593592574492147689671659220275234176041781752268378589773223129) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_89 :
    recurrence2Scalar2Shift.coeff 89 =
      (((53266 * 10 ^ 70 +
        9114485002043276123051070513524990710834741905972637812040230773366566) * 10 ^ 70 +
        1150097993881312869838440895529659563444393885021384143651752905938234) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_90 :
    recurrence2Scalar2Shift.coeff 90 =
      -(((267733 * 10 ^ 70 +
        3980417949143250407062798136922712940118696408925002834834093706037922) * 10 ^ 70 +
        8510885133639972778630647342395662605771966501477552106986471747824538) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_91 :
    recurrence2Scalar2Shift.coeff 91 =
      (((1295385 * 10 ^ 70 +
        9313437747900560737057655232717435350257272836704412233012626829020701) * 10 ^ 70 +
        8422204610015609137601854812288504305978278319975977174341576371256177) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_92 :
    recurrence2Scalar2Shift.coeff 92 =
      -(((6030071 * 10 ^ 70 +
        6159378886240537191228502702867021907539882385133619277416221537102276) * 10 ^ 70 +
        5151107403584689255383324514811426846110525135043589870602383768159095) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_93 :
    recurrence2Scalar2Shift.coeff 93 =
      (((26979982 * 10 ^ 70 +
        1673539501458940267881558439640942375067098072635989458561177961110450) * 10 ^ 70 +
        6455391485730088259865016331228910501472934243306695781647015931645566) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_94 :
    recurrence2Scalar2Shift.coeff 94 =
      -(((115841896 * 10 ^ 70 +
        2037120873067564592195218500912367330290993056804803425357652247152999) * 10 ^ 70 +
        6628435943001104642315779350467453933526253988919557146987331712637452) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_95 :
    recurrence2Scalar2Shift.coeff 95 =
      (((476257052 * 10 ^ 70 +
        1143239016003449025084538154436568697224445874107180854681790855658087) * 10 ^ 70 +
        0515274123705842062964756142728590175233333023301107349690789457839882) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_96 :
    recurrence2Scalar2Shift.coeff 96 =
      -(((1869857193 * 10 ^ 70 +
        6355985733748309426186888303019842241185207194027718768129325852333124) * 10 ^ 70 +
        6214264752052299586398179495598917755641387150381764436890951308600461) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_97 :
    recurrence2Scalar2Shift.coeff 97 =
      (((6989571203 * 10 ^ 70 +
        1088604797805030432218958682734642884405499666510360198841009226333881) * 10 ^ 70 +
        9883022544456756718294065189584433427492078305355599843067104979484936) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_98 :
    recurrence2Scalar2Shift.coeff 98 =
      -(((24784216206 * 10 ^ 70 +
        9475657722290334137609639913787144027492127055882101365821926959758181) * 10 ^ 70 +
        0042609902790254693836204766106846933829316128218102592527323795868159) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_99 :
    recurrence2Scalar2Shift.coeff 99 =
      (((82882646603 * 10 ^ 70 +
        1354637943051234552334295560204158662919468965699800282086090696935428) * 10 ^ 70 +
        9153230782456882354577755331727879133501580385632388280536705143561151) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_100 :
    recurrence2Scalar2Shift.coeff 100 =
      -(((258222254447 * 10 ^ 70 +
        5671289282210113933301242952696873454289258362061617275071183731296924) * 10 ^ 70 +
        3509694800538848202282188866415920814144187130008619091031207635580838) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_101 :
    recurrence2Scalar2Shift.coeff 101 =
      (((727595466207 * 10 ^ 70 +
        0222716993764982102566753654689152758212476097069207853566878064291815) * 10 ^ 70 +
        0636137696465819368879396954482136002026049718405195741453750080972251) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_102 :
    recurrence2Scalar2Shift.coeff 102 =
      -(((1711658626216 * 10 ^ 70 +
        6204932595197004054430198872549680483182037854251972510584405703635054) * 10 ^ 70 +
        4794207448621118850633837163600105945639399969966844630836238325679580) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_103 :
    recurrence2Scalar2Shift.coeff 103 =
      (((2442332152649 * 10 ^ 70 +
        8660835933533851064984133065505410412222920982428115261456698191545986) * 10 ^ 70 +
        6989930690481104566005758078573355396434739400287299026239672412050683) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_104 :
    recurrence2Scalar2Shift.coeff 104 =
      (((4725051565871 * 10 ^ 70 +
        6155209745248854672894627187466797613379821818814270265097466510810779) * 10 ^ 70 +
        6858939872287781772437985468232518506149106406866424463352193168039658) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_105 :
    recurrence2Scalar2Shift.coeff 105 =
      -(((57585275120222 * 10 ^ 70 +
        3252909584231300096091502571162919545842148166495210686720391730789467) * 10 ^ 70 +
        3202922077677384328603307504979867113938237886639120764428399812686315) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_106 :
    recurrence2Scalar2Shift.coeff 106 =
      (((292061694947116 * 10 ^ 70 +
        5337589190786542798173948489761071933213868490595446729966584079614997) * 10 ^ 70 +
        1614726033918597416199710296676252729319434295790969549008924717360039) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_107 :
    recurrence2Scalar2Shift.coeff 107 =
      -(((1085269470577912 * 10 ^ 70 +
        0667703702761794599733656221433788156708490709207602122143642297336692) * 10 ^ 70 +
        5287342576319213186590609995510840903884337826036796494465190985658849) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_108 :
    recurrence2Scalar2Shift.coeff 108 =
      (((3323723087572305 * 10 ^ 70 +
        3379007540558369821499012296017661077083425563855295105011061302153199) * 10 ^ 70 +
        3377346314101327920239969469683941529037441901169018856690266195497077) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_109 :
    recurrence2Scalar2Shift.coeff 109 =
      -(((9838982677870632 * 10 ^ 70 +
        5503773141482241761973206012865441363026572845970473191234070263363422) * 10 ^ 70 +
        5018698324042113474466917782280441766365245874430946064256926019319629) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_110 :
    recurrence2Scalar2Shift.coeff 110 =
      (((37659755337259067 * 10 ^ 70 +
        3307997436362498521377641902770858192180328912562144495628692243100436) * 10 ^ 70 +
        5354770643638007693708682676105878122622624757656724814360090085956587) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_111 :
    recurrence2Scalar2Shift.coeff 111 =
      -(((193208264069036076 * 10 ^ 70 +
        2333505391441866526974364567205559018737437348308044924794635497505436) * 10 ^ 70 +
        1638745838724427106147226974831152268248308000339950475452278514539755) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_112 :
    recurrence2Scalar2Shift.coeff 112 =
      (((977062416033585188 * 10 ^ 70 +
        4008510946582534152002260536807811236147169903780774611066490532492255) * 10 ^ 70 +
        9339223124476265316030144319496616130604539593777873947064372681834634) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_113 :
    recurrence2Scalar2Shift.coeff 113 =
      -(((3862411154100685639 * 10 ^ 70 +
        0520356950069153879906054875360374572362972891916755141027257978482755) * 10 ^ 70 +
        9452115437711379842753958165197347042561844683513130455758096477648574) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_114 :
    recurrence2Scalar2Shift.coeff 114 =
      (((8983345852349687561 * 10 ^ 70 +
        6871108827203937286265591413979981756097892391405875231989952647905422) * 10 ^ 70 +
        0246682126499701819271434393904602523420685842911946474707802567102329) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_115 :
    recurrence2Scalar2Shift.coeff 115 =
      (((11155514447325454388 * 10 ^ 70 +
        0398420417012179873831942534852949268952452092648778325164134355584294) * 10 ^ 70 +
        2775542783851591263502234615808087108409875919006408742473441741268080) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_116 :
    recurrence2Scalar2Shift.coeff 116 =
      -(((229973920882513538278 * 10 ^ 70 +
        9583673798597659819263713479465302727930262905882650438041329949707954) * 10 ^ 70 +
        7497973995462410798348819886194109510200301616142726854681580557944032) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_117 :
    recurrence2Scalar2Shift.coeff 117 =
      (((1190114516797558760126 * 10 ^ 70 +
        7787527470110310348685812226205992677790512270777185157616617314595962) * 10 ^ 70 +
        9646612964633963328512568587393408339168729025281995508394799862536372) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_118 :
    recurrence2Scalar2Shift.coeff 118 =
      -(((3034992545802761261898 * 10 ^ 70 +
        7204428891224278697857571947344692912392678930834959436701922491623290) * 10 ^ 70 +
        7702747454180613893564475640078718709104413866803218403488798018984155) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_119 :
    recurrence2Scalar2Shift.coeff 119 =
      -(((2424975247964737495809 * 10 ^ 70 +
        9050112453022235123295452487744396435127640379898867755193608941677389) * 10 ^ 70 +
        7901104261413873327100611334218493682802401098411792837282630778300287) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_120 :
    recurrence2Scalar2Shift.coeff 120 =
      (((63261781002169866602775 * 10 ^ 70 +
        9798093401083579835545475579549934399563313306535618052343822951329199) * 10 ^ 70 +
        3341331628273404709294573566874247739711236943802507666712853552472252) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_121 :
    recurrence2Scalar2Shift.coeff 121 =
      -(((324626824377471593513105 * 10 ^ 70 +
        3961783022038806890507251617667467480007000323291041478851632673708418) * 10 ^ 70 +
        9824227569654692475154243680682213081033029328084956270862359049940740) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_122 :
    recurrence2Scalar2Shift.coeff 122 =
      (((917067146303566613955597 * 10 ^ 70 +
        9823396835108955785770742303744518318961366940103057955093420994980056) * 10 ^ 70 +
        7437718090541891171815855204141577132457858969985377368691914848069123) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_123 :
    recurrence2Scalar2Shift.coeff 123 =
      -(((589179744920038417496367 * 10 ^ 70 +
        8377045871717179073044593873321862934676038909451070871643553229207968) * 10 ^ 70 +
        8573658888429817085243717416807064668728525401187074022263175701818963) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_124 :
    recurrence2Scalar2Shift.coeff 124 =
      -(((9940419059325629392125959 * 10 ^ 70 +
        5204343547545307747945748797267504131172198536774790606681130729513587) * 10 ^ 70 +
        5187583125490449299969823143110436116314135426785510364262098141931705) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_125 :
    recurrence2Scalar2Shift.coeff 125 =
      (((69907574013719580843706269 * 10 ^ 70 +
        4975847895484901645550197946817058332034584504163909736403546365037339) * 10 ^ 70 +
        7181272358586156543725205029421707842418389984238681315541917758242123) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_126 :
    recurrence2Scalar2Shift.coeff 126 =
      -(((280235160599829932719799214 * 10 ^ 70 +
        2493214548127065231670591024012561022091496607501601196736064492724548) * 10 ^ 70 +
        6298872911679450124732107407381996437213660529832418892490837859532900) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_127 :
    recurrence2Scalar2Shift.coeff 127 =
      (((618961274920089813981130057 * 10 ^ 70 +
        1223612210528907990048847576553058882211235745976763074666803321644013) * 10 ^ 70 +
        5020062321384508365906666304698722545282247564433492030368035283705383) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_128 :
    recurrence2Scalar2Shift.coeff 128 =
      (((639613423931727807308427854 * 10 ^ 70 +
        5518683773533808614266230529765863421394490614864059161866619498446723) * 10 ^ 70 +
        7007986371089127761316767748941506184706393275221278418348913612000143) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_129 :
    recurrence2Scalar2Shift.coeff 129 =
      -(((12094580384531467940598100375 * 10 ^ 70 +
        0411666427172980725714308245445118879875139947680765883985980311090652) * 10 ^ 70 +
        9001384274689974361761170579425058785692557918509435609620331030170805) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_130 :
    recurrence2Scalar2Shift.coeff 130 =
      (((50893754354500160730030784314 * 10 ^ 70 +
        1586979512495720992700101910779796886110179028642876312830944734908928) * 10 ^ 70 +
        1144402182290316125059431570482128551764274950576702248684234560465394) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_131 :
    recurrence2Scalar2Shift.coeff 131 =
      -(((92748941501759725112647907905 * 10 ^ 70 +
        1507781012166304940490516546078939205478619490512492156329850452612755) * 10 ^ 70 +
        5367559612196915256750666488827750541689674348613357164303965647477936) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_132 :
    recurrence2Scalar2Shift.coeff 132 =
      -(((48511968792295582960636262830 * 10 ^ 70 +
        1600003177186736737068385932673117960218049748145086527991104976265552) * 10 ^ 70 +
        5713041599633067144774818034277700029218311991043402471010152525554213) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_133 :
    recurrence2Scalar2Shift.coeff 133 =
      (((210583269402857957439837818480 * 10 ^ 70 +
        7000047394960298962917330680458169586298147217594695197807942018428166) * 10 ^ 70 +
        4479501757173687423218122511460807867761282803513420335875599312232650) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_134 :
    recurrence2Scalar2Shift.coeff 134 =
      (((3085775300183915003902235602180 * 10 ^ 70 +
        9566141169334511498261277670271592171175018571480425427826088669099546) * 10 ^ 70 +
        1901358033150191441441698476133542849502986402800510981467778941915388) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_135 :
    recurrence2Scalar2Shift.coeff 135 =
      -(((11583961716592760563338768679485 * 10 ^ 70 +
        3586039554552337947215626507050357113525274078641307779464077796457963) * 10 ^ 70 +
        4415076000358549687614175906693200545591099949618493761238278263659616) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_136 :
    recurrence2Scalar2Shift.coeff 136 =
      -(((70662635599496896931302197763308 * 10 ^ 70 +
        7887215841079639807879760698957696497596547085962958050336913160878426) * 10 ^ 70 +
        1691415802531662905659074129450495575161646852371105881098943913382956) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_137 :
    recurrence2Scalar2Shift.coeff 137 =
      (((763446817768626885631262541340843 * 10 ^ 70 +
        0529519975201731622157740310107351907313108175433876874942604749837166) * 10 ^ 70 +
        6728167881392002229648393622483380045028706531721958585017176254565271) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_138 :
    recurrence2Scalar2Shift.coeff 138 =
      -(((2640850180344085392491031368323943 * 10 ^ 70 +
        8591081110234513960253391719859527042785068785429074891627597182342459) * 10 ^ 70 +
        1404056232740355841721390733427170728893827349609895578481915106046912) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_139 :
    recurrence2Scalar2Shift.coeff 139 =
      -(((787918027944953263694494473227229 * 10 ^ 70 +
        0904009878929421916165703835013894524168412287395224190700745531056093) * 10 ^ 70 +
        0016816978438115066145961466123739700363902754148658651003966302164004) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_140 :
    recurrence2Scalar2Shift.coeff 140 =
      (((45793263280425161743413372396073555 * 10 ^ 70 +
        6640302276411697264095762595872235155565126397722670139418523800933616) * 10 ^ 70 +
        3943310065814532899751124169015948581470821813496383299095354473920356) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_141 :
    recurrence2Scalar2Shift.coeff 141 =
      -(((178764458817510967509749414582143754 * 10 ^ 70 +
        1910421014007116014905012115358007562625438046073537120419729770393734) * 10 ^ 70 +
        1143153016702216921620882616747782961658005561181109333897300101408325) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_142 :
    recurrence2Scalar2Shift.coeff 142 =
      (((55387168144047051379291124698746757 * 10 ^ 70 +
        2750200651579577282125712265333463164236805443268536115670649056068612) * 10 ^ 70 +
        2861158124089423950993789141603834819696872854150946899570697508088294) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_143 :
    recurrence2Scalar2Shift.coeff 143 =
      (((2218911542338593079176446711049465047 * 10 ^ 70 +
        4873042005076401221091607228860028832147078334899356658041432078427794) * 10 ^ 70 +
        2001119376443342221468108970434968179223902691636746440869455405750868) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_144 :
    recurrence2Scalar2Shift.coeff 144 =
      -(((8594290020773229653955927195031120305 * 10 ^ 70 +
        1422541622589986873782108747616650429802743860584487358338233388205952) * 10 ^ 70 +
        6807779361233497173828077331762781893527770550039846040611381124691019) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_145 :
    recurrence2Scalar2Shift.coeff 145 =
      -(((116765331758778626433959261480135219 * 10 ^ 70 +
        0063737411870804461701539235766049783024073874213102563926108253274400) * 10 ^ 70 +
        4718519875175067301512743025714478212012423048597320568285295835241887) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_146 :
    recurrence2Scalar2Shift.coeff 146 =
      (((117762499851320962580026952924706043145 * 10 ^ 70 +
        1178035505166109255384995733711072115405296331866538302210591763291933) * 10 ^ 70 +
        2926619721200292792654580845834093317063709354138401887647429296259182) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_147 :
    recurrence2Scalar2Shift.coeff 147 =
      -(((414816725474779920178333415632260705529 * 10 ^ 70 +
        5523743450111291328352426216095415747560322167077770504466838504738674) * 10 ^ 70 +
        1227008247910012667616459839067141716638437984605598537644498093077295) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_148 :
    recurrence2Scalar2Shift.coeff 148 =
      -(((108146965729564513292411597220743667896 * 10 ^ 70 +
        8893747804084069140166978728229964236227489401707101687374924772934288) * 10 ^ 70 +
        8784619546937960221622565169726342167690467321633940166217052158925761) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_149 :
    recurrence2Scalar2Shift.coeff 149 =
      (((5865614222618395183847239417026264004913 * 10 ^ 70 +
        3280235548865134254168322401429780170305215843491419637449438861272383) * 10 ^ 70 +
        8120484133837002321273484690882978245548026495833854664003389801915352) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

theorem recurrence2Scalar2Shift_coeff_150 :
    recurrence2Scalar2Shift.coeff 150 =
      -(((19367884341121349276447506375695626084245 * 10 ^ 70 +
        4021350988099213472642717401174820501885750061013236389422484469840718) * 10 ^ 70 +
        0303399919240001736105572493936414222996596858123965296530748617898825) : ℚ) := by
  unfold recurrence2Scalar2Shift
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

private theorem recurrence2Scalar2Shift_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_151 :
    recurrence2Scalar2Shift.coeff 151 =
      -(((6795926066983366876179382948602410037547 * 10 ^ 70 +
        9365949703528577513668238978948385613263514052250562559266185363754155) * 10 ^ 70 +
        1368017374238040525050689408814836860251108645218488654763255770176754) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (152 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_152 :
    recurrence2Scalar2Shift.coeff 152 =
      (((269118480939463599395844268682583143624931 * 10 ^ 70 +
        7680562067475054279540570654269263108820328297457305194634563099063648) * 10 ^ 70 +
        1969207812832099291336936709634483745337079448810097436946242181803325) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 25 = 23 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (153 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_153 :
    recurrence2Scalar2Shift.coeff 153 =
      -(((861629875535736198524309919896496483526335 * 10 ^ 70 +
        8978479755939206836283077583260017991710841195596804553049382198234169) * 10 ^ 70 +
        2553373338992559604052066363062368830269797954651558535613549809091761) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 26 = 23 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (154 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_154 :
    recurrence2Scalar2Shift.coeff 154 =
      -(((317498696960507830868892740729744498111167 * 10 ^ 70 +
        1701428666497134133939098505067224308489770612708232423251016468144489) * 10 ^ 70 +
        6091911568593487179513153193668027368885741417388112738926550196331192) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 27 = 23 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (155 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_155 :
    recurrence2Scalar2Shift.coeff 155 =
      (((11860638941248606762639933930990231342981802 * 10 ^ 70 +
        9377278707973965700377510421633044563342291749906922832559754088507179) * 10 ^ 70 +
        7365384083539580755946786524143137372756634018850767814450665316505424) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 28 = 23 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (156 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_156 :
    recurrence2Scalar2Shift.coeff 156 =
      -(((38942493945039813944633037945585538406057793 * 10 ^ 70 +
        8225582650190568019468568557581504068060060982862785392230516561905951) * 10 ^ 70 +
        0952738002085036757258817296637468658098626233507462878532103866968300) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 29 = 23 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (157 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_157 :
    recurrence2Scalar2Shift.coeff 157 =
      -(((2744697383340145051538781152788734634331729 * 10 ^ 70 +
        7358712742768445359673008694458438785143535256623451988337048004046461) * 10 ^ 70 +
        2665704690002788992630214466621558042706135960557447329640872669644717) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 30 = 23 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (158 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_158 :
    recurrence2Scalar2Shift.coeff 158 =
      (((480201032003374779351098062464456644241820309 * 10 ^ 70 +
        0951247105147283363144530691364450705214431896208500162284404359864827) * 10 ^ 70 +
        0675277909408055282619278860156917524846091200511923068307586168542109) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 31 = 23 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (159 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_159 :
    recurrence2Scalar2Shift.coeff 159 =
      -(((1754368785866049143684272158319487508128295644 * 10 ^ 70 +
        8823671725466450318902734182644619809174045906719683060222717508674433) * 10 ^ 70 +
        2266987478424832268195903164999534372800991141043328733652598192186654) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 32 = 23 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (160 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_160 :
    recurrence2Scalar2Shift.coeff 160 =
      (((961230610360929399358758680188191225162359806 * 10 ^ 70 +
        8371682042160144322750758765382084752286294880024102354271361455131898) * 10 ^ 70 +
        6672091966140978414483624717346048029633074228443942138497200595812241) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 33 = 23 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (161 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_161 :
    recurrence2Scalar2Shift.coeff 161 =
      (((16501961545096185034824506402227274272058582513 * 10 ^ 70 +
        7027632609473932800830877293394640224082864194389457921288796380976591) * 10 ^ 70 +
        8645680835705209768861476482982223267335667380661461408013694254705120) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 34 = 23 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (162 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_162 :
    recurrence2Scalar2Shift.coeff 162 =
      -(((73153133014968027974378192649184541871490644664 * 10 ^ 70 +
        6022525529029163293972360895007648620848646893459831326736575725801511) * 10 ^ 70 +
        7674894144477409270355072418969727499408314284999492489533355728467469) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 35 = 23 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (163 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_163 :
    recurrence2Scalar2Shift.coeff 163 =
      (((95069064124006197629645974469058429167960919486 * 10 ^ 70 +
        4303634315905316247067946599844267823633704535008246640341021833778028) * 10 ^ 70 +
        8155915090165431779925238544343529025406638325881766847889481749182106) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 36 = 23 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (164 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_164 :
    recurrence2Scalar2Shift.coeff 164 =
      (((429808669129348994270027070516776511312449235695 * 10 ^ 70 +
        9716064033878360763262898462875020816696495576272651161692756591116850) * 10 ^ 70 +
        9947773751380015052655591225294666024177409400382632350739234405117127) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 37 = 23 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (165 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_165 :
    recurrence2Scalar2Shift.coeff 165 =
      -(((2636615160041950292703266427876666790769292136111 * 10 ^ 70 +
        4977542953105286982725787578267695167649104186080309678485558160412885) * 10 ^ 70 +
        2240760778058620516583258956185070558597056489414757379565498032070564) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 38 = 23 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (166 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_166 :
    recurrence2Scalar2Shift.coeff 166 =
      (((5541000506154028671356461304519356544249916019326 * 10 ^ 70 +
        0117718271988014316965909004195424430871425679691015525578205806815616) * 10 ^ 70 +
        7143959811815955984984372644948935387680437022704003499021309055344450) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 39 = 23 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (167 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_167 :
    recurrence2Scalar2Shift.coeff 167 =
      (((5811994733947214926841421562311510596868548393529 * 10 ^ 70 +
        6720222561346358603847913365381860341316333783199565157798934945292688) * 10 ^ 70 +
        0007321632238484448033181100082881326618125892276676963450204914486126) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 40 = 23 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (168 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_168 :
    recurrence2Scalar2Shift.coeff 168 =
      -(((77306201594417622671044673798714537249838074377962 * 10 ^ 70 +
        4680953663927573237803623188214607052701967457703803696074452033795001) * 10 ^ 70 +
        8170571588674343086312313653650238240951182204719745464555409906742125) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 41 = 23 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (169 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_169 :
    recurrence2Scalar2Shift.coeff 169 =
      (((235812599645867128192047690954346197590636827136253 * 10 ^ 70 +
        0118011411859944239695469406571241720703047739855753004315781342003122) * 10 ^ 70 +
        1081996355962033966231375229289990282634077709622839679933851574868589) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 42 = 23 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (170 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_170 :
    recurrence2Scalar2Shift.coeff 170 =
      -(((149073897145536265992507008511914529067440841917622 * 10 ^ 70 +
        0561961215458675138068246099988939922680017683564414622336061291208765) * 10 ^ 70 +
        9703425717694818010333110412058273704043279319367986089242697705812401) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 43 = 23 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (171 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_171 :
    recurrence2Scalar2Shift.coeff 171 =
      -(((1664350583918369772615194644838546748934114008550875 * 10 ^ 70 +
        4972882469232619188300384280984196150740471247125331921441098701972462) * 10 ^ 70 +
        1768285373320407518568266209231361564924682718191179469697458958255455) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 44 = 23 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (172 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_172 :
    recurrence2Scalar2Shift.coeff 172 =
      (((7684661235925527157424006662795112741819659531332719 * 10 ^ 70 +
        8342965667209532391151003421388940749752228561425837876934609876882454) * 10 ^ 70 +
        4128546574302132676043720077699530462092806116139210570041133145084472) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 45 = 23 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (173 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_173 :
    recurrence2Scalar2Shift.coeff 173 =
      -(((13893144776536284050605699241921721149220848321220863 * 10 ^ 70 +
        2151551154088169821487002401444981438753362086633993032140891197804926) * 10 ^ 70 +
        5011334536897536318743177847071688997163863188314707909241114305247593) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 46 = 23 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (174 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_174 :
    recurrence2Scalar2Shift.coeff 174 =
      -(((16425900106138680205982012139118684526589089756472923 * 10 ^ 70 +
        4173324678732962215502294751335012303308077730709300791293176606816542) * 10 ^ 70 +
        5177276099293136330802484330469395171222821364692087991538364788159655) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 47 = 23 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (175 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_175 :
    recurrence2Scalar2Shift.coeff 175 =
      (((185216301019727820223929994447601967435427860539045744 * 10 ^ 70 +
        1021848339535431589678305940902890507701712323066732703901195927244081) * 10 ^ 70 +
        7256681355034333824314669328541886142839196742263734130055210646101459) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 48 = 23 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (176 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_176 :
    recurrence2Scalar2Shift.coeff 176 =
      -(((560738377603631012465065176346687126588161405279710607 * 10 ^ 70 +
        3600788585574904377627323771489337947315163899432932255723987416023187) * 10 ^ 70 +
        2589707074232996695749253780788401160472187442879266585573233049388937) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 49 = 23 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (177 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_177 :
    recurrence2Scalar2Shift.coeff 177 =
      (((547393479154127547617949835781020668216649426300945390 * 10 ^ 70 +
        0453178626042243224292109131289901622566518008844190836870715705379019) * 10 ^ 70 +
        6407400791540944402702757483141692692688639664761939475885682795413413) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 50 = 23 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (178 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_178 :
    recurrence2Scalar2Shift.coeff 178 =
      (((2638193909353888995049011559310224800195399326548026845 * 10 ^ 70 +
        3802549442384166970049651915157758420605652298983496770941112577747424) * 10 ^ 70 +
        9476780367615223058725657923407587042612694617217300291658215938561841) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (179 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_179 :
    recurrence2Scalar2Shift.coeff 179 =
      -(((14603639700175327433504358669284916120000830422343175896 * 10 ^ 70 +
        8466675922211580243469288719870892836826147848417821204009106371085099) * 10 ^ 70 +
        3720133167027646553226655193459672625409887452768052418964439757620368) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 52 = 23 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (180 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_180 :
    recurrence2Scalar2Shift.coeff 180 =
      (((34310567269912866521598674789912148183971041436852941815 * 10 ^ 70 +
        7053416967966369410605177862246521429223953882305879329058572579553251) * 10 ^ 70 +
        7334801011149186019785838557554175520980350952442175099499968945443714) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 53 = 23 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (181 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_181 :
    recurrence2Scalar2Shift.coeff 181 =
      -(((14298803698542203376064095770323381685180677826292922639 * 10 ^ 70 +
        7718773309422110931641790375564716266486357051665583756598787428932585) * 10 ^ 70 +
        2228402929668787587283706176790187584457403746196259560057381478775747) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 54 = 23 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (182 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_182 :
    recurrence2Scalar2Shift.coeff 182 =
      -(((215364530751175360848511623707893175178187180611006451044 * 10 ^ 70 +
        3185297311360971262584108291873568489147808467967054397839656302923433) * 10 ^ 70 +
        4471340427283351777334778686501853133526277194608181469870809265920669) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 55 = 23 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (183 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_183 :
    recurrence2Scalar2Shift.coeff 183 =
      (((936328339829682716317175186202729232581422609172756582908 * 10 ^ 70 +
        8834975493646272841971940114280287175117426349971145151321851856320394) * 10 ^ 70 +
        7460758690233227994560256311227821915881511567754605438023272456742039) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 56 = 23 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (184 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_184 :
    recurrence2Scalar2Shift.coeff 184 =
      -(((1955435089990704365937779673882434881589438772667610219621 * 10 ^ 70 +
        5201315720496108608272237718597309156845646366374629736528588822575677) * 10 ^ 70 +
        3662578805282840077831470450964148625011355538202557232255312688061432) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 57 = 23 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (185 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_185 :
    recurrence2Scalar2Shift.coeff 185 =
      (((514499706413231539646841181570618279504837096069007155633 * 10 ^ 70 +
        7224861619003360240692088893664803740373511086223675693267427485222427) * 10 ^ 70 +
        8475258182286869096618037328476514880842133356009110351099204975634775) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 58 = 23 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (186 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_186 :
    recurrence2Scalar2Shift.coeff 186 =
      (((12372594893599412754703973962560196240690866233577169987767 * 10 ^ 70 +
        8343574642243166720466683142054664989042502175685787650038459160041471) * 10 ^ 70 +
        1565984236814136199398980365273876191322750410740393855549208019995947) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 59 = 23 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (187 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_187 :
    recurrence2Scalar2Shift.coeff 187 =
      -(((51270617941752662346596558150620083043519857040597648862511 * 10 ^ 70 +
        4605042575602511574630721155437187107833385933681412927962845626167277) * 10 ^ 70 +
        9925529926752855654773121839351115267502925462553123630498732559513142) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 60 = 23 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (188 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_188 :
    recurrence2Scalar2Shift.coeff 188 =
      (((109569377601414025361513298892080527383895023791540006915407 * 10 ^ 70 +
        8944390221521484556191312851881415868541257715653709716140995466489153) * 10 ^ 70 +
        0225819585000534752476143983189171737990152556821911507485953436114880) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 61 = 23 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (189 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_189 :
    recurrence2Scalar2Shift.coeff 189 =
      -(((64950541109100145618949843057337794195981728531126035630885 * 10 ^ 70 +
        6068382654913313980557797586739558919091522668489471005487514617074166) * 10 ^ 70 +
        7384160733775437057172265453117758339679193979291489844211269743424626) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 62 = 23 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (190 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_190 :
    recurrence2Scalar2Shift.coeff 190 =
      -(((498595228615811658362016745132672390912931894568349168418369 * 10 ^ 70 +
        8975277966075134564156469555496455152399377410311156968571270187677209) * 10 ^ 70 +
        3453407869965595197976475484725491450012362524302274538384292720845263) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 63 = 23 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (191 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_191 :
    recurrence2Scalar2Shift.coeff 191 =
      (((2355736406141405870342494739415640037495554621444502741694944 * 10 ^ 70 +
        7469610532469451037557432082841118857737540199926232331331761173604263) * 10 ^ 70 +
        6506608146583966818536799474872495796099617630690205497267544347959252) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 64 = 23 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (192 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_192 :
    recurrence2Scalar2Shift.coeff 192 =
      -(((5788478372450806695389387195091178755661978137215106603670614 * 10 ^ 70 +
        7323808503235470603301532133526314648703304181534455247671661564557698) * 10 ^ 70 +
        7106332512167404966551680116894597648142082075355934488902123214875713) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 65 = 23 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (193 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_193 :
    recurrence2Scalar2Shift.coeff 193 =
      (((7060332067746918285972289429428230666629509660765369131674219 * 10 ^ 70 +
        1121625757449460979944896354963459327407146906793777415757818621200545) * 10 ^ 70 +
        0445251609436428145606884794229994766450407648154300907808278352923702) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 66 = 23 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (194 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_194 :
    recurrence2Scalar2Shift.coeff 194 =
      (((9559630197735222639911257093693553874243036600309077782440397 * 10 ^ 70 +
        7870477321363276088787619379149643131170284279156928319916807158377058) * 10 ^ 70 +
        0539529999176669014987727853758739781274033653164545457268063858175341) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 67 = 23 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (195 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_195 :
    recurrence2Scalar2Shift.coeff 195 =
      -(((80857572653422753480029033911645202442516117947894239049997887 * 10 ^ 70 +
        9607911957583569827927355099258353605705347998496325331529520873234276) * 10 ^ 70 +
        3463010824393264351282590248398722488993564503165193797973479353126949) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 68 = 23 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (196 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_196 :
    recurrence2Scalar2Shift.coeff 196 =
      (((253118345400424050365763043956413517587284084435059867399135921 * 10 ^ 70 +
        6804495450759907617632829554393091789995357176544717837951468999829007) * 10 ^ 70 +
        3463937056783310804610140261749132012528146453282846569159875474578773) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (197 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_197 :
    recurrence2Scalar2Shift.coeff 197 =
      -(((489982380019561085711090536349657150209489970852968946438069283 * 10 ^ 70 +
        2676858885142467644308833697403348085593484731403483948273456359301067) * 10 ^ 70 +
        8687964793617567373018256539359645463088009969974951218248356958322593) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 70 = 23 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (198 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_198 :
    recurrence2Scalar2Shift.coeff 198 =
      (((397249819807995605994465814098289009768631792961851523597067578 * 10 ^ 70 +
        7302863506366374776074110863978264308797350342082216454623353796466056) * 10 ^ 70 +
        2836751598462571455592317309585180446160185398413208700720932122446467) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 71 = 23 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (199 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_199 :
    recurrence2Scalar2Shift.coeff 199 =
      (((1299382299019606193962326425085955638831372478784414950782688019 * 10 ^ 70 +
        0087732478917281216347717560399866029570955027436671902390716056693132) * 10 ^ 70 +
        1970433115924146071572927865066334072060144175817338524859626958586189) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 72 = 23 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (200 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_200 :
    recurrence2Scalar2Shift.coeff 200 =
      -(((7250289458326654614164573132928498667803644199755491170658546771 * 10 ^ 70 +
        2637981152741310883246070684559740805109539246646619212228634021559035) * 10 ^ 70 +
        2186754171839869821785184769619885463770946646529007208536888157302914) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 73 = 23 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (201 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_201 :
    recurrence2Scalar2Shift.coeff 201 =
      (((20680748176253943790049793588622396198711795642160841582417806641 * 10 ^ 70 +
        8407187033120157421829920618299063371825753031273614791624403325881745) * 10 ^ 70 +
        7346204508627949253311722151456693335345101176739889756626336215878356) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 74 = 23 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (202 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_202 :
    recurrence2Scalar2Shift.coeff 202 =
      -(((40079428343563468284083267537336367834117063767591034528933793473 * 10 ^ 70 +
        4055735287008250201803267119975203478360454791821311059606054544769675) * 10 ^ 70 +
        9072487163009131570638246117124720667316241959060607888539031602281674) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 75 = 23 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (203 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_203 :
    recurrence2Scalar2Shift.coeff 203 =
      (((43807165950837305325730549061673597726032293126093872156252910256 * 10 ^ 70 +
        5219814379118993470356153798356611319437918734862402356251372620642897) * 10 ^ 70 +
        5676957510218541572604124732642023611093860538580647426951829990034127) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 76 = 23 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (204 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_204 :
    recurrence2Scalar2Shift.coeff 204 =
      (((40850468188280832979421005954474424398901208048608250643047381349 * 10 ^ 70 +
        2751531694023129312530160070437133699542991155125429092105228718803282) * 10 ^ 70 +
        5343855315993206756400972505587253498692748268065261777467924402606629) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 77 = 23 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (205 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_205 :
    recurrence2Scalar2Shift.coeff 205 =
      -(((379823550260820297929017044854312568111942197673089814397543175440 * 10 ^ 70 +
        4377040003169415928230324444132486320899004105716381331181947332294744) * 10 ^ 70 +
        1387069795570353226628618861062491243051060549390809132784556236761374) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 78 = 23 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (206 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_206 :
    recurrence2Scalar2Shift.coeff 206 =
      (((1248551128347889367327839234619306373642219684682474716091375506179 * 10 ^ 70 +
        6524126490229544613055587588275974869820289956811480057502014530883676) * 10 ^ 70 +
        0925886921182565782476761837529171055694022334570096850162367257206632) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 79 = 23 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (207 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_207 :
    recurrence2Scalar2Shift.coeff 207 =
      -(((2913517881148996143047450086657885194635729705243602807543473673870 * 10 ^ 70 +
        7961205933399602832639956118877493858527692118411514011107819675305963) * 10 ^ 70 +
        5715616466940308126910067948046218990691239291953691909878970843306659) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 80 = 23 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (208 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_208 :
    recurrence2Scalar2Shift.coeff 208 =
      (((5150627112407339328851537096977126371871123732957404526640985611205 * 10 ^ 70 +
        6523848209751620779736344907166980439698573723064965919305503329557870) * 10 ^ 70 +
        3181239053712762686416306669109645797899255378459201499620958655063211) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 81 = 23 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (209 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_209 :
    recurrence2Scalar2Shift.coeff 209 =
      -(((6028435969873723977574483056377229722968859746522187994319771932309 * 10 ^ 70 +
        7009120697969388971312263432155204098180018322334960654373092970880255) * 10 ^ 70 +
        4061413096915087365861230652526991170155421217553715723204121977633608) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (210 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_210 :
    recurrence2Scalar2Shift.coeff 210 =
      -(((492210451638030436958460427262454208885195424070470376384726779958 * 10 ^ 70 +
        9246586488565607984161973739099587020763712925458991917854203178342508) * 10 ^ 70 +
        5334753125109845717031256649586099583276071912497367510627209931410577) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (211 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_211 :
    recurrence2Scalar2Shift.coeff 211 =
      (((28408129587559168122442816448026169404354034336678439756782648314099 * 10 ^ 70 +
        5861846808291506325097002992152604312054682625261041036840713264215238) * 10 ^ 70 +
        8600940254522487028163428048119569250584553240004315228941048975602437) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 84 = 23 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (212 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_212 :
    recurrence2Scalar2Shift.coeff 212 =
      -(((104506111070129178980394764441012388701179385969983061163802792822915 * 10 ^ 70 +
        8776156242775043389423535865315188704539239677609819267241652225414725) * 10 ^ 70 +
        1603157156224675761156725245696019607607185703007575972905351575357082) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 85 = 23 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (213 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_213 :
    recurrence2Scalar2Shift.coeff 213 =
      (((272114745037601505249014246833005612045696459039230652070922735617284 * 10 ^ 70 +
        3786275621903952688416750507007541863419097094345146528231976984732605) * 10 ^ 70 +
        6234617756529107654568987524123951915038847161010320759533401130327811) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 86 = 23 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (214 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_214 :
    recurrence2Scalar2Shift.coeff 214 =
      -(((589120119181771273041249671579133711247075755311477326479300032293494 * 10 ^ 70 +
        7866038088195839486915578747458522030732074583206737243839654339990017) * 10 ^ 70 +
        3679957201305317819408680596576986243678014517006641581132110395117829) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (215 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_215 :
    recurrence2Scalar2Shift.coeff 215 =
      (((1112347588941508331119066683345941877007523774826167482552743629772067 * 10 ^ 70 +
        2850172616314001030446842476347723989788432988461091793579347688979856) * 10 ^ 70 +
        9855090970078883119241343903326255181107523394958275707127356784621377) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 88 = 23 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (216 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_216 :
    recurrence2Scalar2Shift.coeff 216 =
      -(((1857668712079931159689408022731416911401687685298103118967641727772040 * 10 ^ 70 +
        7807231035978835344317984019718286829712850417584191459128995143270535) * 10 ^ 70 +
        8870326777143205245302926021486783920402396892104973014898915598883591) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 89 = 23 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (217 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_217 :
    recurrence2Scalar2Shift.coeff 217 =
      (((2725023203616782515507890360798495157461860211612696727478068102939344 * 10 ^ 70 +
        3326902179777471315140329802836569942586471973762365102888006873344618) * 10 ^ 70 +
        7733638568092240734181153549748368426264207567531790860746293587839459) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 90 = 23 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (218 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_218 :
    recurrence2Scalar2Shift.coeff 218 =
      -(((3382619363583176941298880466905741344708006610378225149964927731023956 * 10 ^ 70 +
        1923629702760828167104734061120039123910956154298083517255911626635136) * 10 ^ 70 +
        3088043345082745005953904371205583259415177430741022132681239281006425) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 91 = 23 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (219 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_219 :
    recurrence2Scalar2Shift.coeff 219 =
      (((3117166408671960348942321353347700458491924696597281775030414387600789 * 10 ^ 70 +
        6404873988019085730987937400455244958441731575562544949410515142401368) * 10 ^ 70 +
        2717487924196178479444339451764523425578957394785374294059779105353813) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 92 = 23 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (220 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_220 :
    recurrence2Scalar2Shift.coeff 220 =
      -(((677389847695129354413315819741867097638101398215992367976306385514873 * 10 ^ 70 +
        2274641333774478469383330504308037781882257614016492267259072289935851) * 10 ^ 70 +
        7212398284331859162666172963855742992105325395149519405127370010843030) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 93 = 23 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (221 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_221 :
    recurrence2Scalar2Shift.coeff 221 =
      -(((5837107092950645108737320866790503974391237515701210534597324222979392 * 10 ^ 70 +
        5421386969227239980632905849151455400516429680726517871416685717626991) * 10 ^ 70 +
        6951629373691406516670920590844311117655127694939706345245360720915008) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 94 = 23 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (222 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_222 :
    recurrence2Scalar2Shift.coeff 222 =
      ((((1 * 10 ^ 70 +
        8968341517775886297860535252170783324584113489801423581871862954660410) * 10 ^ 70 +
        1872062699059015853023979317927609483588467969210301619783701286000320) * 10 ^ 70 +
        6137254820535176406744670380490453730857846647064699589918522638491138) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 95 = 23 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (223 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_223 :
    recurrence2Scalar2Shift.coeff 223 =
      -((((4 * 10 ^ 70 +
        1694540127248820068233441742452974421501902510550356503563986736911849) * 10 ^ 70 +
        2818778104687491870636983555181546779118725458947933984105857186210483) * 10 ^ 70 +
        8348953888629904987195392929586649579690980849612998787308701089261039) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 96 = 23 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (224 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_224 :
    recurrence2Scalar2Shift.coeff 224 =
      ((((7 * 10 ^ 70 +
        6968796122285844752819293686425512475628733810152379264877632735021731) * 10 ^ 70 +
        2516807154432069045714620854648289602902581657834429671606732754327435) * 10 ^ 70 +
        6441142983422739446034580759464301887889479803688338670100325111748836) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 97 = 23 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (225 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_225 :
    recurrence2Scalar2Shift.coeff 225 =
      -((((12 * 10 ^ 70 +
        6998973675250049230269839836440871654071019561980558269217659269314281) * 10 ^ 70 +
        4285109204879581947796763946421609547521964504023986410099600529930734) * 10 ^ 70 +
        5815004286747597063544816957921014883312804653572322759872624571385174) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 98 = 23 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (226 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_226 :
    recurrence2Scalar2Shift.coeff 226 =
      ((((19 * 10 ^ 70 +
        2350856552405785945607447261285974960008982003593687772516292840371395) * 10 ^ 70 +
        3160978692754845054251327709067186733088726366370273800209068895244947) * 10 ^ 70 +
        1196171097584883708502928175852725636329317158427783484818316344054129) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 99 = 23 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (227 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_227 :
    recurrence2Scalar2Shift.coeff 227 =
      -((((27 * 10 ^ 70 +
        1052121693730977138670722542042940318475214208522900393288825150373012) * 10 ^ 70 +
        3877619780865006154409909595420889545050857003793319667360100808713031) * 10 ^ 70 +
        0455352693348616115019725282312217694887571858708367425713501128004008) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 100 = 23 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (228 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_228 :
    recurrence2Scalar2Shift.coeff 228 =
      ((((35 * 10 ^ 70 +
        7949583095207759988391588847606735652844931927039605903065567455784196) * 10 ^ 70 +
        0027035398642781178720591528565452872237718248586014049664094580476234) * 10 ^ 70 +
        9446953746962029877381833390523461181390421879649752760709193445469343) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 101 = 23 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (229 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_229 :
    recurrence2Scalar2Shift.coeff 229 =
      -((((44 * 10 ^ 70 +
        4590589946701429721533166125959956766531361652348878652243241042744527) * 10 ^ 70 +
        9303002811302274307714151585479011181239143700225339252172312252346199) * 10 ^ 70 +
        7039380694643870870234494173871373256234976609257957713802765474426622) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 102 = 23 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (230 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_230 :
    recurrence2Scalar2Shift.coeff 230 =
      ((((51 * 10 ^ 70 +
        9835006141198050793365714000193505681042133352552604637345976626955558) * 10 ^ 70 +
        1231356282927619159443902245874813939335952430510518773647015061539080) * 10 ^ 70 +
        6792767813198202488672438658531177522489313340428092961645950967407822) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 102 = 22 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (231 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_231 :
    recurrence2Scalar2Shift.coeff 231 =
      -((((57 * 10 ^ 70 +
        1253532065081593217145559535413131275087719901193629943595470244674161) * 10 ^ 70 +
        0976196913428080206379186406576589018503590407095301688726307457611137) * 10 ^ 70 +
        9482656703857379736170473118983771407681372476844247974353319780569893) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 102 = 21 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (232 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_232 :
    recurrence2Scalar2Shift.coeff 232 =
      ((((58 * 10 ^ 70 +
        7159227628366394327324523634496561189253741307980312137612178913764995) * 10 ^ 70 +
        4316909553006048060189304054776530391525628977425270772831273703193620) * 10 ^ 70 +
        8707956103113244129267006406567776963745266917588825573606340774699176) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 102 = 20 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (233 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_233 :
    recurrence2Scalar2Shift.coeff 233 =
      -((((55 * 10 ^ 70 +
        8908297672419694350669448567548336578715385167409530993167550216915865) * 10 ^ 70 +
        6566754078367508783420804706628361098513962044628073786604111580471285) * 10 ^ 70 +
        2255531601441408682658185201695079699584751376016970818329917540948498) : ℚ) := by
  unfold recurrence2Scalar2Shift
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
    rw [show 102 = 19 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
