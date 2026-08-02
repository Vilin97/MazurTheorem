/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Shift coefficient convolution

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

theorem recurrence2Scalar3Shift_coeff_0 :
    recurrence2Scalar3Shift.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_1 :
    recurrence2Scalar3Shift.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_2 :
    recurrence2Scalar3Shift.coeff 2 =
      (-797631744 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_3 :
    recurrence2Scalar3Shift.coeff 3 =
      (-18326166224208 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_4 :
    recurrence2Scalar3Shift.coeff 4 =
      (-10767685210621016 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_5 :
    recurrence2Scalar3Shift.coeff 5 =
      (-376173652302335882888 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_6 :
    recurrence2Scalar3Shift.coeff 6 =
      (183462296446569560704840 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_7 :
    recurrence2Scalar3Shift.coeff 7 =
      (20903551130359936705145356 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_8 :
    recurrence2Scalar3Shift.coeff 8 =
      (-275710001951205598278094041620 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_9 :
    recurrence2Scalar3Shift.coeff 9 =
      (539718918511024088744545296504092 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_10 :
    recurrence2Scalar3Shift.coeff 10 =
      (-439930528857644265549746151151945956 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_11 :
    recurrence2Scalar3Shift.coeff 11 =
      (302705213405722386269727646356498141946 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_12 :
    recurrence2Scalar3Shift.coeff 12 =
      (-145893664366891715158480469165230912028766 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_13 :
    recurrence2Scalar3Shift.coeff 13 =
      (52081221993368123417696693942401786803010690 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_14 :
    recurrence2Scalar3Shift.coeff 14 =
      (-14005521883254213365665315343278797241776057424 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_15 :
    recurrence2Scalar3Shift.coeff 15 =
      (2887217712090811155753644900458101934853784011334 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_16 :
    recurrence2Scalar3Shift.coeff 16 =
      (-458887557993277136474515778578901296994043659577107 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_17 :
    recurrence2Scalar3Shift.coeff 17 =
      (55334995391059967187943873586235955607538598683232109 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_18 :
    recurrence2Scalar3Shift.coeff 18 =
      (-4808696463933121677067953012080663211548851508006262456 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_19 :
    recurrence2Scalar3Shift.coeff 19 =
      (247581233987272948542210226817213986941006609521351537032 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_20 :
    recurrence2Scalar3Shift.coeff 20 =
      (2734535283042297535330735510114329253881943600446505583842 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_21 :
    recurrence2Scalar3Shift.coeff 21 =
      (-2069732904741258038639375321732259149538163586266071560037449 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_22 :
    recurrence2Scalar3Shift.coeff 22 =
      (241709899059640628682938829098954285998441779506251841527770072 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_23 :
    recurrence2Scalar3Shift.coeff 23 =
      (-17976168746800090232037092926361664531025356474763992043451442183 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_24 :
    recurrence2Scalar3Shift.coeff 24 =
      (979521843046848525064972947501028217200891924958541576755533895062 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_25 :
    recurrence2Scalar3Shift.coeff 25 =
      (-40818179303325960246155217476695345861987185368762072361620263187852 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_26 :
    recurrence2Scalar3Shift.coeff 26 =
      (1323302393711113461327032691559684098942914355740695655390873935322060 : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_27 :
    recurrence2Scalar3Shift.coeff 27 =
      -((3 * 10 ^ 70 +
        3042335587475842278056993067648145572554875256698272632563384034443973) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_28 :
    recurrence2Scalar3Shift.coeff 28 =
      ((52 * 10 ^ 70 +
        3599273500279584409402817522125372799863697054418035951010367602434312) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_29 :
    recurrence2Scalar3Shift.coeff 29 =
      ((679 * 10 ^ 70 +
        0030919065994812622011566851871077131717652335866487876515633499969676) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_30 :
    recurrence2Scalar3Shift.coeff 30 =
      -((108995 * 10 ^ 70 +
        2453424430891402903221787212340237973452110016096723924113502122148744) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_31 :
    recurrence2Scalar3Shift.coeff 31 =
      ((5585384 * 10 ^ 70 +
        7789364196234138447717387860302145413322939803083362594400141562870880) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_32 :
    recurrence2Scalar3Shift.coeff 32 =
      -((202551666 * 10 ^ 70 +
        6874311661071379306729684032112747460879504327568845029404554460166750) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_33 :
    recurrence2Scalar3Shift.coeff 33 =
      ((8383378867 * 10 ^ 70 +
        5934684525006772237997340726081797078081407263732110198789914073248630) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_34 :
    recurrence2Scalar3Shift.coeff 34 =
      -((540896290912 * 10 ^ 70 +
        6427253782416219604110651984233271947136611233719300397915359078033110) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_35 :
    recurrence2Scalar3Shift.coeff 35 =
      ((35692996304414 * 10 ^ 70 +
        6290040070070038465668535620967822283021915276396489983011180298200089) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_36 :
    recurrence2Scalar3Shift.coeff 36 =
      -((1864850451595602 * 10 ^ 70 +
        1857913790094479279177938008709254068379830158696277357572797971860170) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_37 :
    recurrence2Scalar3Shift.coeff 37 =
      ((75263254899889203 * 10 ^ 70 +
        2616401457159632377201484217817177185538589315485450488947583173766431) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_38 :
    recurrence2Scalar3Shift.coeff 38 =
      -((2388695585478915605 * 10 ^ 70 +
        7194660861770137843188104933073448411663545401153634038561339731626853) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_39 :
    recurrence2Scalar3Shift.coeff 39 =
      ((60803245393253612856 * 10 ^ 70 +
        5681083213677446516548890264539170609231155038711898374301899472213822) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_40 :
    recurrence2Scalar3Shift.coeff 40 =
      -((1286521445884463692912 * 10 ^ 70 +
        8459247564833905759420660635567292242114135977090255636340545754178245) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_41 :
    recurrence2Scalar3Shift.coeff 41 =
      ((25571139280691572406961 * 10 ^ 70 +
        8691942405781941615045131954265069881764795784664862276472091685306303) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_42 :
    recurrence2Scalar3Shift.coeff 42 =
      -((632426078316121134239965 * 10 ^ 70 +
        0561023857251373076214837777824660821892443615776816189942284631633769) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_43 :
    recurrence2Scalar3Shift.coeff 43 =
      ((21735588396116787958236657 * 10 ^ 70 +
        2580895661104743521832393997584492247601318880038375323664638646203566) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_44 :
    recurrence2Scalar3Shift.coeff 44 =
      -((801823604511763193475925849 * 10 ^ 70 +
        1572128709155405511682525832331602574479166576862147568298082362751122) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_45 :
    recurrence2Scalar3Shift.coeff 45 =
      ((26420018773117934212003415569 * 10 ^ 70 +
        6350151781126118938778873972447784864103735913996824933262572856640785) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_46 :
    recurrence2Scalar3Shift.coeff 46 =
      -((743759291779792806279476326567 * 10 ^ 70 +
        3924324799815847243733611115811447870814683577099570897403253542903299) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_47 :
    recurrence2Scalar3Shift.coeff 47 =
      ((17850721993018814106240366880382 * 10 ^ 70 +
        3370076922088250709926385642792032298057901069789181721485040725420250) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_48 :
    recurrence2Scalar3Shift.coeff 48 =
      -((365635167427964893662908223444653 * 10 ^ 70 +
        1990932780713134408840632834089465568181332344005663959252164115077675) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_49 :
    recurrence2Scalar3Shift.coeff 49 =
      ((6324241717672233198847179330728010 * 10 ^ 70 +
        1984464104138326600572567995957375660511948702032626907984766900431395) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_50 :
    recurrence2Scalar3Shift.coeff 50 =
      -((88303337697543628920028155974169277 * 10 ^ 70 +
        4019284946066727938628207164662473707016693484769586755798183881801633) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_51 :
    recurrence2Scalar3Shift.coeff 51 =
      ((823503760175835833103011759368359876 * 10 ^ 70 +
        9245185623484382704271487542689746924483718026395239214018112235177615) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_52 :
    recurrence2Scalar3Shift.coeff 52 =
      ((2004286718022355814797770578015020739 * 10 ^ 70 +
        6425307600011572941117301894635599210141708482276778918178875038726890) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_53 :
    recurrence2Scalar3Shift.coeff 53 =
      -((342305531141979571370044161553546670138 * 10 ^ 70 +
        9533205715216278095969281041529253633750578620602236259737752295049696) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_54 :
    recurrence2Scalar3Shift.coeff 54 =
      ((10864691281978292228589276644269731165690 * 10 ^ 70 +
        2535711659083008228588647924600996561050390726099547291583033166121691) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_55 :
    recurrence2Scalar3Shift.coeff 55 =
      -((252833699877463715400782010856570823625377 * 10 ^ 70 +
        0101808422112847314612118154243716442748673650016648746268865732592317) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_56 :
    recurrence2Scalar3Shift.coeff 56 =
      ((4942618408308960291452293896354473902318229 * 10 ^ 70 +
        9715564362850074366154711325728839954345290789155891605186165238483119) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_57 :
    recurrence2Scalar3Shift.coeff 57 =
      -((84101524523098678001238665917825653989865441 * 10 ^ 70 +
        2744256202282595378248526348438370005991770439268625691057921640683863) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_58 :
    recurrence2Scalar3Shift.coeff 58 =
      ((1249740674822938333633312895827557361472836203 * 10 ^ 70 +
        9797312634760257542330539940307146574919081344815751868304944432808115) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_59 :
    recurrence2Scalar3Shift.coeff 59 =
      -((15878870938238133363645397018846682100386598708 * 10 ^ 70 +
        9708055420592358932047827603513537379140659640197276106142797052422227) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_60 :
    recurrence2Scalar3Shift.coeff 60 =
      ((160579284536683014780651905746714659433395233830 * 10 ^ 70 +
        8002841665698386985843167337209418583629635967263600516393072762372715) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_61 :
    recurrence2Scalar3Shift.coeff 61 =
      -((937376154163998859242363880388460448172625892832 * 10 ^ 70 +
        2807696104193236286026239575201445790345560911509730131641132798408840) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_62 :
    recurrence2Scalar3Shift.coeff 62 =
      -((8571967366436783283083711099270833347256897504583 * 10 ^ 70 +
        4638065501749618272162786131781134988340655043110074010086134693196326) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_63 :
    recurrence2Scalar3Shift.coeff 63 =
      ((420566606921190524269451466893399591912399338179167 * 10 ^ 70 +
        2478387003807078958367159230710162632908522196698657863974844558553974) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_64 :
    recurrence2Scalar3Shift.coeff 64 =
      -((9407644772013945771244691376590761763730389580822006 * 10 ^ 70 +
        6065096753036826119489798140891006840908023318454074946697836802259151) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_65 :
    recurrence2Scalar3Shift.coeff 65 =
      ((165138234206905874331254674778824644136281682190321095 * 10 ^ 70 +
        7420555885625775387855601641743120632439125692759665388655584791328329) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_66 :
    recurrence2Scalar3Shift.coeff 66 =
      -((2523454938122732161291344814796216210345528294243875088 * 10 ^ 70 +
        4535247165961758124249097356232288736916605502639711787818389883544441) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_67 :
    recurrence2Scalar3Shift.coeff 67 =
      ((34913745614174053766965902547615383931573152609048440439 * 10 ^ 70 +
        0330688553146205589707424411428618979598404357713065662179485537024242) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_68 :
    recurrence2Scalar3Shift.coeff 68 =
      -((445936762453058075686855929968559931554589098734059495805 * 10 ^ 70 +
        1131125257958413913555610381190823121485453607382011582126665672046611) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_69 :
    recurrence2Scalar3Shift.coeff 69 =
      ((5317060418586390973601773499882866766340909514336046879077 * 10 ^ 70 +
        8523468620645828616688164729634777276928747484969867421954957932096433) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_70 :
    recurrence2Scalar3Shift.coeff 70 =
      -((59607704660602254643234635459126867821929501765928597958317 * 10 ^ 70 +
        6374907936053863108553518586535906049126740702113094899873240224517412) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_71 :
    recurrence2Scalar3Shift.coeff 71 =
      ((631457262443573697161663489885093804486606148308912163541302 * 10 ^ 70 +
        0038596035231376156011255223577369496686586345539243414795249807488843) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_72 :
    recurrence2Scalar3Shift.coeff 72 =
      -((6344908916285235703509304857603218698413057693790268933738518 * 10 ^ 70 +
        0474314616493383492589771438568546092337873755049181861191360733740021) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_73 :
    recurrence2Scalar3Shift.coeff 73 =
      ((60648197912435404833261178889988516540546509299851647040959476 * 10 ^ 70 +
        0719207863487093111235900865190436956636345143555462060673175798394806) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_74 :
    recurrence2Scalar3Shift.coeff 74 =
      -((552756254390675685254330593909056140397340492596576289735065794 * 10 ^ 70 +
        4064834681125392669258621698914231226824695168567718998051147413858909) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_75 :
    recurrence2Scalar3Shift.coeff 75 =
      ((4812636230110894171266004871258331583256962134208292535034513899 * 10 ^ 70 +
        8585747466037356581124747338354140201081999770723940747934939997626093) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_76 :
    recurrence2Scalar3Shift.coeff 76 =
      -((40088200493227718657420934187095633711189931631199470939097107685 * 10 ^ 70 +
        7912230567921913897540691569862052018573415686847307057694619726550542) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_77 :
    recurrence2Scalar3Shift.coeff 77 =
      ((319862327750816022375915872518672993436956743011034107353478319912 * 10 ^ 70 +
        9410751913301485221092301350869337034536048755211471963101706318967656) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_78 :
    recurrence2Scalar3Shift.coeff 78 =
      -((2447175889588990389847327736901763033872931820314034885087717082036 * 10 ^ 70 +
        7424018659279317993428861311262843027696373507745102508051621188320300) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_79 :
    recurrence2Scalar3Shift.coeff 79 =
      ((17968326870005559671611342963000327327607083244597022568920330776553 * 10 ^ 70 +
        9179561645018022676962372909143085475604826413207076909886990099737775) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_80 :
    recurrence2Scalar3Shift.coeff 80 =
      -((126716840133292507519062792474126598242677063832490552712974833053169 * 10 ^ 70 +
        8452480434698601488393975360383637523017859899132768422746883508967672) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_81 :
    recurrence2Scalar3Shift.coeff 81 =
      ((858917471803755404968830107610421926526934190327384975056046129250412 * 10 ^ 70 +
        7560899870848591437984448472118471880302467066874499334213992015684063) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_82 :
    recurrence2Scalar3Shift.coeff 82 =
      -((5599120448075681744806241251780717528944316540901106774598264462718634 * 10 ^ 70 +
        7617671947883306162941858017159151814258603862074071736404404386623038) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_83 :
    recurrence2Scalar3Shift.coeff 83 =
      (((3 * 10 ^ 70 +
        5119111984499369175520951990191245593359089585013118156264752839273425) * 10 ^ 70 +
        1853245371571893485772444854581498852680569444341941275762315869922689) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_84 :
    recurrence2Scalar3Shift.coeff 84 =
      -(((21 * 10 ^ 70 +
        2013154975942035444915767923057467198769253117772492284217554535942374) * 10 ^ 70 +
        0489151508199813022848853970018730805235906427463992991589590953731712) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_85 :
    recurrence2Scalar3Shift.coeff 85 =
      (((123 * 10 ^ 70 +
        2132537103125159515442533546143174785047609705050502082650550864352901) * 10 ^ 70 +
        7227622829650378175189440642969817267294860066183935816017605730564618) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_86 :
    recurrence2Scalar3Shift.coeff 86 =
      -(((689 * 10 ^ 70 +
        3834905953447785589975894482817784470727041500707218325357876368923346) * 10 ^ 70 +
        4842716193741428075120981251757011381365705338785167277106049611113811) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_87 :
    recurrence2Scalar3Shift.coeff 87 =
      (((3713 * 10 ^ 70 +
        4585306279723199071033179678319167544510179500621194206230754003728615) * 10 ^ 70 +
        3468914688524636540499910519801071539535418457581799542722085423946002) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_88 :
    recurrence2Scalar3Shift.coeff 88 =
      -(((19257 * 10 ^ 70 +
        3880340066356196312621049989514654079910149960451772627892124478476101) * 10 ^ 70 +
        6613511199588976092765232876375048793040920932906988637225660280395068) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_89 :
    recurrence2Scalar3Shift.coeff 89 =
      (((96132 * 10 ^ 70 +
        9986755742638534798293044483041875718798544105648117127350859427431582) * 10 ^ 70 +
        1967407579165753659943741427972011685314653225505132484365083149784834) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_90 :
    recurrence2Scalar3Shift.coeff 90 =
      -(((461831 * 10 ^ 70 +
        2398442934909898064988555013289139126373254124825860414708978212787945) * 10 ^ 70 +
        0939063994266364026589011046471835886815263904628167152668381962914545) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_91 :
    recurrence2Scalar3Shift.coeff 91 =
      (((2133844 * 10 ^ 70 +
        2419589655030458662198397002654878680589952994731227632771607116260544) * 10 ^ 70 +
        3343044269499842802010893772311909096371059792137974301333781377703446) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_92 :
    recurrence2Scalar3Shift.coeff 92 =
      -(((9471542 * 10 ^ 70 +
        2298530199034805505321520248025950478869768536739024682429662930568889) * 10 ^ 70 +
        0388779680216968192168462663680947193042715803359942457646332998237144) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_93 :
    recurrence2Scalar3Shift.coeff 93 =
      (((40317585 * 10 ^ 70 +
        7351244447016729600850445447686538681362211670949809431579779356115290) * 10 ^ 70 +
        6139285131542313674756110366422781120619952880917217973594983008755309) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_94 :
    recurrence2Scalar3Shift.coeff 94 =
      -(((164191968 * 10 ^ 70 +
        7891945375670426440676116795180422588539029696198256346109091347674628) * 10 ^ 70 +
        3143460673271033182323579817165582987260331909888910838134589980555736) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_95 :
    recurrence2Scalar3Shift.coeff 95 =
      (((637882872 * 10 ^ 70 +
        6075911467697670847805364972030915313962454630117271838447197256692066) * 10 ^ 70 +
        8443037908536280023272685722483670106811245740573409675268026505884006) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_96 :
    recurrence2Scalar3Shift.coeff 96 =
      -(((2356196212 * 10 ^ 70 +
        2891370010898611281547131529409780038129794427990953299942498423212011) * 10 ^ 70 +
        6521821681573573251184441088674965632593324471127754099418273271259653) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_97 :
    recurrence2Scalar3Shift.coeff 97 =
      (((8239723103 * 10 ^ 70 +
        6869783640920880810228528876326575686992133578630249597581635989338573) * 10 ^ 70 +
        1852302904736221188185090455802720569338822211806618623830773879929471) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_98 :
    recurrence2Scalar3Shift.coeff 98 =
      -(((27086684357 * 10 ^ 70 +
        1105240229467094474298853453570190225973762445475427115919463524711814) * 10 ^ 70 +
        3460095064645967643388457609539406844031918955384565574403133973125175) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_99 :
    recurrence2Scalar3Shift.coeff 99 =
      (((82428625716 * 10 ^ 70 +
        6303707269799205958852473383197206067310231560626823621070132944109099) * 10 ^ 70 +
        6090931096591799617372994729130039350455283714907721159428175434855520) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_100 :
    recurrence2Scalar3Shift.coeff 100 =
      -(((223576322741 * 10 ^ 70 +
        8180352280442480985692832357484407389904931558686536893848231114069424) * 10 ^ 70 +
        8262481626028154907415473088680015239766339591435581759769981280119291) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_101 :
    recurrence2Scalar3Shift.coeff 101 =
      (((484137788502 * 10 ^ 70 +
        7230504032631525227832763321412059499609327443654270277833980299861635) * 10 ^ 70 +
        5662911025422326780330983616694254347130608593268066013769979786217873) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_102 :
    recurrence2Scalar3Shift.coeff 102 =
      -(((458301177189 * 10 ^ 70 +
        8487812244023991195747575309092028845925151165456279383025811920821433) * 10 ^ 70 +
        0283710828711382459807209634540499313468502757584969357087978357886862) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_103 :
    recurrence2Scalar3Shift.coeff 103 =
      -(((2888004708485 * 10 ^ 70 +
        6797170869994494559918052958032988181148449735736590103910622949803340) * 10 ^ 70 +
        3504341828334623455060507167071823879049112262512886631275997842077806) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_104 :
    recurrence2Scalar3Shift.coeff 104 =
      (((23381815546939 * 10 ^ 70 +
        4646804003351886931628481737465611340109460426947520711008151821519952) * 10 ^ 70 +
        0089278579298949936536459659921591308439130326113523708932202188372892) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_105 :
    recurrence2Scalar3Shift.coeff 105 =
      -(((107982946578227 * 10 ^ 70 +
        4498164047776074652692103101634111541700711626270080546773921985902148) * 10 ^ 70 +
        9677156726389267372806461401979149538796696586601647377092731121258003) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_106 :
    recurrence2Scalar3Shift.coeff 106 =
      (((379008923778697 * 10 ^ 70 +
        7156856547668810804317802526143839027449458737508749644913329638290465) * 10 ^ 70 +
        3613896640679802385852440274145834944874891994004089963080172358592708) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_107 :
    recurrence2Scalar3Shift.coeff 107 =
      -(((1110318817721287 * 10 ^ 70 +
        7398185672799547851628413359378183090298899193889961728009652646719283) * 10 ^ 70 +
        5484492161936696623841710594867618472031800741327784965403387424508616) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_108 :
    recurrence2Scalar3Shift.coeff 108 =
      (((3274672713500514 * 10 ^ 70 +
        0997611440333850159522516161982324083652018623709449036804872771335808) * 10 ^ 70 +
        9393179931641213045775893869781002118458113839805472132647726299900110) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_109 :
    recurrence2Scalar3Shift.coeff 109 =
      -(((13360666687878781 * 10 ^ 70 +
        3818268955720579213795244917025814555940515478372029100462789737470706) * 10 ^ 70 +
        6551098449417017471432468036331570243276555017326370155345460545463980) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_110 :
    recurrence2Scalar3Shift.coeff 110 =
      (((71132388227994295 * 10 ^ 70 +
        3423539357201726004722275562205033187129829303905952377106355325207285) * 10 ^ 70 +
        2454948897677562415175399344081406561964529679832512557938994599014302) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_111 :
    recurrence2Scalar3Shift.coeff 111 =
      -(((350275115961722328 * 10 ^ 70 +
        8816317624955723064234189343699449383477986607985998450588992530460690) * 10 ^ 70 +
        8877429896570895924594503125166764998749280345526441265970213169418425) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_112 :
    recurrence2Scalar3Shift.coeff 112 =
      (((1285452047362690939 * 10 ^ 70 +
        1232607754246915265590887498442654451910650587728309627481250013612987) * 10 ^ 70 +
        9297188496130038819795482175280350162263460927458037645986152013035554) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_113 :
    recurrence2Scalar3Shift.coeff 113 =
      -(((2421173519601780470 * 10 ^ 70 +
        0656854176736695410462834366866356514829633763720774179333838761576667) * 10 ^ 70 +
        8803767573838309243571806854715186983399542659449149295066661144987505) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_114 :
    recurrence2Scalar3Shift.coeff 114 =
      -(((7399058102532525592 * 10 ^ 70 +
        4816118979008191507706203165628448137998363784483654648405992705337423) * 10 ^ 70 +
        8339603919858231422397147312935155258086183438574864189563646724470245) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_115 :
    recurrence2Scalar3Shift.coeff 115 =
      (((89141554472021363731 * 10 ^ 70 +
        3651356432620589256395705921239784270464945619933548581236864960082763) * 10 ^ 70 +
        6723149116362679501560196400600136851585632751193683087925017201172797) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_116 :
    recurrence2Scalar3Shift.coeff 116 =
      -(((409851406799415510217 * 10 ^ 70 +
        6808119634579304749824152681458518143543584367696703424075833288009193) * 10 ^ 70 +
        1266823188855106709212156811937525449248245280334479999267502114657532) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_117 :
    recurrence2Scalar3Shift.coeff 117 =
      (((888465473205875351715 * 10 ^ 70 +
        2447667429536525451965215182177987602339180826706805785720121851408951) * 10 ^ 70 +
        3420358855257591677748453300837333835264304697924235852161856661505246) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_118 :
    recurrence2Scalar3Shift.coeff 118 =
      (((1734851009385974209249 * 10 ^ 70 +
        7052312245603209723479904529563197871399535424504806308914245229418621) * 10 ^ 70 +
        2165532685722829892278353851146907767690520252416471794665326410510935) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_119 :
    recurrence2Scalar3Shift.coeff 119 =
      -(((24518427448860836015061 * 10 ^ 70 +
        3227572194625605689121528364786541023449874829496844472585536551292864) * 10 ^ 70 +
        3311694489841328696283978979575974106916422523786832233205754475803448) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_120 :
    recurrence2Scalar3Shift.coeff 120 =
      (((113162487000691133339050 * 10 ^ 70 +
        9572303611612237750590934972590794513636410265793189603094087585180266) * 10 ^ 70 +
        4100478355558008518479995285291556488469705068603673768181281028741790) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_121 :
    recurrence2Scalar3Shift.coeff 121 =
      -(((278863475197050886242135 * 10 ^ 70 +
        9785413247107766246940413792653387604138052425913508429037786458421444) * 10 ^ 70 +
        2113716467647748956982785551443360815760499100486137513299006585438403) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_122 :
    recurrence2Scalar3Shift.coeff 122 =
      -(((26959239749488100871187 * 10 ^ 70 +
        8781826944301241065006051837856113645747411517313612021385807375349094) * 10 ^ 70 +
        4985157417260208581334348336586681367999189225910344631639372617569506) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_123 :
    recurrence2Scalar3Shift.coeff 123 =
      (((4078503176876536243295715 * 10 ^ 70 +
        8978327931749889585149667728233166839174574964734630636253820361812286) * 10 ^ 70 +
        3708462620180897401725652228437452683984192621068633295789197649686125) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_124 :
    recurrence2Scalar3Shift.coeff 124 =
      -(((24107126655122938771088340 * 10 ^ 70 +
        2698194397569018115340696269741944967002930933012992653584455825308341) * 10 ^ 70 +
        2407764979828228813432015407873353474681762815286696355737363501770847) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_125 :
    recurrence2Scalar3Shift.coeff 125 =
      (((89284224465924174265033197 * 10 ^ 70 +
        0468545155100643438846200505448485791257207193008765466981234006953959) * 10 ^ 70 +
        9721868911411553972583157177530783798858651587659034139681455316811798) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_126 :
    recurrence2Scalar3Shift.coeff 126 =
      -(((191533949288614575656705115 * 10 ^ 70 +
        7285892388953965385067352285144645210413533268614841107366602373356802) * 10 ^ 70 +
        7219751826719787611394644387096851435341771613682992937368309137904388) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_127 :
    recurrence2Scalar3Shift.coeff 127 =
      -(((199157608193060565927700525 * 10 ^ 70 +
        5586552747191323288190404803223396624308484452731342169211511429505906) * 10 ^ 70 +
        1812942895468593248496593138975601796946377666196436864166167915609419) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_128 :
    recurrence2Scalar3Shift.coeff 128 =
      (((4014519843033995839622128201 * 10 ^ 70 +
        7292142223655462326410570884233824835691305134067480179848350829744745) * 10 ^ 70 +
        7852918353563836444482019786600423842221893070408206321383638525636965) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_129 :
    recurrence2Scalar3Shift.coeff 129 =
      -(((19080216297531214089177449754 * 10 ^ 70 +
        2918463285160405105132065376294595882592090030721434052300976622666720) * 10 ^ 70 +
        1968136586729924438196867955069657875296290351538747541050742118744553) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_130 :
    recurrence2Scalar3Shift.coeff 130 =
      (((46505748487965819545724892739 * 10 ^ 70 +
        5941100955872429603406839162911400024745247929236535960263937724947956) * 10 ^ 70 +
        4853260180418210355986151161624191650969261929563788374443374165317185) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_131 :
    recurrence2Scalar3Shift.coeff 131 =
      -(((20508590344527634705643222341 * 10 ^ 70 +
        0151684245331561601724654710036734865949382933442091821316954165383645) * 10 ^ 70 +
        4360365604901243331307350971880231403482498505514212875918834265932987) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_132 :
    recurrence2Scalar3Shift.coeff 132 =
      -(((218033218094702525213976942332 * 10 ^ 70 +
        9516365930593377095857207912100560916346754665574006825094082643972173) * 10 ^ 70 +
        0284060109778905040974877283529124012740180021268977296313139652007147) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_133 :
    recurrence2Scalar3Shift.coeff 133 =
      (((446745735564622502932351238029 * 10 ^ 70 +
        5791299772960967697167869177303380522775849537860378234708026603224812) * 10 ^ 70 +
        2249412115475841641849853442160510400160309004614196055192446910669399) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_134 :
    recurrence2Scalar3Shift.coeff 134 =
      -(((626095071673924068340226347913 * 10 ^ 70 +
        4018631090192208611521654834387401236557561859202333549478499985678757) * 10 ^ 70 +
        6372451880295215941374857872149473607780307559639186879894040327827681) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_135 :
    recurrence2Scalar3Shift.coeff 135 =
      (((20198222753533864218694564704694 * 10 ^ 70 +
        2520537577773918365608642212483545755431911338997543450800435142147826) * 10 ^ 70 +
        6247869147137738977528280020467741600748075749615705185540789007422917) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_136 :
    recurrence2Scalar3Shift.coeff 136 =
      -(((174265098350949223092884504523681 * 10 ^ 70 +
        8004501813341987935887366840641194195415996439292339239007075680269208) * 10 ^ 70 +
        9011364251574240525422932832231898174701915498438850790070622335340652) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_137 :
    recurrence2Scalar3Shift.coeff 137 =
      (((611253231976638158740493090799993 * 10 ^ 70 +
        8521362657262345471222738827228767787621169222862552351535496435246931) * 10 ^ 70 +
        3874305935836491511543559742322155786305666552170674610211438906875750) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_138 :
    recurrence2Scalar3Shift.coeff 138 =
      (((190532945481687167607317133326012 * 10 ^ 70 +
        9330839268658256385926222737047513469393235059088728266593718411841071) * 10 ^ 70 +
        2579950928206919878101904956638238018723645981852879721219760635166080) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_139 :
    recurrence2Scalar3Shift.coeff 139 =
      -(((11506222479456535561582998610331201 * 10 ^ 70 +
        4483102354523264449686347486295982139331170485464374402162756860671436) * 10 ^ 70 +
        1317277170992632601876680369513740008252516455071634478884700872610556) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_140 :
    recurrence2Scalar3Shift.coeff 140 =
      (((47778806095603855982594538852524747 * 10 ^ 70 +
        4096719068857801745312385636343916307178036770554686172795517306539890) * 10 ^ 70 +
        1028804957223394906880696817377125308421926262646371145699642809348669) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_141 :
    recurrence2Scalar3Shift.coeff 141 =
      -(((27985331580423275569712719443559071 * 10 ^ 70 +
        8779685365264932633224361939165162892401402564251360789119656653095201) * 10 ^ 70 +
        7125257969685168544661720013805710827701196257084430153728734630975380) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_142 :
    recurrence2Scalar3Shift.coeff 142 =
      -(((555145018005615438565864951190904221 * 10 ^ 70 +
        4916149809008995585687709916507729265000805263021249613552662230072130) * 10 ^ 70 +
        2919759930049848314208454732034928385296321299443175097498791233947254) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_143 :
    recurrence2Scalar3Shift.coeff 143 =
      (((2388261164049806076981601214774764563 * 10 ^ 70 +
        0682057101914123460308211013580694375842235605470220082264723696431968) * 10 ^ 70 +
        3225650666505138532021942296526259774675645474426683332971118849526808) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_144 :
    recurrence2Scalar3Shift.coeff 144 =
      -(((811136999147433044407733166134445968 * 10 ^ 70 +
        6882441798773437807731489110344181802031163037761689765806167892727855) * 10 ^ 70 +
        9390000838970921312075569179641829414129998476539441734955356459143136) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_145 :
    recurrence2Scalar3Shift.coeff 145 =
      -(((30358419324974193433899018030329660737 * 10 ^ 70 +
        2618646738059861602059859562086773964035258410747184567282763703459666) * 10 ^ 70 +
        2625877360952434249631664237054958070197584151829673391164028366193854) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

theorem recurrence2Scalar3Shift_coeff_146 :
    recurrence2Scalar3Shift.coeff 146 =
      (((120895286137252817861245196144660972902 * 10 ^ 70 +
        0810666638919164618630254710442594758793969156028407895745816291198461) * 10 ^ 70 +
        2617460273535628697931944855986195721834682030176691105458833987439722) : ℚ) := by
  unfold recurrence2Scalar3Shift
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

private theorem recurrence2Scalar3Shift_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_147 :
    recurrence2Scalar3Shift.coeff 147 =
      -(((25216744545897230935699250510019868752 * 10 ^ 70 +
        5161050307231087910835496414244413958386091150601037493688352354709047) * 10 ^ 70 +
        2305627499731395606783641203985368489250909957597610460046906310509806) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (148 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_148 :
    recurrence2Scalar3Shift.coeff 148 =
      -(((1523288782462150070645616809419026984719 * 10 ^ 70 +
        8714836468217969439622219012423255764304793108632689131389654218401606) * 10 ^ 70 +
        8085089269016561845588497055615948961197937258720881796121713693386062) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (149 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_149 :
    recurrence2Scalar3Shift.coeff 149 =
      (((5845448704233918794559035111475505156522 * 10 ^ 70 +
        7991324308501889074975169716195118258637015004691126890149529486811766) * 10 ^ 70 +
        3152719835315728053181684030628465523613795449427222210909237093086482) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (150 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_150 :
    recurrence2Scalar3Shift.coeff 150 =
      -(((1580548619261400762019469031028119950007 * 10 ^ 70 +
        8485130951987525167377016652351248583104129024586272465182138839696344) * 10 ^ 70 +
        9038013692380088570485224899791744696039570740433337278514899808294267) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (151 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_151 :
    recurrence2Scalar3Shift.coeff 151 =
      -(((67406900665343772442442811059768491463173 * 10 ^ 70 +
        5731093489196243733109682041683468597955793903759278056427165511373679) * 10 ^ 70 +
        6555048631962683304232951218504797080901363056948934066738667945190647) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (152 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_152 :
    recurrence2Scalar3Shift.coeff 152 =
      (((257232952729894802702271508136605286620943 * 10 ^ 70 +
        3235484001044638952921537127217322581174785638630587958053834245327149) * 10 ^ 70 +
        7323635908769346362111539037468040143308400461955634795343497997313976) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (153 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_153 :
    recurrence2Scalar3Shift.coeff 153 =
      -(((81468665989986180789924249248377597031716 * 10 ^ 70 +
        2799768159874043811953837521923455826041668527564969344742161636063707) * 10 ^ 70 +
        6401210147125554272511196035712196032975840496412314253875995878574389) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (154 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_154 :
    recurrence2Scalar3Shift.coeff 154 =
      -(((2835026430081224321770572766005771221995117 * 10 ^ 70 +
        7094006481550377611906127449648518547848747936916154613874216231036299) * 10 ^ 70 +
        0115358906609776109022630630506217797056885549942178988947155288634861) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (155 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_155 :
    recurrence2Scalar3Shift.coeff 155 =
      (((11037303070979080906845240123516539586406024 * 10 ^ 70 +
        7114702803647535492544296846573833545072715558265095196925119539829767) * 10 ^ 70 +
        9031969067847684140005355204236379558399449042296931633457008325880960) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (156 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_156 :
    recurrence2Scalar3Shift.coeff 156 =
      -(((5501809289725788901402351403341080152109638 * 10 ^ 70 +
        6475730537204749330581551493595442418749471907004445601184486527012287) * 10 ^ 70 +
        4354220887822479273100460418282225317186361243403219094495664836584201) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (157 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_157 :
    recurrence2Scalar3Shift.coeff 157 =
      -(((111216042764848306251494588269297198495512035 * 10 ^ 70 +
        4756185320479037714321418044490016127203981810753470981151736457334417) * 10 ^ 70 +
        7004201785041072124111625679467201491472841911230786229464127658662396) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (158 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_158 :
    recurrence2Scalar3Shift.coeff 158 =
      (((469706903038386060014111285545528789069839490 * 10 ^ 70 +
        3373250401181582370904267236366199861810849874028790894647168294659174) * 10 ^ 70 +
        3713865163618447121974224948814823199716831319408742118906446285698240) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (159 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_159 :
    recurrence2Scalar3Shift.coeff 159 =
      -(((435863946780772822697541453296721087005319778 * 10 ^ 70 +
        6837793689141999683587709053565233259671281592372943982055127640478848) * 10 ^ 70 +
        0870745965112288401190804289871867774007884167408862256296826847933018) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (160 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_160 :
    recurrence2Scalar3Shift.coeff 160 =
      -(((3753665361542200877432072687325691884871835834 * 10 ^ 70 +
        9633275277520679915237431481775325844024955304882846468337146734384430) * 10 ^ 70 +
        8273720267245717234980710970889374209367551997414611072251372009854227) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (161 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_161 :
    recurrence2Scalar3Shift.coeff 161 =
      (((18884001503145949894152753339905778337792255948 * 10 ^ 70 +
        1563755453696311757265186589732057612918510443538097375293318575908971) * 10 ^ 70 +
        5609228984272285313313297225485906996309870201182345628704695677233300) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (162 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_162 :
    recurrence2Scalar3Shift.coeff 162 =
      -(((29263874371678269989523141818626184191602663596 * 10 ^ 70 +
        9761509737605323189296151501092569456662347972405333981012840833515180) * 10 ^ 70 +
        2291618513893013258763855069848681521912069636275770312636682649632580) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (163 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_163 :
    recurrence2Scalar3Shift.coeff 163 =
      -(((94628295077454830002402421557398044291585547047 * 10 ^ 70 +
        7738875885647185258973475126294835370521275035469593711219835965574468) * 10 ^ 70 +
        3578269855448502697050561481857766757238341029971304534942772765383998) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (164 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_164 :
    recurrence2Scalar3Shift.coeff 164 =
      (((667555444138041952920227930804366208259480391479 * 10 ^ 70 +
        0461369448923307457787473337847682565232924087557450584815633727095908) * 10 ^ 70 +
        0659434666460671234938417895961080364503447890319659998758113749678773) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (165 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_165 :
    recurrence2Scalar3Shift.coeff 165 =
      -(((1534100728704687048577128870792623412285660685729 * 10 ^ 70 +
        3571004664345008131212153661468834082063615624676257108836586719357985) * 10 ^ 70 +
        1042002937887938941760993702376438939150277335796095499586298879192785) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (166 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_166 :
    recurrence2Scalar3Shift.coeff 166 =
      -(((1019163377748713692323801689410221105747799086347 * 10 ^ 70 +
        2470226184918275207792471993222450109959685586529999345859474649342375) * 10 ^ 70 +
        4399251623102571350799650012758413148714257226095408052478430038018200) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (167 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_167 :
    recurrence2Scalar3Shift.coeff 167 =
      (((19198142209700721453202714787710054988361840200748 * 10 ^ 70 +
        4782786442432929497198878994918084072186055472000623800007987693539874) * 10 ^ 70 +
        7675723922045585223808495998311987094224720168058110158017741679898111) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (168 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_168 :
    recurrence2Scalar3Shift.coeff 168 =
      -(((62509562219346061999946335553332450872564828592735 * 10 ^ 70 +
        1310542975392122557909807391813969717131978676335732338098416256975648) * 10 ^ 70 +
        2098540903868206692613685437205522071332531519858950584521704826948323) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (169 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_169 :
    recurrence2Scalar3Shift.coeff 169 =
      (((51258227449741461269345056800482866055362498364027 * 10 ^ 70 +
        9756908339063560387627929101773883000481981107047097084014758216662484) * 10 ^ 70 +
        1189663774330818373104883894447463555976953318462384484930698564451755) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (170 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_170 :
    recurrence2Scalar3Shift.coeff 170 =
      (((396868486930722952016739359318772818029339992006424 * 10 ^ 70 +
        3767313499249938486150156811349075491942771871853856214125436655927327) * 10 ^ 70 +
        1856399822448679625846804954607371730940042634628794137386433897322489) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (171 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_171 :
    recurrence2Scalar3Shift.coeff 171 =
      -(((1972380266312303808040372254996075872057649975288913 * 10 ^ 70 +
        8279512727623031775812043019703243984087626318816008762159581493242095) * 10 ^ 70 +
        2881184469292085763012915134504412233575727391147766951333071809965448) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (172 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_172 :
    recurrence2Scalar3Shift.coeff 172 =
      (((3823713938391227624828659223104384706987246525294173 * 10 ^ 70 +
        2345631493101963856564144002513184347620468719420608513374847294909432) * 10 ^ 70 +
        7450654530414869734920106862526178978951102874574204812256796057532242) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (173 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_173 :
    recurrence2Scalar3Shift.coeff 173 =
      (((3239554824422180330814584093541087180693180147759368 * 10 ^ 70 +
        0723306323158250300868784001924426645086193076247720214190414100258706) * 10 ^ 70 +
        9242080433852004292497986837258087837793961361314992227222216863887308) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (174 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_174 :
    recurrence2Scalar3Shift.coeff 174 =
      -(((45909923651969754591361804072824035614930661998783657 * 10 ^ 70 +
        4559494488891595777202312985004575941509437925594218990717352891692167) * 10 ^ 70 +
        6068525264300682372211060630034254027642010209872054762524249826887321) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (175 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_175 :
    recurrence2Scalar3Shift.coeff 175 =
      (((145405735663449747561410513627340145936968553481957609 * 10 ^ 70 +
        9856946805635743651131990939705351144558092258951553526622469639287183) * 10 ^ 70 +
        2664792800786697295929539963378203495708944065048879320726158434108878) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (176 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_176 :
    recurrence2Scalar3Shift.coeff 176 =
      -(((158726805548970846304583953876377062230735366816289685 * 10 ^ 70 +
        1654679587573347802353302302879107079587680919093719494517175645950700) * 10 ^ 70 +
        9887527904546268851726714798539826445913155739258837150096439064868450) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (177 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_177 :
    recurrence2Scalar3Shift.coeff 177 =
      -(((618148691879452430885130700434081241798720674004037918 * 10 ^ 70 +
        5490889947059363719834917490365311008024298939501919992835417759741218) * 10 ^ 70 +
        2246582924308845689259614030681123696947491546160533471937598709571792) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (178 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_178 :
    recurrence2Scalar3Shift.coeff 178 =
      (((3654722310154998627780558037856579391812275172431806874 * 10 ^ 70 +
        4015317207121611043147136718973716745637151122120759609902680647783817) * 10 ^ 70 +
        9375470739222101517155409072662631012201833926256938844248969072616283) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (179 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_179 :
    recurrence2Scalar3Shift.coeff 179 =
      -(((8870827724221676230746220724002389467148180252886259493 * 10 ^ 70 +
        9420160660235692567994262936548842815542975792517594394771245898925495) * 10 ^ 70 +
        9779098771393554148969791941534771170389350655669742814427024928249895) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (180 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_180 :
    recurrence2Scalar3Shift.coeff 180 =
      (((4594842227086738595751684934659831327881519748065526687 * 10 ^ 70 +
        5590461841658212555576395867755798192240255014051499319164965488733962) * 10 ^ 70 +
        9925283906743670701504123628159114257813959850699441086807398499099867) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (181 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_181 :
    recurrence2Scalar3Shift.coeff 181 =
      (((52068144627096211807581271952658750268713950814159434442 * 10 ^ 70 +
        6277505697154912504173046137190637665366527382443183718069991588643994) * 10 ^ 70 +
        9965516006291887463487872816650972992689232977128058784578285264926899) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (182 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_182 :
    recurrence2Scalar3Shift.coeff 182 =
      -(((234026634952173438830290046925778115085568404659995918693 * 10 ^ 70 +
        0192436322438757415130905725241741057789296159697711300532886907754337) * 10 ^ 70 +
        4296024215889431454286050230906343173213742758663976237343828224310323) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (183 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_183 :
    recurrence2Scalar3Shift.coeff 183 =
      (((499195232997513314012764576349976584442088063926758164792 * 10 ^ 70 +
        4702288302326583629180391112873760096424629141168779866116770937214296) * 10 ^ 70 +
        5694033893318328806993034002227852883148521728287018249101554752784191) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (184 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_184 :
    recurrence2Scalar3Shift.coeff 184 =
      -(((166248006315937458013710974539351212109309417276016802330 * 10 ^ 70 +
        9553769675753775899819321718928956977694759305324554364924088382918768) * 10 ^ 70 +
        9935148805692368647974229535123304570755606065262728959893245073777573) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (185 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_185 :
    recurrence2Scalar3Shift.coeff 185 =
      -(((3013041961112276637661986517848484160008517496583087421007 * 10 ^ 70 +
        1058120493161501490769033176667418681162654750675502708496436851986403) * 10 ^ 70 +
        6171527315251892706567098158633203958588638775834651719962251484197940) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (186 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_186 :
    recurrence2Scalar3Shift.coeff 186 =
      (((12722761279915026636329494917699421546909032678651095583270 * 10 ^ 70 +
        2376912818099386379679004696454387487370053251546572499078246287132345) * 10 ^ 70 +
        9035215969503296314884095487563846081178172326839946699848286366485795) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (187 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_187 :
    recurrence2Scalar3Shift.coeff 187 =
      -(((27461863230088454769476340528496363907248749826602648481254 * 10 ^ 70 +
        6700361414785445749512694940889595956919800564823761409328047036467506) * 10 ^ 70 +
        6288014690920514527480501452526336806521970252262502682193895932505406) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (188 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_188 :
    recurrence2Scalar3Shift.coeff 188 =
      (((17074540913738883852474944537469798915104704744300025015574 * 10 ^ 70 +
        5220180598950547115469077493376955177843441708344151823760591457698305) * 10 ^ 70 +
        0046267176506205510951380608357965893019468966474384969593985062282095) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (189 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_189 :
    recurrence2Scalar3Shift.coeff 189 =
      (((121348441059211346575064884991976308049126703828981565968676 * 10 ^ 70 +
        1111092012402808910553832914188340626954524626702422964777339159919202) * 10 ^ 70 +
        1506464856601432186460881971143515298339081322985848402127927184927633) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (190 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_190 :
    recurrence2Scalar3Shift.coeff 190 =
      -(((579207715759652673330394565298674457458689793763025232881828 * 10 ^ 70 +
        4380039350392152229107683394633530125940133992156632508983544632677375) * 10 ^ 70 +
        5913414291538946378203359518773022570257448300982073879832602181076101) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (191 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_191 :
    recurrence2Scalar3Shift.coeff 191 =
      (((1425253554506197002289548736801505487527698755846217978396859 * 10 ^ 70 +
        3634234056722963998762257973704823213326459400973023857325791214541475) * 10 ^ 70 +
        5020870750823737363856501878415107176688363535661553467636072862041066) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (192 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_192 :
    recurrence2Scalar3Shift.coeff 192 =
      -(((1737672259765204840266102165903303807118096759173493644733856 * 10 ^ 70 +
        7951415668180214161277530471987905004965101646619695208872988237708610) * 10 ^ 70 +
        5954025712118473542193533091477959056252573135651308877574364453962814) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (193 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_193 :
    recurrence2Scalar3Shift.coeff 193 =
      -(((2341213264667649007432497334380806019915742198671486700744085 * 10 ^ 70 +
        1583733026427652210261387153516457221071705028264831894975995607254881) * 10 ^ 70 +
        7672014356697147754300282264022145207441739717780744625844064254730728) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (194 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_194 :
    recurrence2Scalar3Shift.coeff 194 =
      (((19762268144938786622849578841354575201860504327868433579022110 * 10 ^ 70 +
        3675476426096230882903628345491194283747368691082318043854413897810205) * 10 ^ 70 +
        6571139213542922406815684455800719367169253989375308121181971830805599) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (195 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_195 :
    recurrence2Scalar3Shift.coeff 195 =
      -(((61582361836249861564568135477175975416419091174344012287175397 * 10 ^ 70 +
        8521303957789580044530667087751901860064446695190971231176593388237066) * 10 ^ 70 +
        5817761429542373527961442047425524274030778927650398722040016570608601) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (196 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_196 :
    recurrence2Scalar3Shift.coeff 196 =
      (((118283494311998395512897354786840745724473789669730575012696058 * 10 ^ 70 +
        4453212018273758532540476853105965712922048632384591643092958323569680) * 10 ^ 70 +
        1441555040485425863166262267358811492352427807415359291919164420816636) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (197 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_197 :
    recurrence2Scalar3Shift.coeff 197 =
      -(((93097788176188450082387905902690737484541051564634384396837355 * 10 ^ 70 +
        4655460846402576955787894822977528746584640063151148793023473367835754) * 10 ^ 70 +
        3711264070777055308313268934866798136747287394559126932879434453246709) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (198 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_198 :
    recurrence2Scalar3Shift.coeff 198 =
      -(((322237370454817762773830351793015017384912527841183858167777786 * 10 ^ 70 +
        8251895747878470868916194295940427177188338541691884771825883469248862) * 10 ^ 70 +
        6132186503128559763320072085348583995033866335577840379384265990436372) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (199 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_199 :
    recurrence2Scalar3Shift.coeff 199 =
      (((1759314091295987741221471843889458209596986961057910634213025417 * 10 ^ 70 +
        5079209000700474949886853952326818257188062484040458686960771488215790) * 10 ^ 70 +
        0047920426597838430856069020028044848797638849804572116960811814408549) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (200 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_200 :
    recurrence2Scalar3Shift.coeff 200 =
      -(((4962202977099505546130381528641322903979541039939358388151005688 * 10 ^ 70 +
        5264671845918721105914802813174939598479893988475831394836170260611722) * 10 ^ 70 +
        7249183621294223639427310808470180334632656515304702778991460509395775) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (201 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_201 :
    recurrence2Scalar3Shift.coeff 201 =
      (((9487645006180730288289484844646173634531704690001600035356656146 * 10 ^ 70 +
        0931451186914032277680733102854794740813176124859052337167936075713358) * 10 ^ 70 +
        4926701296148672822479682156571363961164891894366078455460488693632954) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (202 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_202 :
    recurrence2Scalar3Shift.coeff 202 =
      -(((10023946297185480540696779100374905682559563603798964772294470262 * 10 ^ 70 +
        8409054120106950195847259850492012283478943619726253344905848798304526) * 10 ^ 70 +
        9939700007179196382207025303671886471716327775837940070509477028188114) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (203 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_203 :
    recurrence2Scalar3Shift.coeff 203 =
      -(((10854721966917124371099952202004747848293724463227111385788756079 * 10 ^ 70 +
        6399284443177423959150805284968924112625938705597238497264196059016284) * 10 ^ 70 +
        9937752164713766242383252552674546887547825279281074504146923933774727) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (204 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_204 :
    recurrence2Scalar3Shift.coeff 204 =
      (((92205375865141031622757764176256380215466505642650518595994419112 * 10 ^ 70 +
        5990313135572008337819063357628995310797401611504979604140640547175441) * 10 ^ 70 +
        7847528021466155829607699744722238443536063291176012565599053471941763) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (205 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_205 :
    recurrence2Scalar3Shift.coeff 205 =
      -(((297363908709561992311071468299749142435065467617972001871488079592 * 10 ^ 70 +
        3232498337217658202855565005782711203246674462571359336107631288926913) * 10 ^ 70 +
        5578831101013505778641841640505780330207424694789090942753204385384601) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (206 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_206 :
    recurrence2Scalar3Shift.coeff 206 =
      (((683814821093515261895514176483710997170679481820603442977823587188 * 10 ^ 70 +
        1174752001245505071034729071467057986708929997236490923120786384487084) * 10 ^ 70 +
        2286306145243708297990147425569052684909494236001094844537474206279059) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (207 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_207 :
    recurrence2Scalar3Shift.coeff 207 =
      -(((1187354170957883417828269469523753687903944199155731742816935176611 * 10 ^ 70 +
        0969739881316593228797016063953496937703848614834559714480442564870475) * 10 ^ 70 +
        1026257813180107126868102531182532295357708163138428169548485609410123) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (208 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_208 :
    recurrence2Scalar3Shift.coeff 208 =
      (((1336861326723046781035244245718655317558539376069113954449099748623 * 10 ^ 70 +
        3216070652671004553851165586449262263029859872552372114299254693402556) * 10 ^ 70 +
        1278863960566170219695854868716203716390085950075076578993401617738389) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (209 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_209 :
    recurrence2Scalar3Shift.coeff 209 =
      (((296236935032221739628149598306647218362031491484623673503949494047 * 10 ^ 70 +
        1227850666781853696941097697742245579103467142431679257709090011934623) * 10 ^ 70 +
        7626014820625877619936079188641401266175300193169453782945288670545383) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (210 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_210 :
    recurrence2Scalar3Shift.coeff 210 =
      -(((6958860517356519880978445361216015873740437308802430100351894588669 * 10 ^ 70 +
        3709511799973111218118434889290218799480102519083067221962187864092832) * 10 ^ 70 +
        1869474230287312139830825266023997210518837368812611326598310206862883) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (211 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_211 :
    recurrence2Scalar3Shift.coeff 211 =
      (((24753911114979836431765086575832464934780892806378350940980731332095 * 10 ^ 70 +
        0579339331548262340198629434560319087445997890102274044814572631557309) * 10 ^ 70 +
        5060209694044071102518124896044708753042584627690933005017568720442707) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (212 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_212 :
    recurrence2Scalar3Shift.coeff 212 =
      -(((63350556360526446349376800990827123966219357856802819781910781162826 * 10 ^ 70 +
        3998166656180056358143554499133022819535284389459809551066873140528686) * 10 ^ 70 +
        5067874871528545213253943792452155175426565347068960078885701046029187) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (213 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_213 :
    recurrence2Scalar3Shift.coeff 213 =
      (((135284065247854226564862372685451241257520185711198147156071615378701 * 10 ^ 70 +
        0121207410430559769597921503918700865453418534940888582400295693384555) * 10 ^ 70 +
        1748403176009583835944224502377783796660977159648567228025414057511722) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (214 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_214 :
    recurrence2Scalar3Shift.coeff 214 =
      -(((252072991535807150458868974137229238934999124031373031153465582232373 * 10 ^ 70 +
        3800387688205079983984035597618712923444687303838643232056274909123663) * 10 ^ 70 +
        9701432102910678849383610126690671280968099377457216785833720931307021) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (215 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_215 :
    recurrence2Scalar3Shift.coeff 215 =
      (((414860082638920230154661905892720919442272889026265555641249868465224 * 10 ^ 70 +
        2580652620020414121033494282626772788651774046062018689278733202129025) * 10 ^ 70 +
        1803874986324026154725090140915512959739625527176563204567496514267234) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (216 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_216 :
    recurrence2Scalar3Shift.coeff 216 =
      -(((597399795664008549129478140894280020528707275124652927406271642834597 * 10 ^ 70 +
        7273855692415566658116114367070359683853813431728495431704432454887122) * 10 ^ 70 +
        0346317715760224680807257959314944676436495467051925108686667476012827) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (217 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_217 :
    recurrence2Scalar3Shift.coeff 217 =
      (((720537547910563220747853104308554463313283333249673215583967100969400 * 10 ^ 70 +
        2944044702736351490154193729155511125412191844900095965928781534735562) * 10 ^ 70 +
        2991311460102604572534166448337420376189531875994764443932781482102043) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (218 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_218 :
    recurrence2Scalar3Shift.coeff 218 =
      -(((620281461112726492270832933792190727562429331611482856114027597283771 * 10 ^ 70 +
        7237749697745524779023473283816919459947822033656594718007908359086617) * 10 ^ 70 +
        7991798271178611214762382969749054128981144963563662277289869851580037) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (219 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_219 :
    recurrence2Scalar3Shift.coeff 219 =
      (((16091955425207640520363956231000053621017886181065332781118944867561 * 10 ^ 70 +
        8212328423671394222768852138633284816216931062105207465479901078931428) * 10 ^ 70 +
        8616881117440930742488936238936081374559501387061907385791407231777621) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (220 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_220 :
    recurrence2Scalar3Shift.coeff 220 =
      (((1508791904422324361398127499892966062000001401665114593254333487707781 * 10 ^ 70 +
        1321396885979176512582029405885920903804984178259144806825697806998069) * 10 ^ 70 +
        7144332708006741786491164393669207171059623658786896469667151566508183) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (221 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_221 :
    recurrence2Scalar3Shift.coeff 221 =
      -(((4499173537103262881392456778372404745655765223310923980527121248732276 * 10 ^ 70 +
        4754126118426452287352483475005908354523685822807895929983506312127143) * 10 ^ 70 +
        6887938433088826835503150075880907184207020034467269749276599772361451) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (222 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_222 :
    recurrence2Scalar3Shift.coeff 222 =
      (((9575784208609970766677245038643471253870903574426245428952672966982374 * 10 ^ 70 +
        5984118818686828910486911484835290624880123980384102744507688071997829) * 10 ^ 70 +
        1531987854921404386292255955514931115495445772292586861180184944396752) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (223 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_223 :
    recurrence2Scalar3Shift.coeff 223 =
      -((((1 * 10 ^ 70 +
        7328984251466669372985966453993878033490025948807864609046280005835621) * 10 ^ 70 +
        4689522813561785925882117957782354807399430169356024256090306818453176) * 10 ^ 70 +
        8897075503430078164684607997002893293879019873648547893033929788223856) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (224 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_224 :
    recurrence2Scalar3Shift.coeff 224 =
      ((((2 * 10 ^ 70 +
        8160968261405189527778019038577455785316673645575917300933446566011458) * 10 ^ 70 +
        0790224646127543034754079996689120919406620155066658707313733366237595) * 10 ^ 70 +
        8421083485591042237380224168750414788968778611512585684146410040529875) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (225 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_225 :
    recurrence2Scalar3Shift.coeff 225 =
      -((((4 * 10 ^ 70 +
        2097656306435229660098181783981883510505133885362229380335678753006579) * 10 ^ 70 +
        0440535723240870036489799771245283490875356242375466836258762467855447) * 10 ^ 70 +
        8793616332193458284649241943383345348369116287721583728808262666963518) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (226 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_226 :
    recurrence2Scalar3Shift.coeff 226 =
      ((((5 * 10 ^ 70 +
        8610909030200441716771388159824568000877643747081139493137267266558986) * 10 ^ 70 +
        8517887644652286479904480772033046109662350484132591654350077641225928) * 10 ^ 70 +
        6546181089456324016429579566308042327857829990761311584574824554713429) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (227 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_227 :
    recurrence2Scalar3Shift.coeff 227 =
      -((((7 * 10 ^ 70 +
        6505177962071642768580298170613411729770790825546911366632432016940964) * 10 ^ 70 +
        5823485128736441184902386125544451057282217812232077799329214060977552) * 10 ^ 70 +
        6911863961525879770386126322357574440558974594000042484523749177114570) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (228 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_228 :
    recurrence2Scalar3Shift.coeff 228 =
      ((((9 * 10 ^ 70 +
        3922960816593053997552499453260996355099086174893055000335827898668625) * 10 ^ 70 +
        5673032164422917492031022757664932647295165378538138890288697981216336) * 10 ^ 70 +
        8509276177321234124194819178396789895170045373798976065558215535884837) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (229 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_229 :
    recurrence2Scalar3Shift.coeff 229 =
      -((((10 * 10 ^ 70 +
        8505889086560416513201815858687714734991611443895536313748773266574221) * 10 ^ 70 +
        9100689806662277673354349502581287253671053706978126779383677287807449) * 10 ^ 70 +
        1275575661368846164405260365162601312323380055704318925434417044353479) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
  rw [recurrence2Scalar3Shift_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (230 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_230 :
    recurrence2Scalar3Shift.coeff 230 =
      ((((11 * 10 ^ 70 +
        7713717355404766978385537460293410992866574132312995882504119879947453) * 10 ^ 70 +
        8312994183753055606763575676353225351582991311948337601588122282866466) * 10 ^ 70 +
        4443756915070275423609435132299358003536063149509043182491361277170037) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
    rw [show 102 = 18 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (231 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_231 :
    recurrence2Scalar3Shift.coeff 231 =
      -((((11 * 10 ^ 70 +
        9259268082698518545249092762584830995462594278846618980350570187329473) * 10 ^ 70 +
        6788824828340364822153731194052154833799219861256910009393922050124728) * 10 ^ 70 +
        9608415282249725633538417973596674338303308054030040382336475356470133) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
    rw [show 102 = 17 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (232 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_232 :
    recurrence2Scalar3Shift.coeff 232 =
      ((((11 * 10 ^ 70 +
        1576171684141322820159832351238650866755124263095193711341117276011912) * 10 ^ 70 +
        2960938385934977543479360951060892822580786001114744487107582000787394) * 10 ^ 70 +
        6542277173614285720360771661798252547451901490090564446990547597784911) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
    rw [show 102 = 16 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (233 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_233 :
    recurrence2Scalar3Shift.coeff 233 =
      -((((9 * 10 ^ 70 +
        4212235126228245450031901468774565670829302223816306995941757282593478) * 10 ^ 70 +
        0102067131984449302947552161114411232125625392636295221011616196993920) * 10 ^ 70 +
        3145769852712949075569074783894492917147406272657025068112862773351301) : ℚ) := by
  unfold recurrence2Scalar3Shift
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
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
