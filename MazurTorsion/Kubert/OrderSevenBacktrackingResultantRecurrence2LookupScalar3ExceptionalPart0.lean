/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2ExceptionalProduct_coeff_0
  recurrence2ExceptionalProduct_coeff_1
  recurrence2ExceptionalProduct_coeff_2
  recurrence2ExceptionalProduct_coeff_3
  recurrence2ExceptionalProduct_coeff_4
  recurrence2ExceptionalProduct_coeff_5
  recurrence2ExceptionalProduct_coeff_6
  recurrence2ExceptionalProduct_coeff_7
  recurrence2ExceptionalProduct_coeff_8
  recurrence2ExceptionalProduct_coeff_9
  recurrence2ExceptionalProduct_coeff_10
  recurrence2ExceptionalProduct_coeff_11
  recurrence2ExceptionalProduct_coeff_12
  recurrence2ExceptionalProduct_coeff_13
  recurrence2ExceptionalProduct_coeff_14
  recurrence2ExceptionalProduct_coeff_15
  recurrence2ExceptionalProduct_coeff_16
  recurrence2ExceptionalProduct_coeff_17
  recurrence2ExceptionalProduct_coeff_18
  recurrence2ExceptionalProduct_coeff_19
  recurrence2ExceptionalProduct_coeff_20
  recurrence2ExceptionalProduct_coeff_21
  recurrence2ExceptionalProduct_coeff_22
  recurrence2ExceptionalProduct_coeff_23
  recurrence2ExceptionalProduct_coeff_24
  recurrence2ExceptionalProduct_coeff_25
  recurrence2ExceptionalProduct_coeff_26
  recurrence2ExceptionalProduct_coeff_27
  recurrence2ExceptionalProduct_coeff_28
  recurrence2ExceptionalProduct_coeff_29
  recurrence2ExceptionalProduct_coeff_30
  recurrence2ExceptionalProduct_coeff_31
  recurrence2ExceptionalProduct_coeff_32
  recurrence2ExceptionalProduct_coeff_33
  recurrence2ExceptionalProduct_coeff_34
  recurrence2ExceptionalProduct_coeff_35
  recurrence2ExceptionalProduct_coeff_36
  recurrence2ExceptionalProduct_coeff_37
  recurrence2ExceptionalProduct_coeff_38
  recurrence2ExceptionalProduct_coeff_39
  recurrence2ExceptionalProduct_coeff_40
  recurrence2ExceptionalProduct_coeff_41
  recurrence2ExceptionalProduct_coeff_42
  recurrence2ExceptionalProduct_coeff_43
  recurrence2ExceptionalProduct_coeff_44
  recurrence2ExceptionalProduct_coeff_45
  recurrence2ExceptionalProduct_coeff_46
  recurrence2ExceptionalProduct_coeff_47
  recurrence2ExceptionalProduct_coeff_48
  recurrence2ExceptionalProduct_coeff_49
  recurrence2ExceptionalProduct_coeff_50
  recurrence2ExceptionalProduct_coeff_51
  recurrence2ExceptionalProduct_coeff_52
  recurrence2ExceptionalProduct_coeff_53
  recurrence2ExceptionalProduct_coeff_54
  recurrence2ExceptionalProduct_coeff_55
  recurrence2ExceptionalProduct_coeff_56
  recurrence2ExceptionalProduct_coeff_57
  recurrence2ExceptionalProduct_coeff_58
  recurrence2ExceptionalProduct_coeff_59
  recurrence2ExceptionalProduct_coeff_60
  recurrence2ExceptionalProduct_coeff_61
  recurrence2ExceptionalProduct_coeff_62
  recurrence2ExceptionalProduct_coeff_63
  recurrence2ExceptionalProduct_coeff_64
  recurrence2ExceptionalProduct_coeff_65
  recurrence2ExceptionalProduct_coeff_66
  recurrence2ExceptionalProduct_coeff_67
  recurrence2ExceptionalProduct_coeff_68
  recurrence2ExceptionalProduct_coeff_69
  recurrence2ExceptionalProduct_coeff_70
  recurrence2ExceptionalProduct_coeff_71
  recurrence2ExceptionalProduct_coeff_72
  recurrence2ExceptionalProduct_coeff_73
  recurrence2ExceptionalProduct_coeff_74
  recurrence2ExceptionalProduct_coeff_75
  recurrence2ExceptionalProduct_coeff_76
  recurrence2ExceptionalProduct_coeff_77
  recurrence2ExceptionalProduct_coeff_78
  recurrence2ExceptionalProduct_coeff_79
  recurrence2ExceptionalProduct_coeff_80
  recurrence2ExceptionalProduct_coeff_81
  recurrence2ExceptionalProduct_coeff_82
  recurrence2ExceptionalProduct_coeff_83
  recurrence2ExceptionalProduct_coeff_84
  recurrence2ExceptionalProduct_coeff_85
  recurrence2ExceptionalProduct_coeff_86
  recurrence2ExceptionalProduct_coeff_87
  recurrence2ExceptionalProduct_coeff_88
  recurrence2ExceptionalProduct_coeff_89
  recurrence2ExceptionalProduct_coeff_90
  recurrence2ExceptionalProduct_coeff_91
  recurrence2ExceptionalProduct_coeff_92
  recurrence2ExceptionalProduct_coeff_93
  recurrence2ExceptionalProduct_coeff_94
  recurrence2ExceptionalProduct_coeff_95
  recurrence2ExceptionalProduct_coeff_96
  recurrence2ExceptionalProduct_coeff_97
  recurrence2ExceptionalProduct_coeff_98
  recurrence2ExceptionalProduct_coeff_99
  recurrence2ExceptionalProduct_coeff_100
  recurrence2ExceptionalProduct_coeff_101
  recurrence2ExceptionalProduct_coeff_102
  recurrence2ExceptionalProduct_coeff_103
  recurrence2ExceptionalProduct_coeff_104
  recurrence2ExceptionalProduct_coeff_105
  recurrence2ExceptionalProduct_coeff_106
  recurrence2ExceptionalProduct_coeff_107
  recurrence2ExceptionalProduct_coeff_108
  recurrence2ExceptionalProduct_coeff_109
  recurrence2ExceptionalProduct_coeff_110
  recurrence2ExceptionalProduct_coeff_111
  recurrence2ExceptionalProduct_coeff_112
  recurrence2ExceptionalProduct_coeff_113
  recurrence2ExceptionalProduct_coeff_114
  recurrence2ExceptionalProduct_coeff_115
  recurrence2ExceptionalProduct_coeff_116
  recurrence2ExceptionalProduct_coeff_117
  recurrence2ExceptionalProduct_coeff_118
  recurrence2ExceptionalProduct_coeff_119
  recurrence2ExceptionalProduct_coeff_120
  recurrence2ExceptionalProduct_coeff_121
  recurrence2ExceptionalProduct_coeff_122
  recurrence2ExceptionalProduct_coeff_123
  recurrence2ExceptionalProduct_coeff_124
  recurrence2ExceptionalProduct_coeff_125
  recurrence2ExceptionalProduct_coeff_126
  recurrence2ExceptionalProduct_coeff_127
  recurrence2ExceptionalProduct_coeff_128
  recurrence2ExceptionalProduct_coeff_129
  recurrence2ExceptionalProduct_coeff_130
  recurrence2ExceptionalProduct_coeff_131
  recurrence2ExceptionalProduct_coeff_132
  recurrence2ExceptionalProduct_coeff_133
  recurrence2ExceptionalProduct_coeff_134
  recurrence2ExceptionalProduct_coeff_135
  recurrence2ExceptionalProduct_coeff_136
  recurrence2ExceptionalProduct_coeff_137
  recurrence2ExceptionalProduct_coeff_138
  recurrence2ExceptionalProduct_coeff_139
  recurrence2ExceptionalProduct_coeff_140
  recurrence2ExceptionalProduct_coeff_141
  recurrence2ExceptionalProduct_coeff_142
  recurrence2ExceptionalProduct_coeff_143
  recurrence2ExceptionalProduct_coeff_144
  recurrence2ExceptionalProduct_coeff_145
  recurrence2ExceptionalProduct_coeff_146
  recurrence2ExceptionalProduct_coeff_147
  recurrence2ExceptionalProduct_coeff_148
  recurrence2ExceptionalProduct_coeff_149
  recurrence2ExceptionalProduct_coeff_150
  recurrence2ExceptionalProduct_coeff_151
  recurrence2ExceptionalProduct_coeff_152
  recurrence2ExceptionalProduct_coeff_153
  recurrence2ExceptionalProduct_coeff_154
  recurrence2ExceptionalProduct_coeff_155
  recurrence2ExceptionalProduct_coeff_156
  recurrence2ExceptionalProduct_coeff_157
  recurrence2ExceptionalProduct_coeff_158
  recurrence2ExceptionalProduct_coeff_159
  recurrence2ExceptionalProduct_coeff_160
  recurrence2ExceptionalProduct_coeff_161
  recurrence2ExceptionalProduct_coeff_162
  recurrence2ExceptionalProduct_coeff_163
  recurrence2ExceptionalProduct_coeff_164
  recurrence2ExceptionalProduct_coeff_165
  recurrence2ExceptionalProduct_coeff_166
  recurrence2ExceptionalProduct_coeff_167
  recurrence2ExceptionalProduct_coeff_168
  recurrence2ExceptionalProduct_coeff_169
  recurrence2ExceptionalProduct_coeff_170
  recurrence2ExceptionalProduct_coeff_171
  recurrence2ExceptionalProduct_coeff_172
  recurrence2ExceptionalProduct_coeff_173
  recurrence2ExceptionalProduct_coeff_174
  recurrence2ExceptionalProduct_coeff_175
  recurrence2ExceptionalProduct_coeff_176
  recurrence2ExceptionalProduct_coeff_177
  recurrence2ExceptionalProduct_coeff_178
  recurrence2ExceptionalProduct_coeff_179
  recurrence2ExceptionalProduct_coeff_180
  recurrence2ExceptionalProduct_coeff_181
  recurrence2ExceptionalProduct_coeff_182
  recurrence2ExceptionalProduct_coeff_183
  recurrence2ExceptionalProduct_coeff_184
  recurrence2ExceptionalProduct_coeff_185
  recurrence2ExceptionalProduct_coeff_186
  recurrence2ExceptionalProduct_coeff_187
  recurrence2ExceptionalProduct_coeff_188
  recurrence2ExceptionalProduct_coeff_189
  recurrence2ExceptionalProduct_coeff_190
  recurrence2ExceptionalProduct_coeff_191
  recurrence2ExceptionalProduct_coeff_192
  recurrence2ExceptionalProduct_coeff_193
  recurrence2C3_coeff_0
  recurrence2C3_coeff_1
  recurrence2C3_coeff_2
  recurrence2C3_coeff_3
  recurrence2C3_coeff_4
  recurrence2C3_coeff_5
  recurrence2C3_coeff_6
  recurrence2C3_coeff_7
  recurrence2C3_coeff_8
  recurrence2C3_coeff_9
  recurrence2C3_coeff_10
  recurrence2C3_coeff_11
  recurrence2C3_coeff_12
  recurrence2C3_coeff_13
  recurrence2C3_coeff_14
  recurrence2C3_coeff_15
  recurrence2C3_coeff_16
  recurrence2C3_coeff_17
  recurrence2C3_coeff_18
  recurrence2C3_coeff_19
  recurrence2C3_coeff_20
  recurrence2C3_coeff_21
  recurrence2C3_coeff_22
  recurrence2C3_coeff_23
  recurrence2C3_coeff_24
  recurrence2C3_coeff_25
  recurrence2C3_coeff_26
  recurrence2C3_coeff_27
  recurrence2C3_coeff_28
  recurrence2C3_coeff_29
  recurrence2C3_coeff_30
  recurrence2C3_coeff_31
  recurrence2C3_coeff_32
  recurrence2C3_coeff_33
  recurrence2C3_coeff_34
  recurrence2C3_coeff_35
  recurrence2C3_coeff_36
  recurrence2C3_coeff_37
  recurrence2C3_coeff_38
  recurrence2C3_coeff_39
  recurrence2C3_coeff_40
  recurrence2C3_coeff_41
  recurrence2C3_coeff_42
  recurrence2C3_coeff_43
  recurrence2C3_coeff_44
  recurrence2C3_coeff_45
  recurrence2C3_coeff_46
  recurrence2C3_coeff_47
  recurrence2C3_coeff_48
  recurrence2C3_coeff_49
  recurrence2C3_coeff_50
  recurrence2C3_coeff_51
  recurrence2C3_coeff_52
  recurrence2C3_coeff_53
  recurrence2C3_coeff_54
  recurrence2C3_coeff_55
  recurrence2C3_coeff_56
  recurrence2C3_coeff_57
  recurrence2C3_coeff_58
  recurrence2C3_coeff_59
  recurrence2C3_coeff_60
  recurrence2C3_coeff_61
  recurrence2C3_coeff_62
  recurrence2C3_coeff_63
  recurrence2C3_coeff_64
  recurrence2C3_coeff_65
  recurrence2C3_coeff_66
  recurrence2C3_coeff_67
  recurrence2C3_coeff_68
  recurrence2C3_coeff_69
  recurrence2C3_coeff_70
  recurrence2C3_coeff_71
  recurrence2C3_coeff_72
  recurrence2C3_coeff_73
  recurrence2C3_coeff_74
  recurrence2C3_coeff_75
  recurrence2C3_coeff_76
  recurrence2C3_coeff_77
  recurrence2C3_coeff_78
  recurrence2C3_coeff_79
  recurrence2C3_coeff_80
  recurrence2C3_coeff_81
  recurrence2C3_coeff_82
  recurrence2C3_coeff_83
  recurrence2C3_coeff_84
  recurrence2C3_coeff_85
  recurrence2C3_coeff_86
  recurrence2C3_coeff_87
  recurrence2C3_coeff_88
  recurrence2C3_coeff_89
  recurrence2C3_coeff_90
  recurrence2C3_coeff_91
  recurrence2C3_coeff_92
  recurrence2C3_coeff_93
  recurrence2C3_coeff_94
  recurrence2C3_coeff_95
  recurrence2C3_coeff_96
  recurrence2C3_coeff_97
  recurrence2C3_coeff_98
  recurrence2C3_coeff_99
  recurrence2C3_coeff_100
  recurrence2C3_coeff_101
  recurrence2C3_coeff_102
  recurrence2C3_coeff_103
  recurrence2C3_coeff_104
  recurrence2C3_coeff_105
  recurrence2C3_coeff_106
  recurrence2C3_coeff_107
  recurrence2C3_coeff_108
  recurrence2C3_coeff_109
  recurrence2C3_coeff_110
  recurrence2C3_coeff_111
  recurrence2C3_coeff_112
  recurrence2C3_coeff_113
  recurrence2C3_coeff_114
  recurrence2C3_coeff_115
  recurrence2C3_coeff_116
  recurrence2C3_coeff_117
  recurrence2C3_coeff_118
  recurrence2C3_coeff_119
  recurrence2C3_coeff_120
  recurrence2C3_coeff_121
  recurrence2C3_coeff_122
  recurrence2C3_coeff_123
  recurrence2C3_coeff_124
  recurrence2C3_coeff_125
  recurrence2C3_coeff_126
  recurrence2C3_coeff_127
  recurrence2C3_coeff_128
  recurrence2C3_coeff_129
  recurrence2C3_coeff_130
  recurrence2C3_coeff_131
  recurrence2C3_coeff_132
  recurrence2C3_coeff_133
  recurrence2C3_coeff_134
  recurrence2C3_coeff_135
  recurrence2C3_coeff_136
  recurrence2C3_coeff_137
  recurrence2C3_coeff_138
  recurrence2C3_coeff_139
  recurrence2C3_coeff_140
  recurrence2C3_coeff_141
  recurrence2C3_coeff_142
  recurrence2C3_coeff_143
  recurrence2C3_coeff_144
  recurrence2C3_coeff_145
  recurrence2C3_coeff_146
  recurrence2C3_coeff_147
  recurrence2C3_coeff_148
  recurrence2C3_coeff_149
  recurrence2C3_coeff_150
  recurrence2C3_coeff_151
  recurrence2C3_coeff_152
  recurrence2C3_coeff_153
  recurrence2C3_coeff_154
  recurrence2C3_coeff_155
  recurrence2C3_coeff_156
  recurrence2C3_coeff_157
  recurrence2C3_coeff_158
  recurrence2C3_coeff_159
  recurrence2C3_coeff_160
  recurrence2C3_coeff_161
  recurrence2C3_coeff_162
  recurrence2C3_coeff_163
  recurrence2C3_coeff_164
  recurrence2C3_coeff_165
  recurrence2C3_coeff_166
  recurrence2C3_coeff_167
  recurrence2C3_coeff_168
  recurrence2C3_coeff_169
  recurrence2C3_coeff_170
  recurrence2C3_coeff_171
  recurrence2C3_coeff_172
  recurrence2C3_coeff_173
  recurrence2C3_coeff_174
  recurrence2C3_coeff_175
  recurrence2C3_coeff_176
  recurrence2C3_coeff_177
  recurrence2C3_coeff_178
  recurrence2C3_coeff_179
  recurrence2C3_coeff_180
  recurrence2C3_coeff_181
  recurrence2C3_coeff_182

theorem recurrence2Scalar3Exceptional_coeff_0 :
    recurrence2Scalar3Exceptional.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_1 :
    recurrence2Scalar3Exceptional.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_2 :
    recurrence2Scalar3Exceptional.coeff 2 =
      (2796869376 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_3 :
    recurrence2Scalar3Exceptional.coeff 3 =
      (-6239940903504 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_4 :
    recurrence2Scalar3Exceptional.coeff 4 =
      (-34738626578046312 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_5 :
    recurrence2Scalar3Exceptional.coeff 5 =
      (33448901926260658584 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_6 :
    recurrence2Scalar3Exceptional.coeff 6 =
      (76728798195414181381136 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_7 :
    recurrence2Scalar3Exceptional.coeff 7 =
      (-76733348848149146990400988 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_8 :
    recurrence2Scalar3Exceptional.coeff 8 =
      (-38363106489573021090039044696 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_9 :
    recurrence2Scalar3Exceptional.coeff 9 =
      (59668748252499755964119499376720 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_10 :
    recurrence2Scalar3Exceptional.coeff 10 =
      (-16462243536116116724219708422451564 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_11 :
    recurrence2Scalar3Exceptional.coeff 11 =
      (-785060373352251563964950149911165896 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_12 :
    recurrence2Scalar3Exceptional.coeff 12 =
      (758788815774248443355658936771659232718 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_13 :
    recurrence2Scalar3Exceptional.coeff 13 =
      (-2280661548630736122835048680990461953338 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_14 :
    recurrence2Scalar3Exceptional.coeff 14 =
      (-45475267422775360175218757866667438176058464 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_15 :
    recurrence2Scalar3Exceptional.coeff 15 =
      (16084325847850687499963201345054561352412086369 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_16 :
    recurrence2Scalar3Exceptional.coeff 16 =
      (-4322166142015770418100349021596022699857094819620 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_17 :
    recurrence2Scalar3Exceptional.coeff 17 =
      (911077692272539216443400885262103270306448707607230 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_18 :
    recurrence2Scalar3Exceptional.coeff 18 =
      (-141426841381915690260919338303052773344691290827931375 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_19 :
    recurrence2Scalar3Exceptional.coeff 19 =
      (15496426236939601562278680935859075275334193475592342332 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_20 :
    recurrence2Scalar3Exceptional.coeff 20 =
      (-1019407657555669782934151700815368102342470053701685827872 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_21 :
    recurrence2Scalar3Exceptional.coeff 21 =
      (-5385824201192950064159700510387370216112392412717013540718 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_22 :
    recurrence2Scalar3Exceptional.coeff 22 =
      (11046656029044875575533300227454170546940179360540765008709418 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_23 :
    recurrence2Scalar3Exceptional.coeff 23 =
      (-1544570628407461539159663743546089644646695377317824483162641729 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_24 :
    recurrence2Scalar3Exceptional.coeff 24 =
      (124317250329558182146671082857375589207423969138274068390529120118 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_25 :
    recurrence2Scalar3Exceptional.coeff 25 =
      (-5622941998771786800745057538994287200823520367052813582295404754022 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_26 :
    recurrence2Scalar3Exceptional.coeff 26 =
      (-26641527131991333837469906294983685060913392376433167311051092586168 : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_27 :
    recurrence2Scalar3Exceptional.coeff 27 =
      ((2 * 10 ^ 70 +
        9442742564293847795245774181561649929077208235724693366801115646183330) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_28 :
    recurrence2Scalar3Exceptional.coeff 28 =
      -((293 * 10 ^ 70 +
        5565767533692479193058167019970531466621509512430338844661843877424725) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_29 :
    recurrence2Scalar3Exceptional.coeff 29 =
      ((18523 * 10 ^ 70 +
        6888472682212404217909650714062677742740889537689273247300487073235204) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_30 :
    recurrence2Scalar3Exceptional.coeff 30 =
      -((856285 * 10 ^ 70 +
        2159264894324984537436348420231677392110399583239986577847010533763676) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_31 :
    recurrence2Scalar3Exceptional.coeff 31 =
      ((29877157 * 10 ^ 70 +
        4799327605577406525961474124898532060179582539082774641628332885031594) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_32 :
    recurrence2Scalar3Exceptional.coeff 32 =
      -((777340642 * 10 ^ 70 +
        3009825744070866973892420742019934302121959322963585642344240858458319) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_33 :
    recurrence2Scalar3Exceptional.coeff 33 =
      ((14746650453 * 10 ^ 70 +
        2885048257333693034717482282422441561112685095392046261766046616264953) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_34 :
    recurrence2Scalar3Exceptional.coeff 34 =
      -((246809538992 * 10 ^ 70 +
        0983589331079367359274479898393306460328099476000678548703959274073393) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_35 :
    recurrence2Scalar3Exceptional.coeff 35 =
      ((8783328150886 * 10 ^ 70 +
        3087147360370494578593705327795855376347270047058202701333771514897965) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_36 :
    recurrence2Scalar3Exceptional.coeff 36 =
      -((502684597610799 * 10 ^ 70 +
        7347003131989812494266002287106690536462744059573719623803233237269822) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_37 :
    recurrence2Scalar3Exceptional.coeff 37 =
      ((22622748110896411 * 10 ^ 70 +
        3731389736182158011657213780479880360293698858600012395377084737000785) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_38 :
    recurrence2Scalar3Exceptional.coeff 38 =
      -((754059700537661992 * 10 ^ 70 +
        0950992757225603142629720443766418629073418075601907101451569149579974) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_39 :
    recurrence2Scalar3Exceptional.coeff 39 =
      ((19624176760978523920 * 10 ^ 70 +
        2398635335548560754552729803199187595408357083708033683656018570488933) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_40 :
    recurrence2Scalar3Exceptional.coeff 40 =
      -((431443954653152420563 * 10 ^ 70 +
        4796909451469152615575843165328908308313042917208630865941587774163779) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_41 :
    recurrence2Scalar3Exceptional.coeff 41 =
      ((9229763319288110490663 * 10 ^ 70 +
        1962008020962622604602549728206997713459941917764585898127762128245337) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_42 :
    recurrence2Scalar3Exceptional.coeff 42 =
      -((227528212549356724438737 * 10 ^ 70 +
        5291746611933950903684932213066334531256560013757951095579433293750019) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_43 :
    recurrence2Scalar3Exceptional.coeff 43 =
      ((6537249361641912455194705 * 10 ^ 70 +
        6132376635862155310633500807344018723006629304098788022103989625483326) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_44 :
    recurrence2Scalar3Exceptional.coeff 44 =
      -((192851428725022920951978391 * 10 ^ 70 +
        7460859522539911940120698639608337018530420454257961034748133131145990) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_45 :
    recurrence2Scalar3Exceptional.coeff 45 =
      ((5395285126489414259761535406 * 10 ^ 70 +
        9848425504348886837932007596736804277098605540954793158616994434176783) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_46 :
    recurrence2Scalar3Exceptional.coeff 46 =
      -((141454276058134377148554738909 * 10 ^ 70 +
        5008832347070624592636862960092887264387946885647751754421282957552730) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_47 :
    recurrence2Scalar3Exceptional.coeff 47 =
      ((3508351137907481780743971116933 * 10 ^ 70 +
        2697774832565411369227817176115863399232022600714780615931975455933649) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_48 :
    recurrence2Scalar3Exceptional.coeff 48 =
      -((82754316076907696086964946724393 * 10 ^ 70 +
        8493742158618495734572183252209634611044960155471405032064820267573333) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_49 :
    recurrence2Scalar3Exceptional.coeff 49 =
      ((1853099325599491923401445727790526 * 10 ^ 70 +
        5942291831247405698239436281653858053902063175826951610388095390064526) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_50 :
    recurrence2Scalar3Exceptional.coeff 50 =
      -((39276969252355478511421320639970583 * 10 ^ 70 +
        3437367281069073803782027135938069022418354761840954221324947054837883) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_51 :
    recurrence2Scalar3Exceptional.coeff 51 =
      ((788202338611073381309350026994312946 * 10 ^ 70 +
        2496527259762875529900828822447841199983784380393013807099357122642095) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_52 :
    recurrence2Scalar3Exceptional.coeff 52 =
      -((15028725028822301980770718942398656047 * 10 ^ 70 +
        8271578083576077955732435022785066496095072488241341248422375648176846) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_53 :
    recurrence2Scalar3Exceptional.coeff 53 =
      ((273417393540706798692346975570442251797 * 10 ^ 70 +
        3231996332099408598287844811583298964288278668136123928868122188502761) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_54 :
    recurrence2Scalar3Exceptional.coeff 54 =
      -((4759481131049642638820512178811628165979 * 10 ^ 70 +
        5827785512514437654150940263421162351752143286789839719017112049803304) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_55 :
    recurrence2Scalar3Exceptional.coeff 55 =
      ((79345850908930736016925441929590898579860 * 10 ^ 70 +
        8884725425224782296809645509627561268118401513006053732623667993223749) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_56 :
    recurrence2Scalar3Exceptional.coeff 56 =
      -((1266843537822275020315016858278783407708436 * 10 ^ 70 +
        2248969091635913332600063280891990530218426428162764829287186353467650) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_57 :
    recurrence2Scalar3Exceptional.coeff 57 =
      ((19374548887960313750242055310362050511524740 * 10 ^ 70 +
        0566392536599242250247477209456348170870526245778909824973828499313036) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_58 :
    recurrence2Scalar3Exceptional.coeff 58 =
      -((284034649221229124044668719361846481577878309 * 10 ^ 70 +
        3350185563448747393246477034989079343755477645579810868896678725250795) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_59 :
    recurrence2Scalar3Exceptional.coeff 59 =
      ((3995728028427471121938026235403500220411874879 * 10 ^ 70 +
        9388813423103861626358484770976178408907958437167286687100206162591593) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_60 :
    recurrence2Scalar3Exceptional.coeff 60 =
      -((53990040688159790523317379639798854490464723608 * 10 ^ 70 +
        9019311502765837376540022399413977081426340509050526370433658462001107) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_61 :
    recurrence2Scalar3Exceptional.coeff 61 =
      ((701167869500627533982704630568002751707235133148 * 10 ^ 70 +
        7797043529132170859563375086801958271125080253521695323294875907539556) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_62 :
    recurrence2Scalar3Exceptional.coeff 62 =
      -((8757261616050230874323769202331441119197206913164 * 10 ^ 70 +
        7668770696322432011120948281777569456072224403569376585098182550487069) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_63 :
    recurrence2Scalar3Exceptional.coeff 63 =
      ((105253001866272951857596891973897259714749733406411 * 10 ^ 70 +
        5455689885326807296190388416583774925580945007870276216286149734145619) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_64 :
    recurrence2Scalar3Exceptional.coeff 64 =
      -((1218301812486672012965562299064242175384261920533641 * 10 ^ 70 +
        1663871154355467601472749948730541554137267980526830423601803172379707) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_65 :
    recurrence2Scalar3Exceptional.coeff 65 =
      ((13591430957963634461999420112359855951983020264055351 * 10 ^ 70 +
        0605941098084248228562137308165585670256497566295462105027645908660256) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_66 :
    recurrence2Scalar3Exceptional.coeff 66 =
      -((146233349241563376785662306038196932087803714094789634 * 10 ^ 70 +
        6716817261518028544937514862839423239345517899338427956050790789747867) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_67 :
    recurrence2Scalar3Exceptional.coeff 67 =
      ((1518172358974766035568343918606267826971093541267233342 * 10 ^ 70 +
        1914782466406741378672097230096869207957192571844876335209180548161443) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_68 :
    recurrence2Scalar3Exceptional.coeff 68 =
      -((15215907591346969784669095801338981250852787842795872464 * 10 ^ 70 +
        0910668799902200287125298834299769651891996427906657664527423977424243) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_69 :
    recurrence2Scalar3Exceptional.coeff 69 =
      ((147304377514263396950415787525128362325948239390077157968 * 10 ^ 70 +
        8922758335059103965410606172396562677241954148499498527508041397195816) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_70 :
    recurrence2Scalar3Exceptional.coeff 70 =
      -((1378301291176088622829405840608952367374855022386238450595 * 10 ^ 70 +
        4280535942959036100945890142067437333887898458501787865536914211584946) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_71 :
    recurrence2Scalar3Exceptional.coeff 71 =
      ((12472287639187175385751248744125095372709362291938038702885 * 10 ^ 70 +
        7798976626536012659197421467876757326538604108588913468422682314881585) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_72 :
    recurrence2Scalar3Exceptional.coeff 72 =
      -((109205130932050816110223777607104489837451462094143399621759 * 10 ^ 70 +
        8392062758053472597098399391135270175499487593920372130112624336846671) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_73 :
    recurrence2Scalar3Exceptional.coeff 73 =
      ((925591773157692507657953561838060640066559334429112799622803 * 10 ^ 70 +
        5623568157682876984058294257725023841306365486309947529155025926012817) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_74 :
    recurrence2Scalar3Exceptional.coeff 74 =
      -((7597293928053430810413495655055320908438809481462288663038789 * 10 ^ 70 +
        1769803347274577769464105253924145360706633908810799180706930887825452) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_75 :
    recurrence2Scalar3Exceptional.coeff 75 =
      ((60418764344997076839973682324379080041492107690984537055849776 * 10 ^ 70 +
        7022324782976387603524070505000108109610238477187746732309154271325602) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_76 :
    recurrence2Scalar3Exceptional.coeff 76 =
      -((465784726825751744057457535379440887261746638638802635833236708 * 10 ^ 70 +
        5634622118114656950086891643137169679573430757477114101914562314144958) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_77 :
    recurrence2Scalar3Exceptional.coeff 77 =
      ((3482609769930001763965017495255034568848332215380143613637188059 * 10 ^ 70 +
        0225016788555030794106704717211060487315220677968059381853141475542488) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_78 :
    recurrence2Scalar3Exceptional.coeff 78 =
      -((25263404598414125157642168358765753705700529195544295527163043989 * 10 ^ 70 +
        9515052111930776987406240859589547968599958674527138981901437339688758) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_79 :
    recurrence2Scalar3Exceptional.coeff 79 =
      ((177862617894007227529947905062040198044624712482473279655262328696 * 10 ^ 70 +
        5674329235166124720153535578284283380206644805935149751480176676154564) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_80 :
    recurrence2Scalar3Exceptional.coeff 80 =
      -((1215753149783934506736127645181464055500452795114368981422483170733 * 10 ^ 70 +
        1738935086679627492688600556556608281223663694017687609204544132170632) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_81 :
    recurrence2Scalar3Exceptional.coeff 81 =
      ((8071992510653526489135039268499917253137874880272440231107727008526 * 10 ^ 70 +
        9859021561326427618502842664786407367379611696428174707535218204955482) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_82 :
    recurrence2Scalar3Exceptional.coeff 82 =
      -((52084052871981716631251552067665237343102510543598509822712860475321 * 10 ^ 70 +
        1686661593954318870786032856557064503162633274204100122122168015973554) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_83 :
    recurrence2Scalar3Exceptional.coeff 83 =
      ((326719501403155442926075118296505143200191839567914741873982902166220 * 10 ^ 70 +
        8330333248959269326670760627860333003484455136990516658365190400938245) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_84 :
    recurrence2Scalar3Exceptional.coeff 84 =
      -((1992850654088562997312821617493736444509028844371704841143402333468525 * 10 ^ 70 +
        4378953303920747532793773162704722197299763869917847371445463201595117) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_85 :
    recurrence2Scalar3Exceptional.coeff 85 =
      (((1 * 10 ^ 70 +
        1821651978930250581870199049117377951800667033397892134810635834097772) * 10 ^ 70 +
        2973137040712411410522771058380691751787467365048364118343047826160505) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_86 :
    recurrence2Scalar3Exceptional.coeff 86 =
      -(((6 * 10 ^ 70 +
        8225363688850475548113425726661537696896192182505574660065678273751272) * 10 ^ 70 +
        7019670421275960887693098562061191592079357574248654797491019690446421) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_87 :
    recurrence2Scalar3Exceptional.coeff 87 =
      (((38 * 10 ^ 70 +
        3299468289773170267717585933952443778699509667519455761277281462582781) * 10 ^ 70 +
        9802285439816082233878955715761139105141279864705489548487172329130134) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_88 :
    recurrence2Scalar3Exceptional.coeff 88 =
      -(((209 * 10 ^ 70 +
        7474565983201657924666419451773242297162152459780952970126309202631059) * 10 ^ 70 +
        3249571390025635689078896133735610942077824338314705341968842473139358) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_89 :
    recurrence2Scalar3Exceptional.coeff 89 =
      (((1118 * 10 ^ 70 +
        1282226605886601161980392745644396780013428483246180730452908046631411) * 10 ^ 70 +
        7294102024737217107703292323846339212818907555100967919696353548914411) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_90 :
    recurrence2Scalar3Exceptional.coeff 90 =
      -(((5805 * 10 ^ 70 +
        3084489304033437166947821012528073595835930057541018106983771140486879) * 10 ^ 70 +
        5152173469444112496056922578358922880447347815567374412092811386735406) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_91 :
    recurrence2Scalar3Exceptional.coeff 91 =
      (((29353 * 10 ^ 70 +
        8421595927195147995238802105386170488523160937067473740605572529119211) * 10 ^ 70 +
        8588439636949697686556019120574630514483234503686647140640581153782446) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_92 :
    recurrence2Scalar3Exceptional.coeff 92 =
      -(((144646 * 10 ^ 70 +
        5568672402597670871533023327866960023165455001612572608127015178918005) * 10 ^ 70 +
        1094515522005028693676708256969037437039499653147488235243592027391090) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_93 :
    recurrence2Scalar3Exceptional.coeff 93 =
      (((695549 * 10 ^ 70 +
        3813282066246939845448509384645387282581674907418241888166752351582892) * 10 ^ 70 +
        7519056655275245235687438168366200746600319291680362587775573948801170) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_94 :
    recurrence2Scalar3Exceptional.coeff 94 =
      -(((3266427 * 10 ^ 70 +
        9071684451984709116595583054420316011595826170719386757737742595149757) * 10 ^ 70 +
        3448266130265844068639022587250095191931943275088791236520949567547314) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_95 :
    recurrence2Scalar3Exceptional.coeff 95 =
      (((14967551 * 10 ^ 70 +
        6908322560753280140118537329125705572720546705461156362066624967226095) * 10 ^ 70 +
        2569115917035977467159880958380400245455268858855116528214098900893501) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_96 :
    recurrence2Scalar3Exceptional.coeff 96 =
      -(((66780109 * 10 ^ 70 +
        4728025458881838635254149248898316320879434719812552289424581526412971) * 10 ^ 70 +
        9147189895495986161343569284960124149089441139700774867886191680587889) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_97 :
    recurrence2Scalar3Exceptional.coeff 97 =
      (((289934567 * 10 ^ 70 +
        7582745544067677787764545936432918014374311203611650658303459316854190) * 10 ^ 70 +
        4236605188195136881662984137004762076036818967090234593911564713595957) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_98 :
    recurrence2Scalar3Exceptional.coeff 98 =
      -(((1229247829 * 10 ^ 70 +
        0965289134405841559059263687743960483135673512861359757971973435618000) * 10 ^ 70 +
        7960852389096814353181435281121840952773995230850453762882171102157091) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_99 :
    recurrence2Scalar3Exceptional.coeff 99 =
      (((5120682004 * 10 ^ 70 +
        5459078068972404618879161195126014671937202437853079342582371251687378) * 10 ^ 70 +
        6762399714834514946651933716909615369444056294088884190807193217010500) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_100 :
    recurrence2Scalar3Exceptional.coeff 100 =
      -(((20991185971 * 10 ^ 70 +
        6056671311399159052536271549031479380857573221283263201265270145948458) * 10 ^ 70 +
        2883077609243736470843015975055146698553945241790994395064735856428100) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_101 :
    recurrence2Scalar3Exceptional.coeff 101 =
      (((83875078810 * 10 ^ 70 +
        1557054825582130796710198117915863332844132416775634640460538821679355) * 10 ^ 70 +
        9103022811882996159254774669308398310801336444451362276769360889624575) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_102 :
    recurrence2Scalar3Exceptional.coeff 102 =
      -(((321607909929 * 10 ^ 70 +
        9022910047644901689725382224697475904143459828603293089856250917849614) * 10 ^ 70 +
        5667180167014886840992779958671695287232194652701558681202618031799247) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_103 :
    recurrence2Scalar3Exceptional.coeff 103 =
      (((1179772444235 * 10 ^ 70 +
        8176027726563181883944512929269781538640337152398212093608014147244040) * 10 ^ 70 +
        4918717443879253967791134660269590968751450104481542660559038383804630) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_104 :
    recurrence2Scalar3Exceptional.coeff 104 =
      -(((4266565833492 * 10 ^ 70 +
        1647270753925383279963230373443193227627029600310749644724790038992202) * 10 ^ 70 +
        6441391944990606690359573828125149619869071718302860740781832251131361) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_105 :
    recurrence2Scalar3Exceptional.coeff 105 =
      (((16012010120131 * 10 ^ 70 +
        5306293527254322797152009344794776622456049684945607695194515130000795) * 10 ^ 70 +
        9821988529224687649927303168985621756716324159661938142889853432523404) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_106 :
    recurrence2Scalar3Exceptional.coeff 106 =
      -(((62351698866016 * 10 ^ 70 +
        8321737146066225569912609050735175335684646635940448773611690518837300) * 10 ^ 70 +
        3137609797458529699433782273422353872788390640873918368884643688844923) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_107 :
    recurrence2Scalar3Exceptional.coeff 107 =
      (((228653255031579 * 10 ^ 70 +
        0543718343781384648086847550292420303198640723764994938444098859089543) * 10 ^ 70 +
        9124848499893088701115649033026063537701279019278667345080437774059097) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_108 :
    recurrence2Scalar3Exceptional.coeff 108 =
      -(((685308859000583 * 10 ^ 70 +
        0307450640105899350308280480010933316173573903633099428928132970202432) * 10 ^ 70 +
        2390833164224246412097779810459132676590418531677492185016959731616061) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_109 :
    recurrence2Scalar3Exceptional.coeff 109 =
      (((1488002401460645 * 10 ^ 70 +
        8928274948912042931992092300780390862892710133204641827682533952820642) * 10 ^ 70 +
        1659385384556821157335049498708943292638492181959774839993574520744126) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_110 :
    recurrence2Scalar3Exceptional.coeff 110 =
      -(((3221979366823777 * 10 ^ 70 +
        0774861729247538206619502360631796850974704796980299136038536438852338) * 10 ^ 70 +
        7204327909570610678747264146572242836252702878883273861128061593936337) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_111 :
    recurrence2Scalar3Exceptional.coeff 111 =
      (((22004758345123297 * 10 ^ 70 +
        1821763108509005359748919174312243208326777988252882381732514259263558) * 10 ^ 70 +
        6373780180074037390887826025138666016279702693755548660182217126854495) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_112 :
    recurrence2Scalar3Exceptional.coeff 112 =
      -(((166103867217829441 * 10 ^ 70 +
        5968408447169608068667319364249539677087693166725502751344919552342723) * 10 ^ 70 +
        1541524041682251080927759072429040724479991903468283524302083717228739) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_113 :
    recurrence2Scalar3Exceptional.coeff 113 =
      (((702073775581260807 * 10 ^ 70 +
        2302983700468238164373873683076432338450223712892660863239690160166837) * 10 ^ 70 +
        4564203144909640558933203548120289830403544081911968407917581786881882) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_114 :
    recurrence2Scalar3Exceptional.coeff 114 =
      -(((742049254251000548 * 10 ^ 70 +
        4041057961695365840437297620840018078230529747728113731697488436091283) * 10 ^ 70 +
        3207733172595844515000496104690791546724459800735827980041925314843155) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_115 :
    recurrence2Scalar3Exceptional.coeff 115 =
      -(((9061605157955450818 * 10 ^ 70 +
        4142612613985517445251384713257062384425140417040242266612346276139057) * 10 ^ 70 +
        1972892705898201870183505438002547728236188507288358404370487535320665) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_116 :
    recurrence2Scalar3Exceptional.coeff 116 =
      (((50563203700331396189 * 10 ^ 70 +
        4130996981005427802364432671395912939830852841008102751435156390142120) * 10 ^ 70 +
        0859217206008235850632866168239032133170879896289657109639224973123186) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_117 :
    recurrence2Scalar3Exceptional.coeff 117 =
      -(((13757982535345121488 * 10 ^ 70 +
        2125657493312580987308531082590162106737663883884819983464928094690801) * 10 ^ 70 +
        9292177734224150145477532666566414911288386007396127680301790154268630) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_118 :
    recurrence2Scalar3Exceptional.coeff 118 =
      -(((1123948647417905505143 * 10 ^ 70 +
        1407211231400848578842774234023927249599645433329618214029763056667164) * 10 ^ 70 +
        0171749038493907028758024752619022942562597540520597600579167882776547) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_119 :
    recurrence2Scalar3Exceptional.coeff 119 =
      (((5998566222117141887394 * 10 ^ 70 +
        5834441299722032046050968867754848082606967658194718501246750689771451) * 10 ^ 70 +
        3237973813133539389763237951708347286943135587687211103441797538809361) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_120 :
    recurrence2Scalar3Exceptional.coeff 120 =
      -(((6298396235182658872396 * 10 ^ 70 +
        9991303786488863156929787809665305125666302151277623473243110793015784) * 10 ^ 70 +
        8381930039814532364029730932761125437452720265298001037954294699127731) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_121 :
    recurrence2Scalar3Exceptional.coeff 121 =
      -(((90048669400091041884736 * 10 ^ 70 +
        7348833837513132999443793112160067536735928938036522802894323493397551) * 10 ^ 70 +
        6062020666798136333963340166590360790825139299968279998919023680325949) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_122 :
    recurrence2Scalar3Exceptional.coeff 122 =
      (((554722646270589451756694 * 10 ^ 70 +
        1250642381820689851930113561933333265591187596553816737901984809314824) * 10 ^ 70 +
        1182282429946373797244048036180353131928364547701097126662636583657341) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_123 :
    recurrence2Scalar3Exceptional.coeff 123 =
      -(((899184193361844459647096 * 10 ^ 70 +
        7176124217957379449246612604463918991839979981517289808934522271600012) * 10 ^ 70 +
        6616965213998173024775630282941020062984257037446884942728055841253812) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_124 :
    recurrence2Scalar3Exceptional.coeff 124 =
      -(((6280620814598533879340717 * 10 ^ 70 +
        2950779131350970551927957515471485927351252154260943099334650253212620) * 10 ^ 70 +
        6016659540504616266638111460323902988703029823557647074040768277671530) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_125 :
    recurrence2Scalar3Exceptional.coeff 125 =
      (((46708563345012329410635182 * 10 ^ 70 +
        5689631183010215327059425891620293990250400896784015238972616051028819) * 10 ^ 70 +
        9439883409117527727269938547911166445536427947050706291942094576151468) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_126 :
    recurrence2Scalar3Exceptional.coeff 126 =
      -(((107297913832289120329406208 * 10 ^ 70 +
        8738576916411363796162603311535624894039129881688536541596834947135617) * 10 ^ 70 +
        5219836490737215897085456733891125169925859855814630992212321320452072) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_127 :
    recurrence2Scalar3Exceptional.coeff 127 =
      -(((327019233112626401087849832 * 10 ^ 70 +
        2284376615482725604270700103129857391744284769994326299749395416088159) * 10 ^ 70 +
        8490527569839927568986296336292962497688848012325014169557455766268869) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_128 :
    recurrence2Scalar3Exceptional.coeff 128 =
      (((3430040180194186714164571088 * 10 ^ 70 +
        3973577601131601528578175949471389673826571780705407034061077881986587) * 10 ^ 70 +
        0463461948145584135783000385914788480700636080821978569532316922368947) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_129 :
    recurrence2Scalar3Exceptional.coeff 129 =
      -(((10590457117396700324134423827 * 10 ^ 70 +
        8881906226175002406672488717817079605411428052894658151276792242453099) * 10 ^ 70 +
        2588884452403026405568786159257865655858269780438380549499679690935709) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_130 :
    recurrence2Scalar3Exceptional.coeff 130 =
      -(((7827781078235261313953152831 * 10 ^ 70 +
        3465782068314953490466894930479586610732491577976359437917786624686169) * 10 ^ 70 +
        5453062087837200240057175615034195151773582810239761993654706313005956) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_131 :
    recurrence2Scalar3Exceptional.coeff 131 =
      (((212072253290130063830388239170 * 10 ^ 70 +
        7324583502963332533305515666241890478576083494754595433612031976407155) * 10 ^ 70 +
        3057623356016314278042246127581391285463550903510933414623857678061616) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_132 :
    recurrence2Scalar3Exceptional.coeff 132 =
      -(((873844727435913278277184352189 * 10 ^ 70 +
        5007984552436737194636802933386758750153855396062098968141717557168842) * 10 ^ 70 +
        8136463269072131608029570266605548148019188840194839108538654195759950) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_133 :
    recurrence2Scalar3Exceptional.coeff 133 =
      (((755366361241576272819643674140 * 10 ^ 70 +
        3588718968583113239947423695805746636278366321236110890717668565436476) * 10 ^ 70 +
        6872390488753530260539162428937015587638876897597656529895944776035864) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_134 :
    recurrence2Scalar3Exceptional.coeff 134 =
      (((10007608568127125826673589974494 * 10 ^ 70 +
        5146383396079038048222090460192526575980754321368477224748649061319396) * 10 ^ 70 +
        2629529126728058118712661373585703832348734900974114069314131008791310) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_135 :
    recurrence2Scalar3Exceptional.coeff 135 =
      -(((58465779619643999263277605631433 * 10 ^ 70 +
        4059711903248179774503351539712403966046664187403521318318319773117785) * 10 ^ 70 +
        9660291769942251849413632200040315610987219025625724481124941178756965) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_136 :
    recurrence2Scalar3Exceptional.coeff 136 =
      (((125185882708053019461713525697006 * 10 ^ 70 +
        9339350869649557355701593763227566867306094132134741837759541695610867) * 10 ^ 70 +
        4870154111797358844742692611707414594963667972184007451711311929166939) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_137 :
    recurrence2Scalar3Exceptional.coeff 137 =
      (((265436420516159156480190636029304 * 10 ^ 70 +
        9904089165882402968274116090174561064707097049142171462312024229557171) * 10 ^ 70 +
        8341973724493938535132356505166785376076470530341189492814349446482881) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_138 :
    recurrence2Scalar3Exceptional.coeff 138 =
      -(((3020826482895906493225763888782318 * 10 ^ 70 +
        2639602625949713259388528154075978605640573985316269386262121643280820) * 10 ^ 70 +
        2140992439457450102720744874993839477270305491008721037318702381747216) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_139 :
    recurrence2Scalar3Exceptional.coeff 139 =
      (((10349165252330879769410000599645211 * 10 ^ 70 +
        3212886943589099707066386155332706148055611835387075896792773163813455) * 10 ^ 70 +
        6432350533262091740956727374383690510156285133428295367224952252580995) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_140 :
    recurrence2Scalar3Exceptional.coeff 140 =
      -(((6740618291177080939702323173357155 * 10 ^ 70 +
        7880516811176884459679881501528470132168642466144393723657150201844490) * 10 ^ 70 +
        1222937139809381765873813618752674040030634713496487341369401249702808) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_141 :
    recurrence2Scalar3Exceptional.coeff 141 =
      -(((107486975485121929794655183001855838 * 10 ^ 70 +
        2108731156333379816562490769140351170969390141628577536892987319303116) * 10 ^ 70 +
        8433424386518572193454842278280518975288020998320510078780554600825503) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_142 :
    recurrence2Scalar3Exceptional.coeff 142 =
      (((586078909268136554669535573353372959 * 10 ^ 70 +
        0592910481420022279044211197018982251054280849656709685804367761943917) * 10 ^ 70 +
        2418700429983774736217863041100020634008131912468092202601540193569619) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_143 :
    recurrence2Scalar3Exceptional.coeff 143 =
      -(((1324229719040057609658747235108250379 * 10 ^ 70 +
        9804525929658485147992471784561881987321333385166035587223649296629163) * 10 ^ 70 +
        6211654206074832011947425686758628637376317709829148891111758998174417) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_144 :
    recurrence2Scalar3Exceptional.coeff 144 =
      -(((1288819258415144261884901125727678371 * 10 ^ 70 +
        7588538641580171239635349738030934401591073769872446049530550059170226) * 10 ^ 70 +
        3103731834076818987736759720838535119993325980396710936216673877217079) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_145 :
    recurrence2Scalar3Exceptional.coeff 145 =
      (((22339905399681692635245373870309841108 * 10 ^ 70 +
        4100915017796119339749027873148585014474612137146519398543947774000238) * 10 ^ 70 +
        1190030006424591112601339500464109871031119712295197315108052952029090) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_146 :
    recurrence2Scalar3Exceptional.coeff 146 =
      -(((87281409667568046856653626185161872864 * 10 ^ 70 +
        7735950684078260893310807129463258815832789825609523873898430779704816) * 10 ^ 70 +
        8445791454289524829556013025016469438615870531461642877833107711948396) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_147 :
    recurrence2Scalar3Exceptional.coeff 147 =
      (((136091160865079514701016960036969235039 * 10 ^ 70 +
        4613861812663183506840696873680059491618686867941309252994373050582511) * 10 ^ 70 +
        5001322184941098847569586425320542952128083267166580122612254271459405) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_148 :
    recurrence2Scalar3Exceptional.coeff 148 =
      (((390289666162071908125143834746231404710 * 10 ^ 70 +
        9667932570583985688076880920633544318475247625631778321494849553910461) * 10 ^ 70 +
        6013049114242637259764013654638244978310654622644531205533206282933374) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_149 :
    recurrence2Scalar3Exceptional.coeff 149 =
      -(((3337625698722423775096021045340072806290 * 10 ^ 70 +
        3383509124681292363797647135804174703544152757253863767365016945082600) * 10 ^ 70 +
        6481332080764228207978050674862654107283506378317934337830422967936483) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_150 :
    recurrence2Scalar3Exceptional.coeff 150 =
      (((10906053668101734585453149555331629466530 * 10 ^ 70 +
        7438589704409095041210710470834504567684427267797168102337431505581512) * 10 ^ 70 +
        1112234268513323460612748918639291040879592462881637414280679263827536) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_151 :
    recurrence2Scalar3Exceptional.coeff 151 =
      -(((13301044548103202564873386050413592197040 * 10 ^ 70 +
        9217389821070538922260237466570449767504093843371295381277779252695491) * 10 ^ 70 +
        8693458411003664573292312975359789622085674651379989384323909285894514) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_152 :
    recurrence2Scalar3Exceptional.coeff 152 =
      -(((56142196301169651283838236914891238700427 * 10 ^ 70 +
        3131477772558864586826537770384669454697536613708123076419364413909714) * 10 ^ 70 +
        5956194388036834243000475365252100398695352939521415693965602736127579) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_153 :
    recurrence2Scalar3Exceptional.coeff 153 =
      (((394736095892143848878193903641476838018359 * 10 ^ 70 +
        9731455420454936259314524969568492589531753425055124469736336781214480) * 10 ^ 70 +
        2892668900704665931578157928424835009442960528289389392368629986026157) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_154 :
    recurrence2Scalar3Exceptional.coeff 154 =
      -(((1215161851335629625753188893630233895565298 * 10 ^ 70 +
        1829539860101475085856323803197562077684954257357216973211490665858265) * 10 ^ 70 +
        6995890206147780608042513040766859675188563655489486763304845113430466) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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

theorem recurrence2Scalar3Exceptional_coeff_155 :
    recurrence2Scalar3Exceptional.coeff 155 =
      (((1535799896921156096716819765403544408759558 * 10 ^ 70 +
        1162232015830514989929573022137762593789857237132054316595976254026841) * 10 ^ 70 +
        8117364106502377766765417579162602984535168220822274144843780350259912) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_156 :
    recurrence2Scalar3Exceptional.coeff 156 =
      (((5020273662757718212096429127678748002331407 * 10 ^ 70 +
        7149037615559387114797805560728782808035613818087601147818894095296628) * 10 ^ 70 +
        0842802930053175666132890548469995507361266461081569648974142746621432) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_157 :
    recurrence2Scalar3Exceptional.coeff 157 =
      -(((37458948820033618888917781769912043488663911 * 10 ^ 70 +
        7492689418057683849332015353001277467349191661002053143238601537543633) * 10 ^ 70 +
        1562332465957945070414438635543447329845330693572377952086017930251488) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_158 :
    recurrence2Scalar3Exceptional.coeff 158 =
      (((121318638972008267398406939923528433283778626 * 10 ^ 70 +
        9346170828026674747688110278399032316743358165574845097729967613673369) * 10 ^ 70 +
        6939571310104402804905336374418596214860552422473939343281642740243176) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_159 :
    recurrence2Scalar3Exceptional.coeff 159 =
      -(((199244320468975969115581989145926692888938285 * 10 ^ 70 +
        3097459056953181484586658315573693870738856249229369575729033739669129) * 10 ^ 70 +
        2049263030026131483598003172121176457613216988229586905436764423011543) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_160 :
    recurrence2Scalar3Exceptional.coeff 160 =
      -(((202836935821772713089161767568643814125260208 * 10 ^ 70 +
        7179985818879197422644123508396266199771957079141091642331131652560172) * 10 ^ 70 +
        4677052415710522791529131164657336195716521299844378517100698286152646) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_161 :
    recurrence2Scalar3Exceptional.coeff 161 =
      (((2667860707621938719523116861133847057941151828 * 10 ^ 70 +
        5783130183528571797096371669416677250438391779741646845891869919719784) * 10 ^ 70 +
        6513310361930431758563911457180140581865870900306540254107787756165363) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_162 :
    recurrence2Scalar3Exceptional.coeff 162 =
      -(((10146314541084049589700954179083483276642659565 * 10 ^ 70 +
        4732660249813723238486304189794008657385210439816179679408839671173067) * 10 ^ 70 +
        6094844269369326802904862828273035611871676938022993736330817777041117) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_163 :
    recurrence2Scalar3Exceptional.coeff 163 =
      (((22586027962198533022758062207309605075550401902 * 10 ^ 70 +
        7028474223596737232194490375666175020633905067281069663352390383276778) * 10 ^ 70 +
        5506473208576847970841945378193445023199063282561123103109908895668489) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_164 :
    recurrence2Scalar3Exceptional.coeff 164 =
      -(((16353414018697809966668130285433723880534301073 * 10 ^ 70 +
        5728464633174421659910181733490824520236043932777356568137378395198423) * 10 ^ 70 +
        6767874051745735099565161272573519475904580737938400197327743399317635) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_165 :
    recurrence2Scalar3Exceptional.coeff 165 =
      -(((110066805459163397930326393928768621741983479844 * 10 ^ 70 +
        1311276988346748791128157024394556344265081664562833812538110726712605) * 10 ^ 70 +
        2372031903775437412052098740554303930963733833116858400800578214752539) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_166 :
    recurrence2Scalar3Exceptional.coeff 166 =
      (((614346061059074973170459941123445679755298635797 * 10 ^ 70 +
        7551373095973033209626614279386120480285241666312500392381326740402565) * 10 ^ 70 +
        8822795439430839211433253354701637862499008206458183286403924474207105) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_167 :
    recurrence2Scalar3Exceptional.coeff 167 =
      -(((1851738354463883321820860284677958024592746846362 * 10 ^ 70 +
        5490954752783674885106920263851045213330534883682702312444235530095541) * 10 ^ 70 +
        1951123118148615867127607801649217685803911460302737256005608807778238) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_168 :
    recurrence2Scalar3Exceptional.coeff 168 =
      (((3487668584451909712574996273795168292602458774077 * 10 ^ 70 +
        0288465068991649430844313900237838572334335971497208322453737464761461) * 10 ^ 70 +
        5394246504617762025562590000949696136113825363695573451426421313831045) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_169 :
    recurrence2Scalar3Exceptional.coeff 169 =
      -(((1622685165718454702304235665048833157334266365142 * 10 ^ 70 +
        9553228836029302763126770130163702592621349347089901576162863565652537) * 10 ^ 70 +
        8634884686412782078611767482740314667587100699071069464020306140436187) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_170 :
    recurrence2Scalar3Exceptional.coeff 170 =
      -(((17919487584691976251922982972045908905956342755450 * 10 ^ 70 +
        7795951406845268903094000898204112419998384846947922062204526929434729) * 10 ^ 70 +
        8904550826457233844590978633039098521665686684591641334445409300367516) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_171 :
    recurrence2Scalar3Exceptional.coeff 171 =
      (((88847134672125999820967319938512512883822288748565 * 10 ^ 70 +
        1757373364938937568169844775213147338562177940588501160071828596566604) * 10 ^ 70 +
        0689724722693466287204047411332948530533388287247797768341085088593853) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_172 :
    recurrence2Scalar3Exceptional.coeff 172 =
      -(((260722994866523147480923753370752822998156518860307 * 10 ^ 70 +
        7402365046728561672374784317923915016358188331905982472063545899391179) * 10 ^ 70 +
        6420575362505039009180225226430214353414123799290555212067505666414795) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_173 :
    recurrence2Scalar3Exceptional.coeff 173 =
      (((528801820795431791183080892305914830215441386479409 * 10 ^ 70 +
        0096005891092715950849897257127667114274238800853085198496344234169841) * 10 ^ 70 +
        4416848332929655175269291282536482380529063487846948892270423440204666) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_174 :
    recurrence2Scalar3Exceptional.coeff 174 =
      -(((573815729533203281512469094542583651873626729199322 * 10 ^ 70 +
        9686426272638253893874708164361440763709108562279253932499216804020324) * 10 ^ 70 +
        9004800754091875840005330928537751093165747764864632326019155213756083) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_175 :
    recurrence2Scalar3Exceptional.coeff 175 =
      -(((880773829345662113112377822751718554601654459802124 * 10 ^ 70 +
        3465970037706933464083376667530927957635425007529980982236633774719280) * 10 ^ 70 +
        2081494654195731185360114016179619506028476794315259093819894249741783) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_176 :
    recurrence2Scalar3Exceptional.coeff 176 =
      (((7196999918590494547174004086476424673215134408474614 * 10 ^ 70 +
        3869610978500934663529937466866019770744543697959172970952239710863004) * 10 ^ 70 +
        9894473942416628070991170481255982374694517144366332781230760826150566) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_177 :
    recurrence2Scalar3Exceptional.coeff 177 =
      -(((24878940668600165744077723368319086279647016582680624 * 10 ^ 70 +
        0127209871413662893685305340586456418658173175758860837283397975774337) * 10 ^ 70 +
        6942485306231824650905920755764192221118505546676963937970057036684819) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_178 :
    recurrence2Scalar3Exceptional.coeff 178 =
      (((62000461475457865459364728575184543627117941968928044 * 10 ^ 70 +
        1320266908074439091277821458167170762534276732362340706181321580358950) * 10 ^ 70 +
        1730475825870076451627254869143146658531283365109582243301499806581401) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_179 :
    recurrence2Scalar3Exceptional.coeff 179 =
      -(((117139592419128537281811910429535657005274069167316293 * 10 ^ 70 +
        5901147428294716473701452546936124600633857540918733901602857960301457) * 10 ^ 70 +
        0326719947111487210493179915764889200717249128328169241583504429709611) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_180 :
    recurrence2Scalar3Exceptional.coeff 180 =
      (((145041648296022743763519327882542436996858289286691702 * 10 ^ 70 +
        7554787291395834447956343273519602937402359564613240271698238159693135) * 10 ^ 70 +
        8450124105246430244033550958427331521633167816218082916477463523984732) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_181 :
    recurrence2Scalar3Exceptional.coeff 181 =
      (((21791631821121732811499945165328453544323772918546876 * 10 ^ 70 +
        1756561304503461669021514548229479635182164193350923614717150968766570) * 10 ^ 70 +
        4235094673612960855514193516720970363901742731729399913484459549134738) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Exceptional_coeff_182 :
    recurrence2Scalar3Exceptional.coeff 182 =
      -(((814688627492802010540678121230836484920308986077851441 * 10 ^ 70 +
        2443182723941707728541493269123431861744856793065661980428673009875311) * 10 ^ 70 +
        1185115985538105168474144608176061566853274868546296187787517057496559) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
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
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_183 :
    recurrence2Scalar3Exceptional.coeff 183 =
      (((3123278390651112475236464383171354943242300699356423755 * 10 ^ 70 +
        9676534996767089890476864402575289112210767429141988625485819162349273) * 10 ^ 70 +
        9333943664794089181695260821118863388821100266933102497375731980974595) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_184 :
    recurrence2Scalar3Exceptional.coeff 184 =
      -(((8446144481471109994937101740796438806872330130678815133 * 10 ^ 70 +
        8150318311524293245818288945260732118002077498562913088950634933312895) * 10 ^ 70 +
        9222825583947541031930606723536337527398855265076877890507497246343196) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 2 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_185 :
    recurrence2Scalar3Exceptional.coeff 185 =
      (((18728132947115285390089378017355263653693068935481205813 * 10 ^ 70 +
        6709539806684871967099217046556268965093022446633872751569184352993290) * 10 ^ 70 +
        7783435299050633084087127300562718752151008537160283656504043136859657) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 3 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_186 :
    recurrence2Scalar3Exceptional.coeff 186 =
      -(((35354995502494037216846904897994098202947117139233644854 * 10 ^ 70 +
        0361926800468311259025052716944897601066588539581963525595198055497768) * 10 ^ 70 +
        9917078528522496300482091250653741426106935897770167680186932055508009) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 4 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_187 :
    recurrence2Scalar3Exceptional.coeff 187 =
      (((56508292123861458159739666485552810187101466148259392663 * 10 ^ 70 +
        5751062448729705811372276537206784088828882355999703449941557677777973) * 10 ^ 70 +
        9734509167019097369541093970453799725985208340028331478783565896377337) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 5 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_188 :
    recurrence2Scalar3Exceptional.coeff 188 =
      -(((72025867391285502942987050221425726630974738818311620647 * 10 ^ 70 +
        9133975878556107683738177795141667734526730263356357050502919613811836) * 10 ^ 70 +
        9587727411414793411096693574517977729329955700478428546484777802577542) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 6 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_189 :
    recurrence2Scalar3Exceptional.coeff 189 =
      (((55451801210085077846796220899195539842012066446095431638 * 10 ^ 70 +
        6091519729944246526359636391082051992211973384961665644564697701223080) * 10 ^ 70 +
        2350614828600288061629717975284404074538900805900330655476957780166526) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 7 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_190 :
    recurrence2Scalar3Exceptional.coeff 190 =
      (((45420753326614391401823423809649338271858452166628403772 * 10 ^ 70 +
        6679086734912351799959862149681221711000321333714601883247440778919396) * 10 ^ 70 +
        2179134254449055845246312389355168752660933788063022506363455495554154) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 8 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_191 :
    recurrence2Scalar3Exceptional.coeff 191 =
      -(((315165588283771636561250803543232088456836407120921448245 * 10 ^ 70 +
        3031177304479744066425074157960357964823203671867451188676128999841745) * 10 ^ 70 +
        5339638014964343077487225292920790798883363103226731054938048162598063) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 9 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_192 :
    recurrence2Scalar3Exceptional.coeff 192 =
      (((865905139588887024447659938093115531690309886147271195680 * 10 ^ 70 +
        8180467614479308745286692303187295790507503252584986317964536857562466) * 10 ^ 70 +
        7914238481410142865189897179419702992160475966818439614323326535879710) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 10 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_193 :
    recurrence2Scalar3Exceptional.coeff 193 =
      -(((1808327789752621657483032119438153674796110677435762682687 * 10 ^ 70 +
        3792190049958167463042120056254235186592531498295816753306531021205927) * 10 ^ 70 +
        4345931239476313821182163231226608156399264476600529196704829871879617) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 11 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_194 :
    recurrence2Scalar3Exceptional.coeff 194 =
      (((3184482460155083941476145689845555728760907486205535667200 * 10 ^ 70 +
        8586683272540561746666429030273770651834479812735214969816765588063388) * 10 ^ 70 +
        3876673829446702578480631470570507897908926890317263449754368685198146) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 12 +
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (195 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_195 :
    recurrence2Scalar3Exceptional.coeff 195 =
      -(((4853540504044308223548486697949603539001407047583591315992 * 10 ^ 70 +
        8958226757840216149835086600320594118041651256170735448732497847817076) * 10 ^ 70 +
        3628717260477492590093256038203889233143047854373919928866910508152948) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 13 +
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
    rw [show 23 = 21 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (196 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_196 :
    recurrence2Scalar3Exceptional.coeff 196 =
      (((6337024452220498094575580956224891392528765612090663747322 * 10 ^ 70 +
        8484200824108089548224788205398907287553166398101006027906782607547022) * 10 ^ 70 +
        4070047126394900784801375832006817241653021906065417828224529888165619) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 14 +
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
    rw [show 23 = 20 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (197 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_197 :
    recurrence2Scalar3Exceptional.coeff 197 =
      -(((6656175820214390206585207140217812568424732790801875762068 * 10 ^ 70 +
        4796593799036198601825939115197353983577131013589794865983635102552003) * 10 ^ 70 +
        6053338427659644766185676052137137071385764723184541404366316919089967) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 15 +
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
    rw [show 23 = 19 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (198 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_198 :
    recurrence2Scalar3Exceptional.coeff 198 =
      (((4226517498204184773286426092805374117130989650784551366370 * 10 ^ 70 +
        3887294321606854677385982930732087616879310778462401290114439380442357) * 10 ^ 70 +
        9452726598197167697113901804129671432774419261053914690370686093108151) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 16 +
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
    rw [show 23 = 18 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (199 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_199 :
    recurrence2Scalar3Exceptional.coeff 199 =
      (((3098515787395011543131308434030150593732746959089345628918 * 10 ^ 70 +
        0705118789291052840444032188268946898611870222551243428440551333551631) * 10 ^ 70 +
        8432148408662313786180314810876666243601308968048192589596182848081961) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 17 +
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
    rw [show 23 = 17 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (200 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_200 :
    recurrence2Scalar3Exceptional.coeff 200 =
      -(((17739344263302481876101992579904989603105428945923440367693 * 10 ^ 70 +
        3452629089549792869222739479166755955842530091233396051868023794743344) * 10 ^ 70 +
        7974252070141015736840054817252087446866993775557920492318761829417599) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 18 +
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
    rw [show 23 = 16 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (201 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_201 :
    recurrence2Scalar3Exceptional.coeff 201 =
      (((41799180150505857147452316550132217017693035460584069275329 * 10 ^ 70 +
        2069562984132180387694397480749309877586589165387857659853970980094602) * 10 ^ 70 +
        5422835084869697304749114855763048389125286028856663735803259472539099) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 19 +
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
    rw [show 23 = 15 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (202 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_202 :
    recurrence2Scalar3Exceptional.coeff 202 =
      -(((76198830639460294363353376700091525071519301557087986851141 * 10 ^ 70 +
        9401246609497558554742233123486959055670453299004424642590168937001156) * 10 ^ 70 +
        8556822322022288670884026679739340987562644154454216929378430157817699) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 20 +
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
    rw [show 23 = 14 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (203 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_203 :
    recurrence2Scalar3Exceptional.coeff 203 =
      (((119692024854759281429646037532373745936764929335893532079843 * 10 ^ 70 +
        1393651455359890346471926334237031172190088340042368734479519017809743) * 10 ^ 70 +
        4898248050013241025127823524395321187518027665613430882263780599274143) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 21 +
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
    rw [show 23 = 13 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (204 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_204 :
    recurrence2Scalar3Exceptional.coeff 204 =
      -(((168045747222649796386028001975470199540783952382542006060336 * 10 ^ 70 +
        8732888445117408144082930173331627868084965606200830054341376402912917) * 10 ^ 70 +
        9266693208385568045947185472179385090751011319482586315056104209974628) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 22 +
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
  rw [recurrence2Scalar3Exceptional_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (205 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_205 :
    recurrence2Scalar3Exceptional.coeff 205 =
      (((213748758183979505456574652784459982395284501789477027077389 * 10 ^ 70 +
        3922489874628473342443604736517394073933460391297288718793273912322122) * 10 ^ 70 +
        2630308201563569420936470613501058952008332372155529843367055437228430) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 23 +
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
    rw [show 23 = 11 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (206 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_206 :
    recurrence2Scalar3Exceptional.coeff 206 =
      -(((246581637234929928263764004163010253894443779081160352770954 * 10 ^ 70 +
        7727472885924093650717083297011262472080253270921433090415614008989140) * 10 ^ 70 +
        0458920377102168824266686779941246685260168606462279643624451573142127) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 24 +
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
    rw [show 23 = 10 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (207 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_207 :
    recurrence2Scalar3Exceptional.coeff 207 =
      (((255209842571688976273715062567353211541475032533927666027955 * 10 ^ 70 +
        2824532316545625910832721209079629193479943614132286037771044375757497) * 10 ^ 70 +
        9799026258514228433572869137096854631216048066046037145864771257609923) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 25 +
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
    rw [show 23 = 9 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (208 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_208 :
    recurrence2Scalar3Exceptional.coeff 208 =
      -(((229663286235698364425887167889585690132983319672182946889104 * 10 ^ 70 +
        3451228043951142429607018469674428335051053005643710285199341091775361) * 10 ^ 70 +
        4833008124019630989441076916659758568183562348062080005034575986708133) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 26 +
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
    rw [show 23 = 8 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (209 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_209 :
    recurrence2Scalar3Exceptional.coeff 209 =
      (((164217655687470098066083054292299285999831194146026567076833 * 10 ^ 70 +
        2486409326936162542556284685041407077464059808695232872202271101292860) * 10 ^ 70 +
        7334339958813011390833027264466482350940173841825748097705635196721545) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 27 +
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
    rw [show 23 = 7 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (210 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_210 :
    recurrence2Scalar3Exceptional.coeff 210 =
      -(((59915715959615373757097909636540895497385984363683489569841 * 10 ^ 70 +
        7513317037547417884419414968262921845547900286351097828815966743192809) * 10 ^ 70 +
        8922421418972755946135473854508417040462696459317172494070386066566288) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 28 +
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
    rw [show 23 = 6 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (211 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_211 :
    recurrence2Scalar3Exceptional.coeff 211 =
      -(((74112008914907090092709216540216185910388359994494396488283 * 10 ^ 70 +
        8327198796751904506182608203593455869012432779172305266237714935432953) * 10 ^ 70 +
        6822027112170303520355411552837082317022385252764824439273890618920764) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 29 +
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
    rw [show 23 = 5 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (212 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_212 :
    recurrence2Scalar3Exceptional.coeff 212 =
      (((221170089156471697686008246075442844791371516043688415458212 * 10 ^ 70 +
        7539379106391733563308706540877817820458798011011152059415421612538860) * 10 ^ 70 +
        4368086375325264589592453450646688532480466368534235842651427137014932) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 30 +
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
    rw [show 23 = 4 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (213 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_213 :
    recurrence2Scalar3Exceptional.coeff 213 =
      -(((359548333123157843562308555239134167377277018434188247579329 * 10 ^ 70 +
        5368265899509507793097757637676266029070764447907229991869518469638305) * 10 ^ 70 +
        0726570332295603923794245067621032673677664501791452220481895686096305) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 31 +
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
    rw [show 23 = 3 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (214 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_214 :
    recurrence2Scalar3Exceptional.coeff 214 =
      (((466683383181800184326333316592854885492470644361518073466700 * 10 ^ 70 +
        7360447318855835943238797887038893904545862534201584676364030617637189) * 10 ^ 70 +
        6808677795243535716619078025817896990189940068171094826687359759094038) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 32 +
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
    rw [show 23 = 2 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (215 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_215 :
    recurrence2Scalar3Exceptional.coeff 215 =
      -(((523971004995992399095604694131774817366843956324396262990771 * 10 ^ 70 +
        2175876860762876011103745232823658616202452845515692963869895908677409) * 10 ^ 70 +
        5278557839756443779721868708060458619744287482028855814097498266548704) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 33 +
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
    rw [show 23 = 1 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (216 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_216 :
    recurrence2Scalar3Exceptional.coeff 216 =
      (((520978204666960227937185631597102060486794165222277165150493 * 10 ^ 70 +
        5586954872955775148029387805909312386129398776580696526679003287297294) * 10 ^ 70 +
        8441495847291570807709001987139660215275333658448606504768768854780854) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 34 +
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
  rw [recurrence2Scalar3Exceptional_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (217 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_217 :
    recurrence2Scalar3Exceptional.coeff 217 =
      -(((457894210175147712265618382312858423374955610751812115233748 * 10 ^ 70 +
        1974936612080649337179961181104826656425266562848365052150935093324728) * 10 ^ 70 +
        6500449097187963991014773565084989184443641781498944988787863552044714) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 35 +
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
    rw [show 55 = 31 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (218 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_218 :
    recurrence2Scalar3Exceptional.coeff 218 =
      (((345523216019557139403095342036612031931585675196323843548433 * 10 ^ 70 +
        1568033860375670877534219648422673815795796215114671328385928564865445) * 10 ^ 70 +
        6824421205680851435251391924390197437358380890646338736089916725576699) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 36 +
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
    rw [show 55 = 30 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (219 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_219 :
    recurrence2Scalar3Exceptional.coeff 219 =
      -(((202816543663389117619187974434832947541942017936930924992252 * 10 ^ 70 +
        1578511847167037353412234283268423255658992676699088150170281519028358) * 10 ^ 70 +
        9448455387775530453738697859994051822587824383495599195455422800999446) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 37 +
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
    rw [show 55 = 29 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (220 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_220 :
    recurrence2Scalar3Exceptional.coeff 220 =
      (((52637671670336499603086911308574198317421195066237373244741 * 10 ^ 70 +
        7404315534651701270304804458317835784298268989358434379534331301899471) * 10 ^ 70 +
        5342815168666230239585800165424363309182942798961546822011514721820955) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 38 +
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
    rw [show 55 = 28 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (221 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_221 :
    recurrence2Scalar3Exceptional.coeff 221 =
      (((83079610923425619958498849137266477135154513290100541866637 * 10 ^ 70 +
        8352572530674401455927142130187965184066424269547422401160326491062077) * 10 ^ 70 +
        4136576058828984786680961807001403106313307690856484170948177119032861) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 39 +
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
  rw [recurrence2Scalar3Exceptional_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (222 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_222 :
    recurrence2Scalar3Exceptional.coeff 222 =
      -(((187525638151693752737066411887817267743576107635879043032389 * 10 ^ 70 +
        0480133808508785209386260580298480867834919337425798392773236058796222) * 10 ^ 70 +
        0431565686142681541017104937549218799485998923416645632707573333401555) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 40 +
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
    rw [show 55 = 26 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (223 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_223 :
    recurrence2Scalar3Exceptional.coeff 223 =
      (((251593644523806699083824908075098917012868786300158552961222 * 10 ^ 70 +
        5488659697592386241186479366851833004323951099984288607807969341324774) * 10 ^ 70 +
        2202303629649977789280771313367139841120748533394161418633532661198332) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 41 +
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
    rw [show 55 = 25 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (224 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_224 :
    recurrence2Scalar3Exceptional.coeff 224 =
      -(((274417252416547657588583026521429788000231978544343519787245 * 10 ^ 70 +
        8863739313339972533662935404580690345015909480444495729506430572416619) * 10 ^ 70 +
        6560531845267719335366977959521617732529043164775757467451827476233802) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 42 +
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
    rw [show 55 = 24 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (225 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_225 :
    recurrence2Scalar3Exceptional.coeff 225 =
      (((262041563359073820627922855995159685922976658469641906122366 * 10 ^ 70 +
        7618216992499928539236993072406853081136312116435505465282363201495019) * 10 ^ 70 +
        8626289128621339084529105489562295915816248107949028510611530766241332) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 43 +
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
  rw [recurrence2Scalar3Exceptional_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (226 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_226 :
    recurrence2Scalar3Exceptional.coeff 226 =
      -(((224866591482521728419009149609052460702954941718979441731492 * 10 ^ 70 +
        3512156370867284466733640753798651136449237677301169476761494896148280) * 10 ^ 70 +
        4276656843277165879097017242088321217041243223538991631476309136469968) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 44 +
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
    rw [show 55 = 22 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (227 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_227 :
    recurrence2Scalar3Exceptional.coeff 227 =
      (((174706870481393565243174417628596333079862373807557337270140 * 10 ^ 70 +
        1758157812551011995651136890081194903068837604526763120117753349469333) * 10 ^ 70 +
        8651738313908036914931955802650087230752246353017226337544734975929911) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 45 +
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
    rw [show 55 = 21 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (228 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_228 :
    recurrence2Scalar3Exceptional.coeff 228 =
      -(((122239908774802774839680859046823942865002692116544799744582 * 10 ^ 70 +
        7573663118926790893891944146011956672315784846496097752642686838316537) * 10 ^ 70 +
        7822555196847609276613142932894169500187920367075046786721461556619628) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 46 +
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
    rw [show 55 = 20 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (229 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_229 :
    recurrence2Scalar3Exceptional.coeff 229 =
      (((75344170560495310454362332011174240894247793969509521885077 * 10 ^ 70 +
        5790217610632971683413037739521023967062178328226473047956193872077652) * 10 ^ 70 +
        2612054774671161321210824130371685844276051080359771169286864723755408) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 47 +
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
  rw [recurrence2Scalar3Exceptional_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (230 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_230 :
    recurrence2Scalar3Exceptional.coeff 230 =
      -(((38479156045962330790302298562844005376065001943684022781914 * 10 ^ 70 +
        5085714564534939108182996894032604346575301153046687556245970040957890) * 10 ^ 70 +
        9106873855920912684147237316440567022502647834623171084255852347111591) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 48 +
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
    rw [show 55 = 18 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
