/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Exceptional coefficient convolution

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
  recurrence2C4_coeff_0
  recurrence2C4_coeff_1
  recurrence2C4_coeff_2
  recurrence2C4_coeff_3
  recurrence2C4_coeff_4
  recurrence2C4_coeff_5
  recurrence2C4_coeff_6
  recurrence2C4_coeff_7
  recurrence2C4_coeff_8
  recurrence2C4_coeff_9
  recurrence2C4_coeff_10
  recurrence2C4_coeff_11
  recurrence2C4_coeff_12
  recurrence2C4_coeff_13
  recurrence2C4_coeff_14
  recurrence2C4_coeff_15
  recurrence2C4_coeff_16
  recurrence2C4_coeff_17
  recurrence2C4_coeff_18
  recurrence2C4_coeff_19
  recurrence2C4_coeff_20
  recurrence2C4_coeff_21
  recurrence2C4_coeff_22
  recurrence2C4_coeff_23
  recurrence2C4_coeff_24
  recurrence2C4_coeff_25
  recurrence2C4_coeff_26
  recurrence2C4_coeff_27
  recurrence2C4_coeff_28
  recurrence2C4_coeff_29
  recurrence2C4_coeff_30
  recurrence2C4_coeff_31
  recurrence2C4_coeff_32
  recurrence2C4_coeff_33
  recurrence2C4_coeff_34
  recurrence2C4_coeff_35
  recurrence2C4_coeff_36
  recurrence2C4_coeff_37
  recurrence2C4_coeff_38
  recurrence2C4_coeff_39
  recurrence2C4_coeff_40
  recurrence2C4_coeff_41
  recurrence2C4_coeff_42
  recurrence2C4_coeff_43
  recurrence2C4_coeff_44
  recurrence2C4_coeff_45
  recurrence2C4_coeff_46
  recurrence2C4_coeff_47
  recurrence2C4_coeff_48
  recurrence2C4_coeff_49
  recurrence2C4_coeff_50
  recurrence2C4_coeff_51
  recurrence2C4_coeff_52
  recurrence2C4_coeff_53
  recurrence2C4_coeff_54
  recurrence2C4_coeff_55
  recurrence2C4_coeff_56
  recurrence2C4_coeff_57
  recurrence2C4_coeff_58
  recurrence2C4_coeff_59
  recurrence2C4_coeff_60
  recurrence2C4_coeff_61
  recurrence2C4_coeff_62
  recurrence2C4_coeff_63
  recurrence2C4_coeff_64
  recurrence2C4_coeff_65
  recurrence2C4_coeff_66
  recurrence2C4_coeff_67
  recurrence2C4_coeff_68
  recurrence2C4_coeff_69
  recurrence2C4_coeff_70
  recurrence2C4_coeff_71
  recurrence2C4_coeff_72
  recurrence2C4_coeff_73
  recurrence2C4_coeff_74
  recurrence2C4_coeff_75
  recurrence2C4_coeff_76
  recurrence2C4_coeff_77
  recurrence2C4_coeff_78
  recurrence2C4_coeff_79
  recurrence2C4_coeff_80
  recurrence2C4_coeff_81
  recurrence2C4_coeff_82
  recurrence2C4_coeff_83
  recurrence2C4_coeff_84
  recurrence2C4_coeff_85
  recurrence2C4_coeff_86
  recurrence2C4_coeff_87
  recurrence2C4_coeff_88
  recurrence2C4_coeff_89
  recurrence2C4_coeff_90
  recurrence2C4_coeff_91
  recurrence2C4_coeff_92
  recurrence2C4_coeff_93
  recurrence2C4_coeff_94
  recurrence2C4_coeff_95
  recurrence2C4_coeff_96
  recurrence2C4_coeff_97
  recurrence2C4_coeff_98
  recurrence2C4_coeff_99
  recurrence2C4_coeff_100
  recurrence2C4_coeff_101
  recurrence2C4_coeff_102
  recurrence2C4_coeff_103
  recurrence2C4_coeff_104
  recurrence2C4_coeff_105
  recurrence2C4_coeff_106
  recurrence2C4_coeff_107
  recurrence2C4_coeff_108
  recurrence2C4_coeff_109
  recurrence2C4_coeff_110
  recurrence2C4_coeff_111
  recurrence2C4_coeff_112
  recurrence2C4_coeff_113
  recurrence2C4_coeff_114
  recurrence2C4_coeff_115
  recurrence2C4_coeff_116
  recurrence2C4_coeff_117
  recurrence2C4_coeff_118
  recurrence2C4_coeff_119
  recurrence2C4_coeff_120
  recurrence2C4_coeff_121
  recurrence2C4_coeff_122
  recurrence2C4_coeff_123
  recurrence2C4_coeff_124
  recurrence2C4_coeff_125
  recurrence2C4_coeff_126
  recurrence2C4_coeff_127
  recurrence2C4_coeff_128
  recurrence2C4_coeff_129
  recurrence2C4_coeff_130
  recurrence2C4_coeff_131
  recurrence2C4_coeff_132
  recurrence2C4_coeff_133
  recurrence2C4_coeff_134
  recurrence2C4_coeff_135
  recurrence2C4_coeff_136
  recurrence2C4_coeff_137
  recurrence2C4_coeff_138
  recurrence2C4_coeff_139
  recurrence2C4_coeff_140
  recurrence2C4_coeff_141
  recurrence2C4_coeff_142
  recurrence2C4_coeff_143
  recurrence2C4_coeff_144
  recurrence2C4_coeff_145
  recurrence2C4_coeff_146
  recurrence2C4_coeff_147
  recurrence2C4_coeff_148
  recurrence2C4_coeff_149
  recurrence2C4_coeff_150
  recurrence2C4_coeff_151
  recurrence2C4_coeff_152
  recurrence2C4_coeff_153
  recurrence2C4_coeff_154
  recurrence2C4_coeff_155
  recurrence2C4_coeff_156
  recurrence2C4_coeff_157
  recurrence2C4_coeff_158
  recurrence2C4_coeff_159
  recurrence2C4_coeff_160
  recurrence2C4_coeff_161
  recurrence2C4_coeff_162
  recurrence2C4_coeff_163
  recurrence2C4_coeff_164
  recurrence2C4_coeff_165
  recurrence2C4_coeff_166
  recurrence2C4_coeff_167
  recurrence2C4_coeff_168
  recurrence2C4_coeff_169
  recurrence2C4_coeff_170
  recurrence2C4_coeff_171
  recurrence2C4_coeff_172
  recurrence2C4_coeff_173
  recurrence2C4_coeff_174
  recurrence2C4_coeff_175
  recurrence2C4_coeff_176
  recurrence2C4_coeff_177
  recurrence2C4_coeff_178

theorem recurrence2Scalar4Exceptional_coeff_0 :
    recurrence2Scalar4Exceptional.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_1 :
    recurrence2Scalar4Exceptional.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_2 :
    recurrence2Scalar4Exceptional.coeff 2 =
      (141288909696 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_3 :
    recurrence2Scalar4Exceptional.coeff 3 =
      (-81049818469392 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_4 :
    recurrence2Scalar4Exceptional.coeff 4 =
      (-773631043896598008 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_5 :
    recurrence2Scalar4Exceptional.coeff 5 =
      (378228717197192158944 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_6 :
    recurrence2Scalar4Exceptional.coeff 6 =
      (1232003214540211014700876 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_7 :
    recurrence2Scalar4Exceptional.coeff 7 =
      (-796271009398892766713998172 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_8 :
    recurrence2Scalar4Exceptional.coeff 8 =
      (-566696531802612637903715563556 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_9 :
    recurrence2Scalar4Exceptional.coeff 9 =
      (567281227525908554331912942718560 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_10 :
    recurrence2Scalar4Exceptional.coeff 10 =
      (-107458733456395631034050144521864400 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_11 :
    recurrence2Scalar4Exceptional.coeff 11 =
      (-12326605307477730646064660582365884292 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_12 :
    recurrence2Scalar4Exceptional.coeff 12 =
      (4399929534431734234650437734413683231570 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_13 :
    recurrence2Scalar4Exceptional.coeff 13 =
      (235475422767304210217210270782317041619564 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_14 :
    recurrence2Scalar4Exceptional.coeff 14 =
      (-209596080694095853677439300871305472620402469 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_15 :
    recurrence2Scalar4Exceptional.coeff 15 =
      (51132627479588002906889045925287046870929988561 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_16 :
    recurrence2Scalar4Exceptional.coeff 16 =
      (-11463899512329735845726415509342488120881886951883 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_17 :
    recurrence2Scalar4Exceptional.coeff 17 =
      (2106930704016317971795973309098167821115656970459452 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_18 :
    recurrence2Scalar4Exceptional.coeff 18 =
      (-275153650641009432191454908222193567950631257502365761 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_19 :
    recurrence2Scalar4Exceptional.coeff 19 =
      (23525918194122835940227081215389858417404503696461932819 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_20 :
    recurrence2Scalar4Exceptional.coeff 20 =
      (-793670692853789370149759627826649909057476958791132873715 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_21 :
    recurrence2Scalar4Exceptional.coeff 21 =
      (-121665544760024885680124908340928463559904147770122868326489 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_22 :
    recurrence2Scalar4Exceptional.coeff 22 =
      (25488075416781377461771304380493740066354577130450994337936225 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_23 :
    recurrence2Scalar4Exceptional.coeff 23 =
      (-2546707136225235447478657101888113305597886631832383067132301029 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_24 :
    recurrence2Scalar4Exceptional.coeff 24 =
      (152377249886734617918044847803267621911915754007361596747614397147 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_25 :
    recurrence2Scalar4Exceptional.coeff 25 =
      (-3326840552132757617110013218728029383100416624971396491358563397602 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_26 :
    recurrence2Scalar4Exceptional.coeff 26 =
      (-392405288722785381566740439492845171509012285191899786478901836772592 : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_27 :
    recurrence2Scalar4Exceptional.coeff 27 =
      ((5 * 10 ^ 70 +
        5813778929082262428016125844869949662657550031032226784731129573512998) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_28 :
    recurrence2Scalar4Exceptional.coeff 28 =
      -((412 * 10 ^ 70 +
        3116732661628390868742267832962924693714923644878233586722119662235883) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_29 :
    recurrence2Scalar4Exceptional.coeff 29 =
      ((21461 * 10 ^ 70 +
        1484134921162116522955955514015943721248412950336455497252806050772954) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_30 :
    recurrence2Scalar4Exceptional.coeff 30 =
      -((835951 * 10 ^ 70 +
        8908794476875436471793126792729339525105809848770383172192456630017023) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_31 :
    recurrence2Scalar4Exceptional.coeff 31 =
      ((24379578 * 10 ^ 70 +
        9215670479877646924930167434023329541971605016978336177033736897491916) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_32 :
    recurrence2Scalar4Exceptional.coeff 32 =
      -((517044143 * 10 ^ 70 +
        2452025179695074108152040724330674157728389413085193020080644934730015) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_33 :
    recurrence2Scalar4Exceptional.coeff 33 =
      ((8285943227 * 10 ^ 70 +
        2238181595217006502104902102265682947675205600194816092337019374806775) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_34 :
    recurrence2Scalar4Exceptional.coeff 34 =
      -((199083772134 * 10 ^ 70 +
        8601765013544816472328436993428022417222382089462188428478622830617034) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_35 :
    recurrence2Scalar4Exceptional.coeff 35 =
      ((11232151955083 * 10 ^ 70 +
        8655969058010552146474812574661415670840923178341794837829007696266532) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_36 :
    recurrence2Scalar4Exceptional.coeff 36 =
      -((575845306804122 * 10 ^ 70 +
        0035159076241173993285752273618212650475157933654837352580019289043233) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_37 :
    recurrence2Scalar4Exceptional.coeff 37 =
      ((21453280274797970 * 10 ^ 70 +
        4280813876993673033908655724397001257848593049730054135963404493658725) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_38 :
    recurrence2Scalar4Exceptional.coeff 38 =
      -((606567374167662784 * 10 ^ 70 +
        5303917444498251524756761003617075071141748700632996624264874684288443) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_39 :
    recurrence2Scalar4Exceptional.coeff 39 =
      ((13938577441140873728 * 10 ^ 70 +
        8832657370110486055783557337575265249130777128522794951348452337024419) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_40 :
    recurrence2Scalar4Exceptional.coeff 40 =
      -((292637261236107164284 * 10 ^ 70 +
        7012477273479569708071824651729649487770049507085989219516006681880670) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_41 :
    recurrence2Scalar4Exceptional.coeff 41 =
      ((6736720861010958033821 * 10 ^ 70 +
        6771374384874226846589154603948900695197095053525533619583976806793618) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_42 :
    recurrence2Scalar4Exceptional.coeff 42 =
      -((186029647688127638143899 * 10 ^ 70 +
        6689667261720351924743129234214657659613828441832705703563582108616999) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_43 :
    recurrence2Scalar4Exceptional.coeff 43 =
      ((5536718493989558352971902 * 10 ^ 70 +
        6305516248040987424676406096076585404618971460932643871892465498282931) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_44 :
    recurrence2Scalar4Exceptional.coeff 44 =
      -((158809296914596905032784995 * 10 ^ 70 +
        3345506762280346002301286294248632256850964214821459682769270250969484) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_45 :
    recurrence2Scalar4Exceptional.coeff 45 =
      ((4259272612128639454250710559 * 10 ^ 70 +
        9552901435518310991075295548158865228137893935758450724698198090128089) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_46 :
    recurrence2Scalar4Exceptional.coeff 46 =
      -((107619901876699242003918698599 * 10 ^ 70 +
        2585927986865425367688665540911039279906516280619756578765285759870103) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_47 :
    recurrence2Scalar4Exceptional.coeff 47 =
      ((2584054196752717821454395953043 * 10 ^ 70 +
        9828599916506528201991753150452772828129182141189315219525326236964672) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_48 :
    recurrence2Scalar4Exceptional.coeff 48 =
      -((58967820684486345565090591989112 * 10 ^ 70 +
        8105085100817767716529605769566240804653687528275615370020789575128523) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_49 :
    recurrence2Scalar4Exceptional.coeff 49 =
      ((1274307722077151383492049087021206 * 10 ^ 70 +
        6868849638092345500494062408870920755448315821796469856714679078863495) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_50 :
    recurrence2Scalar4Exceptional.coeff 50 =
      -((26047637636770954276083851600645975 * 10 ^ 70 +
        2009745173654304504421823836088991401594875057916954155108182493737516) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_51 :
    recurrence2Scalar4Exceptional.coeff 51 =
      ((504984162697139940194068503440484869 * 10 ^ 70 +
        9177729699702850811864858777590291194997463364971618737092683384014510) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_52 :
    recurrence2Scalar4Exceptional.coeff 52 =
      -((9326939488275805242356970470003780157 * 10 ^ 70 +
        5948603493775765712253738899435558737661498986893296228008393545084984) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_53 :
    recurrence2Scalar4Exceptional.coeff 53 =
      ((164695066422805807664364005327857417410 * 10 ^ 70 +
        8731928833566647722566758051456938364035629843814161522673015820432475) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_54 :
    recurrence2Scalar4Exceptional.coeff 54 =
      -((2784487024228062135373444560626506891585 * 10 ^ 70 +
        2873290667642028386743295844238880179711445833610320051651838996569133) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_55 :
    recurrence2Scalar4Exceptional.coeff 55 =
      ((45079637632855353674110222125486379838398 * 10 ^ 70 +
        1180871771350820019639228814660707216040374598471119781797155515010506) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_56 :
    recurrence2Scalar4Exceptional.coeff 56 =
      -((698846134724703814495411991599019991913828 * 10 ^ 70 +
        1138051475082755213871288950103362369457531547751025121694770925094430) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_57 :
    recurrence2Scalar4Exceptional.coeff 57 =
      ((10379913128318773419064932581080808256344335 * 10 ^ 70 +
        3111889053698338294949449083044956231638046916808179585937252709820053) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_58 :
    recurrence2Scalar4Exceptional.coeff 58 =
      -((147864211631699087066947779459579863084372000 * 10 ^ 70 +
        9395769926676933268087009308322154516204433702777798554958297215251324) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_59 :
    recurrence2Scalar4Exceptional.coeff 59 =
      ((2022263756076864304716430189358327972729982865 * 10 ^ 70 +
        6347862995784480829676707679065868236617853172307959697749319862075480) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_60 :
    recurrence2Scalar4Exceptional.coeff 60 =
      -((26573538806030623754400532809770398394659037116 * 10 ^ 70 +
        3444730293444325615200753784751099003183711128782922508113529217605188) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_61 :
    recurrence2Scalar4Exceptional.coeff 61 =
      ((335695917985245292154102332171799798778603354319 * 10 ^ 70 +
        4671237700767167221926260265851431809012287132062085156062608785032554) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_62 :
    recurrence2Scalar4Exceptional.coeff 62 =
      -((4079353242635839230422981709327698322110664990767 * 10 ^ 70 +
        7736257630340465765617723341561558582545989696556357399932690831465278) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_63 :
    recurrence2Scalar4Exceptional.coeff 63 =
      ((47721162027777543699676351402097051913852351765954 * 10 ^ 70 +
        1948106064327292427751464493211509024752086928182197159506318023322493) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_64 :
    recurrence2Scalar4Exceptional.coeff 64 =
      -((537841715620223814638790718551918785557368430784402 * 10 ^ 70 +
        3855744319539567376803271623009771918383445237908971691463803909782709) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_65 :
    recurrence2Scalar4Exceptional.coeff 65 =
      ((5844215836550317226502368683326703595288466954667517 * 10 ^ 70 +
        9546199134596602997533407734836465808600908788777194426712448419340233) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_66 :
    recurrence2Scalar4Exceptional.coeff 66 =
      -((61257854870401696544353468236033976443027949549664940 * 10 ^ 70 +
        3566130737759823039710401972706455102726688484655187225831830896922248) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_67 :
    recurrence2Scalar4Exceptional.coeff 67 =
      ((619677065959742327253491343683135049550839611607399447 * 10 ^ 70 +
        3381278232347528465654810492986813057898104007544632323742515355918713) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_68 :
    recurrence2Scalar4Exceptional.coeff 68 =
      -((6052923273960213147951563344861986439172778197160774088 * 10 ^ 70 +
        2813105386861452372024454606455104009219227560143765915110085310820888) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_69 :
    recurrence2Scalar4Exceptional.coeff 69 =
      ((57125362695745639375834617000049717521621944581151470272 * 10 ^ 70 +
        8770322577566426196122991262890695856888188530556071702592494924199409) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_70 :
    recurrence2Scalar4Exceptional.coeff 70 =
      -((521232178595255215027097999767127060609651674094337017145 * 10 ^ 70 +
        4153598466934402310014894776040367296688805203611828768268295936023556) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_71 :
    recurrence2Scalar4Exceptional.coeff 71 =
      ((4600537109825564537014574343477574082282338924969423174188 * 10 ^ 70 +
        2886976988892060706846499732197918303144994415833451943616120267619029) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_72 :
    recurrence2Scalar4Exceptional.coeff 72 =
      -((39296261781795072659283482928000105950994147663567267306774 * 10 ^ 70 +
        0443625543364291247606427644490676033613744654745950858809006941752201) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_73 :
    recurrence2Scalar4Exceptional.coeff 73 =
      ((324965447834711593185764916558885429010867885039762090980778 * 10 ^ 70 +
        9365105140720422426116759928008281897734110852129164112066525593472671) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_74 :
    recurrence2Scalar4Exceptional.coeff 74 =
      -((2602976082568757085697644106062949600837286824673842783530978 * 10 ^ 70 +
        8925284348621355708567327752438186419734461371226894436311294154375513) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_75 :
    recurrence2Scalar4Exceptional.coeff 75 =
      ((20206019082197367148678875426321418081945481425577155833479151 * 10 ^ 70 +
        8305641696748687749401918368816600596290479784031974088124810505797549) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_76 :
    recurrence2Scalar4Exceptional.coeff 76 =
      -((152085559558953145916001362928347177047299415239521389617310609 * 10 ^ 70 +
        1529907011678505133536948016253719669322837119672491543321456072809573) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_77 :
    recurrence2Scalar4Exceptional.coeff 77 =
      ((1110361201901451857750361534867117211173023821543051085444602763 * 10 ^ 70 +
        0971100511158575033834665666026539174761383229792142770124794487404734) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_78 :
    recurrence2Scalar4Exceptional.coeff 78 =
      -((7865853864254014088324014733350095756512888645684561746035058847 * 10 ^ 70 +
        4221827438731185730964696256464618670487936483111216678770795008776893) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_79 :
    recurrence2Scalar4Exceptional.coeff 79 =
      ((54085789797841902688631072564231207074209497242687347658677190206 * 10 ^ 70 +
        1115950206660391178599181684914005184100817370781166181146546310298421) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_80 :
    recurrence2Scalar4Exceptional.coeff 80 =
      -((361141375342824430180015007652729972641864898681193450533738376313 * 10 ^ 70 +
        4937546799351294510372957849778943546907533650783547835436239101758874) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_81 :
    recurrence2Scalar4Exceptional.coeff 81 =
      ((2342902452027906326700373137309188386747104675025035782816249722375 * 10 ^ 70 +
        5916733331542800023035602821955455319364626097736434461532955672270370) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_82 :
    recurrence2Scalar4Exceptional.coeff 82 =
      -((14773844661503155154021774316744747064048393387811994572566558191776 * 10 ^ 70 +
        9437344538391000153176961379530583607074356106920103125963826023389442) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_83 :
    recurrence2Scalar4Exceptional.coeff 83 =
      ((90570635047150560929938912541907570467992658589033882948284071542855 * 10 ^ 70 +
        2943476823606472987307969232649046012157751488835636007340244678897011) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_84 :
    recurrence2Scalar4Exceptional.coeff 84 =
      -((539874919894676351571921162061115639778154680903598162362916067951476 * 10 ^ 70 +
        7607414514789988057969587148720957464189335853451519068488648342348761) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_85 :
    recurrence2Scalar4Exceptional.coeff 85 =
      ((3129997887309920923655237601627952745273682510600614232404212301005389 * 10 ^ 70 +
        0383831370502394729248159625487051216848763965730772162974565426833135) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_86 :
    recurrence2Scalar4Exceptional.coeff 86 =
      -(((1 * 10 ^ 70 +
        7660286780566946918257887400250428212078670323845673077154903841938513) * 10 ^ 70 +
        8910920650558273750374092612091646376374042266862148915020129009264745) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_87 :
    recurrence2Scalar4Exceptional.coeff 87 =
      (((9 * 10 ^ 70 +
        7036118148964442741212234045810189743408541412783623659826509520106419) * 10 ^ 70 +
        9821018036336877553206200145386137055154854433665993409246253706545398) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_88 :
    recurrence2Scalar4Exceptional.coeff 88 =
      -(((51 * 10 ^ 70 +
        9358971154014587137475640807829820873146227152477545052646863174062170) * 10 ^ 70 +
        0995683050868441093806709302402035719332941260300700846466744991635267) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_89 :
    recurrence2Scalar4Exceptional.coeff 89 =
      (((270 * 10 ^ 70 +
        7071150309852903988817756243336218324934028632420768545381584656087439) * 10 ^ 70 +
        6684512331129239299613877740174165738571268573277430732634607740978594) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_90 :
    recurrence2Scalar4Exceptional.coeff 90 =
      -(((1373 * 10 ^ 70 +
        8079700022464337217364220138692293227216530168362776996109248923722355) * 10 ^ 70 +
        9058217320698630856486123401588652672010855817913319408265691969241535) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_91 :
    recurrence2Scalar4Exceptional.coeff 91 =
      (((6791 * 10 ^ 70 +
        6091085758363258482395870563995938361831513035019044329228526131603417) * 10 ^ 70 +
        4769625321641673883100548258365414417581550007032199733004070134744579) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_92 :
    recurrence2Scalar4Exceptional.coeff 92 =
      -(((32752 * 10 ^ 70 +
        6434784886178876387112935047756212533579383115775209805907901400988668) * 10 ^ 70 +
        8868209828995812851068178050230551742743054418487379213389728823467445) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_93 :
    recurrence2Scalar4Exceptional.coeff 93 =
      (((154259 * 10 ^ 70 +
        7893542227251550804150639866296515155646465066244897418708065484950973) * 10 ^ 70 +
        3808647344437913778604474665616038967277603933073825213962221685270556) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_94 :
    recurrence2Scalar4Exceptional.coeff 94 =
      -(((709131 * 10 ^ 70 +
        8367451577789006176962855146159251599249572064173905190130723576228939) * 10 ^ 70 +
        0865860044854775958866602884416764665927624472080938752712494609219956) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_95 :
    recurrence2Scalar4Exceptional.coeff 95 =
      (((3174248 * 10 ^ 70 +
        7186231006030023253368476108869012302406153745468381544682434318189232) * 10 ^ 70 +
        3162415857300302123949925623396386988740378990459353145256048274233610) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_96 :
    recurrence2Scalar4Exceptional.coeff 96 =
      -(((13815692 * 10 ^ 70 +
        1045721309641719767027455494439367234266057088570607565309733532402257) * 10 ^ 70 +
        9873818600148456529795468068012921461511019450175300381130246135606143) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_97 :
    recurrence2Scalar4Exceptional.coeff 97 =
      (((58641869 * 10 ^ 70 +
        8817669616001067215822992145925761124705884725224113391502297404730246) * 10 ^ 70 +
        3224691892400427095801142166248841342749265764741488246333540390925689) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_98 :
    recurrence2Scalar4Exceptional.coeff 98 =
      -(((244441877 * 10 ^ 70 +
        8810164806160064133297731834542439148177335661539801369297988823494463) * 10 ^ 70 +
        9752782588925755327157562003579471972212171853749690108264728825160273) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_99 :
    recurrence2Scalar4Exceptional.coeff 99 =
      (((1004331322 * 10 ^ 70 +
        6493275353161285673503628747268983110978498062847114816189651756055432) * 10 ^ 70 +
        4782023403304594500980969750729391565753546469157970995782761922554309) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_100 :
    recurrence2Scalar4Exceptional.coeff 100 =
      -(((4033161307 * 10 ^ 70 +
        4968959265962634785229267874724426870093952686532703484712121883048171) * 10 ^ 70 +
        4020184100859200875284448081100657439602868431029639785513758579739628) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_101 :
    recurrence2Scalar4Exceptional.coeff 101 =
      (((15545155990 * 10 ^ 70 +
        6202327746807496862168977120757407873298296020943844258144992300784913) * 10 ^ 70 +
        3005082324866479585600623980376001438521261495330201448017219335422179) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_102 :
    recurrence2Scalar4Exceptional.coeff 102 =
      -(((57007672876 * 10 ^ 70 +
        9443248186208251860603839775826306669638175057775470556305451218110746) * 10 ^ 70 +
        7224211259532787698509774926631218810042006411210388814021035542553149) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_103 :
    recurrence2Scalar4Exceptional.coeff 103 =
      (((204284588354 * 10 ^ 70 +
        7255499588038449484015033875345316664171262199913533438301376007584334) * 10 ^ 70 +
        1307310568449581460285846081560118078298871496582949300908419334065421) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_104 :
    recurrence2Scalar4Exceptional.coeff 104 =
      -(((760097198550 * 10 ^ 70 +
        3838942082846404656386498744525697287106291158364968823180256438098390) * 10 ^ 70 +
        9679546363178919566989976624808526697183344245715409530377732413959591) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_105 :
    recurrence2Scalar4Exceptional.coeff 105 =
      (((2989445466237 * 10 ^ 70 +
        3492910109159837343851276934093795665879128881102565125657112136615197) * 10 ^ 70 +
        7441990106238678433275880415530341742847884032255631811778123093634761) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_106 :
    recurrence2Scalar4Exceptional.coeff 106 =
      -(((11289325073134 * 10 ^ 70 +
        0741858932502990094838357449280238664924199908857913833884251233049864) * 10 ^ 70 +
        4051382672639879089699285118120582742382724836444672112245143360969078) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_107 :
    recurrence2Scalar4Exceptional.coeff 107 =
      (((34878004274876 * 10 ^ 70 +
        3140755271548820401317493474181362178648060063102559754926249745035486) * 10 ^ 70 +
        8648152241981551928208986885816953682776231481123158644771696167669324) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_108 :
    recurrence2Scalar4Exceptional.coeff 108 =
      -(((74139217692198 * 10 ^ 70 +
        7489927479302810773946447767564446738576493223666570367970059921446442) * 10 ^ 70 +
        3092580952795731567432132275048598281076907120501722878909081196687214) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_109 :
    recurrence2Scalar4Exceptional.coeff 109 =
      (((122189633777709 * 10 ^ 70 +
        3976893643907388761654363627106510262163366331376545423290576771562655) * 10 ^ 70 +
        8291829294625286520425292482045911770942771544676136346975773306121751) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_110 :
    recurrence2Scalar4Exceptional.coeff 110 =
      -(((852776623307690 * 10 ^ 70 +
        4793491046052456049840949105413762851315380548875914787427116957006174) * 10 ^ 70 +
        1945235200432824860041001239981639809985097901791881862139464180788728) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_111 :
    recurrence2Scalar4Exceptional.coeff 111 =
      (((7862997781209285 * 10 ^ 70 +
        7818764378685055091098429055213255593214358396431520727367828113629748) * 10 ^ 70 +
        0600295373694325552540995478809209544614196937596288675038128133797912) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_112 :
    recurrence2Scalar4Exceptional.coeff 112 =
      -(((38217446965144718 * 10 ^ 70 +
        8165555097925633983696442189647141778340826216316727780391912853168565) * 10 ^ 70 +
        0141871866911200939750840539628243773529393633006693926431150077952413) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_113 :
    recurrence2Scalar4Exceptional.coeff 113 =
      (((59964472389964863 * 10 ^ 70 +
        9169632988056072829978587310005269450728408787753378124156382774581174) * 10 ^ 70 +
        7630206193726110638526954405760041381974567273705153219505458307191592) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_114 :
    recurrence2Scalar4Exceptional.coeff 114 =
      (((422278963848318606 * 10 ^ 70 +
        9196919924829560562352854920087647891016292643933044844165833193818215) * 10 ^ 70 +
        7100614552480849392935752570492921867719512417296648559514633354005022) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_115 :
    recurrence2Scalar4Exceptional.coeff 115 =
      -(((2906855239082010777 * 10 ^ 70 +
        2636807815040854557787075974047082761088198808787560911726176142098960) * 10 ^ 70 +
        6175125477119822239946035901157655249365982205184413564244576149970267) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_116 :
    recurrence2Scalar4Exceptional.coeff 116 =
      (((3171117456877652954 * 10 ^ 70 +
        9009432871405683306401290916562409379057015591167905512295910492106091) * 10 ^ 70 +
        8266295070711422109518636072879834009261642404824600168722190191352423) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_117 :
    recurrence2Scalar4Exceptional.coeff 117 =
      (((52480755987136567170 * 10 ^ 70 +
        3832286021522203427914220892093479006101317517019200770244638089581885) * 10 ^ 70 +
        2638888604355271874235103122239282623602703942625744146512848582940587) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_118 :
    recurrence2Scalar4Exceptional.coeff 118 =
      -(((333425214795633008329 * 10 ^ 70 +
        3264067766788571905639822971794730350013696045182329797369038096013632) * 10 ^ 70 +
        4216027378927510102446025236356173582607976503481923777075969593817724) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_119 :
    recurrence2Scalar4Exceptional.coeff 119 =
      (((543519661435194997492 * 10 ^ 70 +
        9827801215540301352719480620830496117159399838954373501925069903626800) * 10 ^ 70 +
        3457493499199383494183151248219719338186546963244963245955279458951755) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_120 :
    recurrence2Scalar4Exceptional.coeff 120 =
      (((4110244332119526962981 * 10 ^ 70 +
        5862320512626827841454632895228566317381035786727511649399830039313098) * 10 ^ 70 +
        6467516042133363027905320719613933393237696352042713129244057019818749) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_121 :
    recurrence2Scalar4Exceptional.coeff 121 =
      -(((30334904886316149415380 * 10 ^ 70 +
        3617356949823886806163820030737307610443452018618017939115006710877581) * 10 ^ 70 +
        7994248420155236902387058543229939019686313427596179669682825152980780) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_122 :
    recurrence2Scalar4Exceptional.coeff 122 =
      (((64243268604791697536612 * 10 ^ 70 +
        3652837289047269121336073661464375100892325188350896853953320505787144) * 10 ^ 70 +
        9666125495311525864981488884047276889580101683020871159598006752188724) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_123 :
    recurrence2Scalar4Exceptional.coeff 123 =
      (((273758201918379384439054 * 10 ^ 70 +
        7732942514664192827814934836190524896285599306877740913117644438100525) * 10 ^ 70 +
        2061589425668463540200170131865701101890452651987808407293799653335200) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_124 :
    recurrence2Scalar4Exceptional.coeff 124 =
      -(((2499024887016270530580003 * 10 ^ 70 +
        4067658097452251237844785054569804757943828519532783687992078074214270) * 10 ^ 70 +
        7852095002556677556901985990646332006602645706436249166296983119681585) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_125 :
    recurrence2Scalar4Exceptional.coeff 125 =
      (((6817057010225864961561670 * 10 ^ 70 +
        1989644210651570029328362156478959341989977896263997532940471806998245) * 10 ^ 70 +
        4492449854051961284158769075854757231617208083576609334619545010474469) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_126 :
    recurrence2Scalar4Exceptional.coeff 126 =
      (((12591719249266517528646039 * 10 ^ 70 +
        2944801103025326945636034075953376812481128449584681368875457685617254) * 10 ^ 70 +
        9952263907630122025591701802743213813538667244224681264101961163944066) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_127 :
    recurrence2Scalar4Exceptional.coeff 127 =
      -(((179017027708981458914689545 * 10 ^ 70 +
        8066646592686306226044512776872113254893690945843471510587806475968318) * 10 ^ 70 +
        5251489362803919642206959703799499205829939753443623679082178699633245) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_128 :
    recurrence2Scalar4Exceptional.coeff 128 =
      (((625589915271332331080804686 * 10 ^ 70 +
        7891342880620530960357092942067951777088994780700549231562195370717773) * 10 ^ 70 +
        6010764447323756648230950906856293543195838379983531282244837680810306) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_129 :
    recurrence2Scalar4Exceptional.coeff 129 =
      (((79980179430588749815393780 * 10 ^ 70 +
        5430423251711389266387440407773612424869832678561195671040107955427765) * 10 ^ 70 +
        6998003728764012676096592591988517354094791864642227119126115696114625) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_130 :
    recurrence2Scalar4Exceptional.coeff 130 =
      -(((10723471539158614620985550697 * 10 ^ 70 +
        6004374381434614644623823570003808898302820186455754548598951960065299) * 10 ^ 70 +
        7652889230071820270510263992504749236013790896303236116283424473024463) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_131 :
    recurrence2Scalar4Exceptional.coeff 131 =
      (((49052382310083761847602745741 * 10 ^ 70 +
        9492999529138140649274517866793583078141139895211927010327499265553243) * 10 ^ 70 +
        2549070397794679429837843089871836229705341672698920046700825214152865) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_132 :
    recurrence2Scalar4Exceptional.coeff 132 =
      -(((59950850434969895054113827200 * 10 ^ 70 +
        3204795634501814521206350424889021268773455288037708917943793181115227) * 10 ^ 70 +
        1780970325979576772241573894445329617346844471504500078025919388691509) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_133 :
    recurrence2Scalar4Exceptional.coeff 133 =
      -(((480760084742765937581079407637 * 10 ^ 70 +
        2476387238097224360820329015329647227293889202932611507862648891679154) * 10 ^ 70 +
        8122554402073427062546585247732297451215725982534424763700927826312081) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_134 :
    recurrence2Scalar4Exceptional.coeff 134 =
      (((3157585992038646673193049114812 * 10 ^ 70 +
        2610808594543477504284882347038171331327153420636071408159074048546981) * 10 ^ 70 +
        6256585367760733333975651668879700634128565106217188130613271543696027) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_135 :
    recurrence2Scalar4Exceptional.coeff 135 =
      -(((7578709797131552231405198278981 * 10 ^ 70 +
        4460279556949815481030136984461991077529331482876711746905339410705392) * 10 ^ 70 +
        4906284165301645462667594487506936412881969682149640656633365051368344) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_136 :
    recurrence2Scalar4Exceptional.coeff 136 =
      -(((10678889924890111455230317570040 * 10 ^ 70 +
        7719913346874224986114318084295368267137748513402932660021668801285722) * 10 ^ 70 +
        8065652312221370621740935088126017337045470489944264208231675317493945) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_137 :
    recurrence2Scalar4Exceptional.coeff 137 =
      (((157516859325119622402678434623624 * 10 ^ 70 +
        5756296601367256397492118687702945446351440391478300061473017183278581) * 10 ^ 70 +
        5665401919620985272421958184983947368021699284343120486469488718325499) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_138 :
    recurrence2Scalar4Exceptional.coeff 138 =
      -(((580523090277123012558279832885201 * 10 ^ 70 +
        2361844665797302851736376630082026569054016415654268794332588627104112) * 10 ^ 70 +
        7957618482756730179811292359661266642383159499427963431852047108022722) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_139 :
    recurrence2Scalar4Exceptional.coeff 139 =
      (((530122972471821151646491819467503 * 10 ^ 70 +
        6870639406002520560049864618793945991069774716971445135112433435263473) * 10 ^ 70 +
        8649036774761777392140180529062522025660355911947273863753713816324242) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_140 :
    recurrence2Scalar4Exceptional.coeff 140 =
      (((5331070322729544626339758988077633 * 10 ^ 70 +
        8990834421623041079113864204836346383401320999155917246575814229602553) * 10 ^ 70 +
        3061907608601315145476236345555985061358086614757306558058300250257054) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_141 :
    recurrence2Scalar4Exceptional.coeff 141 =
      -(((31524469113660461420167371568099074 * 10 ^ 70 +
        1581331939078630019783958339506903103983605741644160120092650117317477) * 10 ^ 70 +
        1207547969048315241488163361250377473735806461840472537624608940250600) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_142 :
    recurrence2Scalar4Exceptional.coeff 142 =
      (((76438004210078084379458492131252723 * 10 ^ 70 +
        6178285822053008442966837756338135639520857860800758036244561670913625) * 10 ^ 70 +
        2539113282394558084910553977870282293006142518505839241003408815047871) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_143 :
    recurrence2Scalar4Exceptional.coeff 143 =
      (((46434912496965148443034698243744357 * 10 ^ 70 +
        8729383947214057314640263045618859469477043943300574074592035215095625) * 10 ^ 70 +
        6604534729469353375055750359829420983557519596524294788443526622014408) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_144 :
    recurrence2Scalar4Exceptional.coeff 144 =
      -(((1158362669022095885362954404505456368 * 10 ^ 70 +
        2241243841474912269825540315414874745045898636945556361501900651326741) * 10 ^ 70 +
        5755771945612053384490934259000782030078119892201736191895181493660001) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_145 :
    recurrence2Scalar4Exceptional.coeff 145 =
      (((4749177069499664086795701314045822863 * 10 ^ 70 +
        5695966356746438993340172349025900871355224485192134973010755406796742) * 10 ^ 70 +
        0978895326666535272034427505833862347323679774710376913550924680643332) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_146 :
    recurrence2Scalar4Exceptional.coeff 146 =
      -(((8004072074016430179013633868056384488 * 10 ^ 70 +
        3350779286725740080219799552420559102575523922775363262905433164213269) * 10 ^ 70 +
        6434456903720743178383688404519007706177160984042683401245456874483450) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_147 :
    recurrence2Scalar4Exceptional.coeff 147 =
      -(((18569526838722318947622691380271584337 * 10 ^ 70 +
        2944222749180223799493089400309925143053807394818323049951272347358642) * 10 ^ 70 +
        8385667859359255152742489541333171252081563950381989359963118489674341) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_148 :
    recurrence2Scalar4Exceptional.coeff 148 =
      (((175680822354935982073754843339789731984 * 10 ^ 70 +
        0749636147081414702806108235855200994302546065759153591005590553079030) * 10 ^ 70 +
        0834658200180588545581813054997667192439547026932964877200229397004232) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_149 :
    recurrence2Scalar4Exceptional.coeff 149 =
      -(((592847863804147898178521638959287045290 * 10 ^ 70 +
        9521563706024139037842850501621251296205166806168992394624414522516549) * 10 ^ 70 +
        0775430573548030016156638321084192470162240023970613889186395620609340) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_150 :
    recurrence2Scalar4Exceptional.coeff 150 =
      (((777502210126286640719291682194881989846 * 10 ^ 70 +
        1802205838950983467190590445754881997656373261341262006374193695901475) * 10 ^ 70 +
        2551846455822655786599080190263887041851006838567267107447369946744233) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_151 :
    recurrence2Scalar4Exceptional.coeff 151 =
      (((2806298008036770732851480781228216902523 * 10 ^ 70 +
        0492299947348225766499603436861678632187611340364904774056397217598376) * 10 ^ 70 +
        4639558481283773540410539614929856780537335749387614819033953580035724) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_152 :
    recurrence2Scalar4Exceptional.coeff 152 =
      -(((20836581717279483665615636745347622871513 * 10 ^ 70 +
        0926232033689238758828202162699851146293141153881678015029347650594978) * 10 ^ 70 +
        7045593866817572126204489771214801515053575652478463226228363270689933) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_153 :
    recurrence2Scalar4Exceptional.coeff 153 =
      (((65403885548025217789869554248607868366829 * 10 ^ 70 +
        5671927319377766536447127933192377525258172642322914735928069763885052) * 10 ^ 70 +
        0233064088238834275595276463868098941222929141804351886262633293038514) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_154 :
    recurrence2Scalar4Exceptional.coeff 154 =
      -(((85986381066617794067661218138949679754317 * 10 ^ 70 +
        9396203310727968954084161990407158365244202799840508356158385584641216) * 10 ^ 70 +
        6816674593699282530213848613499197865337863140542434337279288224001287) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_155 :
    recurrence2Scalar4Exceptional.coeff 155 =
      -(((255170302312965852153529641436416406205475 * 10 ^ 70 +
        6436132626925310697500860865614752126435905262629630510703557419465679) * 10 ^ 70 +
        6527359546981715870464053242017418846862550060266680676849714470753135) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_156 :
    recurrence2Scalar4Exceptional.coeff 156 =
      (((1972804204445397871121228897438768172989020 * 10 ^ 70 +
        6831993740131988336664448980226517375954673089077850845121931424732430) * 10 ^ 70 +
        7074047857148306098801360876490798145702499783697697466492796210248716) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_157 :
    recurrence2Scalar4Exceptional.coeff 157 =
      -(((6443739819325249009479929197581890321529650 * 10 ^ 70 +
        5400307004228073634252615079848718170318420901730626752619197455656843) * 10 ^ 70 +
        0395039559511176043539540090493240542239274035723659092663907648372466) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_158 :
    recurrence2Scalar4Exceptional.coeff 158 =
      (((10665442072207740372667504944959334773907360 * 10 ^ 70 +
        1675593395855392079068314314931465058983322179265347676094216307516637) * 10 ^ 70 +
        8744026954806307458079168034468379548004904375687471166329250682231911) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_159 :
    recurrence2Scalar4Exceptional.coeff 159 =
      (((10423775844246201080245023851695556126575576 * 10 ^ 70 +
        5506587483623592710936784441870916849248324905884869698359148800700103) * 10 ^ 70 +
        4353331818521407373210476751443490250828233486436662434469234763000328) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_160 :
    recurrence2Scalar4Exceptional.coeff 160 =
      -(((140329802014146645260738585006039517455313168 * 10 ^ 70 +
        0854550290455641400207980337054673998401087260470817278491888058171681) * 10 ^ 70 +
        9019933563595781601865728557799570766621603800017714836307218615924190) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_161 :
    recurrence2Scalar4Exceptional.coeff 161 =
      (((533329294029196531776458223839333827542368334 * 10 ^ 70 +
        0448196135740387396705586103935622224104319844152627128192425802813788) * 10 ^ 70 +
        8178604523387638411805846949115024061070434025415896593486164663114100) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_162 :
    recurrence2Scalar4Exceptional.coeff 162 =
      -(((1180228346775362550890514396768289673162386738 * 10 ^ 70 +
        8805429705466259642060475564451405815154407552131469057869333401331755) * 10 ^ 70 +
        2930234856389331307839012985705460551523406810637939880818417819805113) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_163 :
    recurrence2Scalar4Exceptional.coeff 163 =
      (((822623550651455030426625723126731094127264503 * 10 ^ 70 +
        4767156142230889718529014704920367777248975371047614364209651042014993) * 10 ^ 70 +
        9511256229374136888694442732439026019391537797960404746908033944559932) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_164 :
    recurrence2Scalar4Exceptional.coeff 164 =
      (((5869225364075503534190792545302316950968409324 * 10 ^ 70 +
        8287469342365019378106574534147561615625729150082739550408760936569600) * 10 ^ 70 +
        5613265499946837267681541478279424257197127379928886532882960101101864) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_165 :
    recurrence2Scalar4Exceptional.coeff 165 =
      -(((32223287246742199060244721574825744179098913795 * 10 ^ 70 +
        6072302415185453928840939944730703670827721245333167298552584574792361) * 10 ^ 70 +
        6326408450807755442424609281444948288128741619758418305930291422118959) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_166 :
    recurrence2Scalar4Exceptional.coeff 166 =
      (((95944977302624596095936366228304454508025448098 * 10 ^ 70 +
        8485308041827850372185506154401688931311841010448194126122404184016786) * 10 ^ 70 +
        4289379110470542141452432125981712362230673356638473611373996476053130) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_167 :
    recurrence2Scalar4Exceptional.coeff 167 =
      -(((176986633324742252919086529221615354849271458253 * 10 ^ 70 +
        1229709952009717621472171292577904682680551253733010842479093126257968) * 10 ^ 70 +
        8684014798373672701145305870832027308790271220723842297405006701687201) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_168 :
    recurrence2Scalar4Exceptional.coeff 168 =
      (((67781824404446650073061473343701415997263287779 * 10 ^ 70 +
        5348984940040557320851138036028353849227879050036217179311309154504603) * 10 ^ 70 +
        2969403553430445706071184544148631632180286395650589516409586194155357) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_169 :
    recurrence2Scalar4Exceptional.coeff 169 =
      (((967415903576188392568541329173906168837414264491 * 10 ^ 70 +
        8206998975288990759308551455826135525527120069292952119339229354377607) * 10 ^ 70 +
        0289608250552468626285379826952186437123587534726974527787315075337798) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_170 :
    recurrence2Scalar4Exceptional.coeff 170 =
      -(((4636091135172811243700566340769049732291518570307 * 10 ^ 70 +
        8671808890837422864077272137280341967685481395822118769008355733334380) * 10 ^ 70 +
        5147990051994495552044946469204449672057926212361351307625244902937681) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_171 :
    recurrence2Scalar4Exceptional.coeff 171 =
      (((13327621581331507208860456045426666844442948752543 * 10 ^ 70 +
        8117565474119455363835454222496559349418038494854882162443168143243576) * 10 ^ 70 +
        6031390726410097877597448485663239914030620351595567287495721120308968) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_172 :
    recurrence2Scalar4Exceptional.coeff 172 =
      -(((26315463550847581510887747715675272782696523114100 * 10 ^ 70 +
        2932067619743263763002747422724331199638171979929440834786863751862213) * 10 ^ 70 +
        5771512098812693232658286887410483405689779196590028113393564689085773) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_173 :
    recurrence2Scalar4Exceptional.coeff 173 =
      (((26271053378675139741813765712104048436645159621372 * 10 ^ 70 +
        1086914656514005326243863156760297547879747876638512328829668995861386) * 10 ^ 70 +
        2431516694204645990889822962447644915012228289473626170074213881927090) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_174 :
    recurrence2Scalar4Exceptional.coeff 174 =
      (((52993042643384443339815287547750640540872659703821 * 10 ^ 70 +
        6831662694241846657240937496051163040596379288891885978187680944653024) * 10 ^ 70 +
        7589704049250867110266223855530483974010007883418614532538786513032616) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_175 :
    recurrence2Scalar4Exceptional.coeff 175 =
      -(((380658236317133240374308920648506876293053403384145 * 10 ^ 70 +
        7066370172194082565886218672517039762975255180252794185188297575023792) * 10 ^ 70 +
        9773878376616653241865632567066560219380949448142760957049367103493686) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_176 :
    recurrence2Scalar4Exceptional.coeff 176 =
      (((1272337247608290514512330380158236427538481022870104 * 10 ^ 70 +
        4405039878698030863551657935108516641513833422780571253595704000175890) * 10 ^ 70 +
        7389758390401034351005946995543647808806855471644453152219799333662641) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_177 :
    recurrence2Scalar4Exceptional.coeff 177 =
      -(((3087976792287017910715735680113839068819816116105915 * 10 ^ 70 +
        2864084696275781918953416251168586013441314727598511239578753258577998) * 10 ^ 70 +
        0829121421483397806870351393516137257816063185434837307371800127341023) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

theorem recurrence2Scalar4Exceptional_coeff_178 :
    recurrence2Scalar4Exceptional.coeff 178 =
      (((5638755302757109590208407294768122296959667611412547 * 10 ^ 70 +
        8127939440208401443772658576129838900306528929322490936584304871960643) * 10 ^ 70 +
        2608814010458154259455148025004836692889491090742935659243800150906039) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
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

private theorem recurrence2Scalar4Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_179 :
    recurrence2Scalar4Exceptional.coeff 179 =
      -(((6439200600109193859684549751103219273221511465722382 * 10 ^ 70 +
        7221249848600896116859564542132925509145301044068887415571100299565585) * 10 ^ 70 +
        8401474673340042093362956913748540549038377997756952814411945867103779) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_180 :
    recurrence2Scalar4Exceptional.coeff 180 =
      -(((3134983780158132904132246308808802018608351516907808 * 10 ^ 70 +
        1215620628344878728165227452026842148101487216368179190574052710240814) * 10 ^ 70 +
        9906762716315243541573170557993010796730181864759249656725840080710262) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 2 +
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
  rw [recurrence2Scalar4Exceptional_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_181 :
    recurrence2Scalar4Exceptional.coeff 181 =
      (((44490893873643910136757643058460236040315349724252227 * 10 ^ 70 +
        0199392853761278062740045463587602078422437682456383501406300842172621) * 10 ^ 70 +
        5797916953225812990902371822612881315441372646040620668853653889209535) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 3 +
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
  rw [recurrence2Scalar4Exceptional_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_182 :
    recurrence2Scalar4Exceptional.coeff 182 =
      -(((160302290547457073716271263587203885003612668231735181 * 10 ^ 70 +
        2285881737820373478664532318990476143517566842316453399664869084794725) * 10 ^ 70 +
        7562135478904570194278673129761318035536535802704405968935601972167232) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 4 +
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
  rw [recurrence2Scalar4Exceptional_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_183 :
    recurrence2Scalar4Exceptional.coeff 183 =
      (((419436908545940108994169647230963903889017515422257503 * 10 ^ 70 +
        9452836989017059385600632804735763053325039289436955998912671079126095) * 10 ^ 70 +
        0459490581526355514323995451806686452225088984479507537598350906811803) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 5 +
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
  rw [recurrence2Scalar4Exceptional_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_184 :
    recurrence2Scalar4Exceptional.coeff 184 =
      -(((904619718442641015502486010220207856117081941059855899 * 10 ^ 70 +
        3862231671270221480572249772370185086417967986373483729053475873730628) * 10 ^ 70 +
        1697964999831342569339244990646628005486832386188752638089475373045451) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 6 +
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
  rw [recurrence2Scalar4Exceptional_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_185 :
    recurrence2Scalar4Exceptional.coeff 185 =
      (((1657538426772314546552058344947654565351053248538805491 * 10 ^ 70 +
        5118624407651502122355279846053455699504321613674473115043549627490078) * 10 ^ 70 +
        8628959666992551254054136627651209838067403885228672361977089482360511) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 7 +
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
  rw [recurrence2Scalar4Exceptional_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_186 :
    recurrence2Scalar4Exceptional.coeff 186 =
      -(((2545928850916364645576667655374810362422610269506444205 * 10 ^ 70 +
        5572813218584460558404914257482124843606058957463684959743017616693807) * 10 ^ 70 +
        8148115687748047266986879866420788222129343653697549864420410217105485) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 8 +
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
  rw [recurrence2Scalar4Exceptional_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_187 :
    recurrence2Scalar4Exceptional.coeff 187 =
      (((3019630020200597934902864576618449205500346927841178874 * 10 ^ 70 +
        2623012392966442973589963194836230151030186544512307185012731177843317) * 10 ^ 70 +
        0336773762880902395008482676257600193991278443986993775330807443877733) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 9 +
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
  rw [recurrence2Scalar4Exceptional_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_188 :
    recurrence2Scalar4Exceptional.coeff 188 =
      -(((1755748997357214844825953459633493300807270622686699325 * 10 ^ 70 +
        8127907022251238034923647213952457382823762132587464070438165092835962) * 10 ^ 70 +
        8804457215448021172188100104620872816149375729148787781291023706975551) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 10 +
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
  rw [recurrence2Scalar4Exceptional_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_189 :
    recurrence2Scalar4Exceptional.coeff 189 =
      -(((3722957148216367642212113343166922117518645649672735849 * 10 ^ 70 +
        8609151448386649380337895539224438771838265296825114170855623364286681) * 10 ^ 70 +
        0624116939345460084092011538020421749513689028452107022531342674681788) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 11 +
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
  rw [recurrence2Scalar4Exceptional_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_190 :
    recurrence2Scalar4Exceptional.coeff 190 =
      (((17228202257237863418348721356302342473375606954972622797 * 10 ^ 70 +
        5947928711234764850355796984150883211726296864457056895843236379116745) * 10 ^ 70 +
        8239981348112863209673324324489163003192527197480263262019561723201202) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 12 +
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
  rw [recurrence2Scalar4Exceptional_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_191 :
    recurrence2Scalar4Exceptional.coeff 191 =
      -(((43473731947050633954467877240868395746846283676331124885 * 10 ^ 70 +
        6916304898241001871401222364342099334651076643943851962418271441822365) * 10 ^ 70 +
        0032319526193739442218615998505809242945119600252138483165569765309255) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 13 +
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
  rw [recurrence2Scalar4Exceptional_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_192 :
    recurrence2Scalar4Exceptional.coeff 192 =
      (((86471203383458519100515639100071236157164017440527233466 * 10 ^ 70 +
        7843442469277415279320366428034216346972726551967578334406348421882128) * 10 ^ 70 +
        2639919132831903853229269351976148704726975598253813668253452795826153) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 14 +
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
  rw [recurrence2Scalar4Exceptional_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_193 :
    recurrence2Scalar4Exceptional.coeff 193 =
      -(((146213377104431346208059574052496210859641601697825256209 * 10 ^ 70 +
        0952675553150699286179458919613352924447727244896966593704126725817109) * 10 ^ 70 +
        7109249752800191996911708234582519759108756011904597752220480724817827) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 15 +
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
  rw [recurrence2Scalar4Exceptional_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_194 :
    recurrence2Scalar4Exceptional.coeff 194 =
      (((213450193407976211440764788271997522235199445703300759981 * 10 ^ 70 +
        8807243316165643965594438735479174635298186157902938267101369425908329) * 10 ^ 70 +
        1403049153873379601733457102562860361213089324034832215053069860584300) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 16 +
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (195 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_195 :
    recurrence2Scalar4Exceptional.coeff 195 =
      -(((263157442475245668424842185599223226086539254206104732561 * 10 ^ 70 +
        1869053643901032661332080864930308399893513627053463712313704023831147) * 10 ^ 70 +
        6131358405996028195307106847329313839358152970511510023823094906834676) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 17 +
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
    rw [show 19 = 17 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (196 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_196 :
    recurrence2Scalar4Exceptional.coeff 196 =
      (((248502760688686686559644708841705411616267296557704639064 * 10 ^ 70 +
        9338373745107776563311758918417843599506756651376570873320798387967668) * 10 ^ 70 +
        5528102323623117849233082567177259023500520219134101819861639081940407) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 18 +
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
    rw [show 19 = 16 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (197 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_197 :
    recurrence2Scalar4Exceptional.coeff 197 =
      -(((98428073365564011824826114433678571532858849328848510198 * 10 ^ 70 +
        7517294409736294849729047511526874796010604075947989126845031218880589) * 10 ^ 70 +
        7794427776552535405169418787146344303495878316619654488267396289435348) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 19 +
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
    rw [show 19 = 15 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (198 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_198 :
    recurrence2Scalar4Exceptional.coeff 198 =
      -(((277207448911769398955874057330574243623669352599282221616 * 10 ^ 70 +
        0573652598271285055896675084896474067601980826718143888697965971272890) * 10 ^ 70 +
        0974155108259652576309782615080153764118894457958506081020197970677461) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 20 +
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
    rw [show 19 = 14 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (199 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_199 :
    recurrence2Scalar4Exceptional.coeff 199 =
      (((971418756180957101299512599038572722132966319218807262192 * 10 ^ 70 +
        4465670658807102221860822282011563137166673542812656202806004602578661) * 10 ^ 70 +
        3989161024549999633222128039500713466977639121053753180771064390579796) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 21 +
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
    rw [show 19 = 13 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (200 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_200 :
    recurrence2Scalar4Exceptional.coeff 200 =
      -(((2051659938405932514795905238730171107973950336276057282072 * 10 ^ 70 +
        3453202077198186703125595197621912303190074476030696474925461501853701) * 10 ^ 70 +
        6285432695776831354380930772268941944562768188127523449784212612432633) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 22 +
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
  rw [recurrence2Scalar4Exceptional_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (201 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_201 :
    recurrence2Scalar4Exceptional.coeff 201 =
      (((3522330384359744972281087240950861426186346301733842341836 * 10 ^ 70 +
        0258900584470586621361324409289564698878131136909439671463822951683408) * 10 ^ 70 +
        0456364465764334085451505761233369223552810631613567148373512509268934) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 23 +
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
    rw [show 19 = 11 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (202 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_202 :
    recurrence2Scalar4Exceptional.coeff 202 =
      -(((5286840845243382193652705389759854702617079888339165094514 * 10 ^ 70 +
        5008476882234783757270810253787357541598281050955677341416018368376227) * 10 ^ 70 +
        7676689783777010061567088154122139599116521435855343267943503897635403) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 24 +
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
    rw [show 19 = 10 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (203 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_203 :
    recurrence2Scalar4Exceptional.coeff 203 =
      (((7122561807244533584703748027190165742204744452527023701411 * 10 ^ 70 +
        5954013255641203648862783486318453701152263775809245216939489193167790) * 10 ^ 70 +
        7608654629809249781123740255992647846360222793985689201101987159738359) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 25 +
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
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (204 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_204 :
    recurrence2Scalar4Exceptional.coeff 204 =
      -(((8683482250700695774933797174154434518837714295302252030450 * 10 ^ 70 +
        6676138695782130926958597601031999811944783656165430913311574333457642) * 10 ^ 70 +
        1941245591930598508855724500916095364571979607449399198855998511987672) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 26 +
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
    rw [show 19 = 8 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (205 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_205 :
    recurrence2Scalar4Exceptional.coeff 205 =
      (((9541622888045400482724027187639224223100380547355407571831 * 10 ^ 70 +
        4054502829921648682898941310508073646067116881386492231840835553311825) * 10 ^ 70 +
        8005278154951915802762999866113269077451826277613910826268696386235100) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 27 +
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
    rw [show 19 = 7 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (206 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_206 :
    recurrence2Scalar4Exceptional.coeff 206 =
      -(((9268605263099206561811066987499165749154736045435978528040 * 10 ^ 70 +
        5984547302203980831262278650106577065705107003173781691084674837093744) * 10 ^ 70 +
        7501659314678330665166867491103581693119559681663430794814799850146164) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 28 +
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
    rw [show 19 = 6 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (207 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_207 :
    recurrence2Scalar4Exceptional.coeff 207 =
      (((7545093881043087290914634183830861911880494892548254445055 * 10 ^ 70 +
        4179492837785865483029216408547828321871185326939415779226964011716950) * 10 ^ 70 +
        2765819486462297580523780901108149460333942930100807187987684701889545) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 29 +
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
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (208 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_208 :
    recurrence2Scalar4Exceptional.coeff 208 =
      -(((4272306715210433442484308872735424477047109817493192467111 * 10 ^ 70 +
        0269666175428778691315990942112797595335231434355703445565279376489157) * 10 ^ 70 +
        3894051175330011326232772061527871447383148308727336025348920043580305) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 30 +
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
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (209 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_209 :
    recurrence2Scalar4Exceptional.coeff 209 =
      -(((348135611787495140812079446480913018284653604059776376065 * 10 ^ 70 +
        8965328951880209472715033720954310919718859454072478519965921071991266) * 10 ^ 70 +
        8726693718332823775683931373661386709862422357381575162604995216902515) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 31 +
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
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (210 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_210 :
    recurrence2Scalar4Exceptional.coeff 210 =
      (((5797499422059624264665567766971807002941017433622657724582 * 10 ^ 70 +
        2353721756925689333253146236165143804812725256810111012109936859803450) * 10 ^ 70 +
        1103929303879882200101659206734693720351558702966548005581619275146358) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 32 +
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
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (211 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_211 :
    recurrence2Scalar4Exceptional.coeff 211 =
      -(((11303921384775451023876799450134094119699238613837056807654 * 10 ^ 70 +
        1404413802688975028132497198774975948300541156832573951811461594289917) * 10 ^ 70 +
        3991752104867119758485634281804661558155533737938850172735567673815115) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 33 +
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
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (212 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_212 :
    recurrence2Scalar4Exceptional.coeff 212 =
      (((15981973015726569468511661300433570967338387075577045136778 * 10 ^ 70 +
        4290061251382911833844639859244316365919852228979259778927304159798213) * 10 ^ 70 +
        7370543345497513223430293317143612673742779791274143402856792641775010) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 34 +
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
  rw [recurrence2Scalar4Exceptional_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (213 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_213 :
    recurrence2Scalar4Exceptional.coeff 213 =
      -(((19018218408017571183934081154745843615292065405605147130175 * 10 ^ 70 +
        2054977771154128360929412047136450889703477291616332394918800294904304) * 10 ^ 70 +
        0284738124199596708120728757800617601844235319373491014121419234255498) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 35 +
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
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (214 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_214 :
    recurrence2Scalar4Exceptional.coeff 214 =
      (((19855579923513743746291350177681090057744836027476694800346 * 10 ^ 70 +
        4979682420646924411526772731965448805182876378705781939325296199672842) * 10 ^ 70 +
        6339116182863835441016423373845435079529960831597798963248441895962801) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 36 +
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
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (215 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_215 :
    recurrence2Scalar4Exceptional.coeff 215 =
      -(((18325680133337420662329403676992757014404031373825651808765 * 10 ^ 70 +
        7358946642099168737201457193682191479196826611363671109495390050622676) * 10 ^ 70 +
        4653886366759708591007521817950743536992600747998469353164882508936721) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 37 +
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
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (216 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_216 :
    recurrence2Scalar4Exceptional.coeff 216 =
      (((14691045649607999784326371017787007355760205088889332654576 * 10 ^ 70 +
        8194239976256917378442701680239241071613920687384956514944766437129215) * 10 ^ 70 +
        1054979057390052838903739333584698297827409183809704695351459267954904) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 38 +
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
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (217 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_217 :
    recurrence2Scalar4Exceptional.coeff 217 =
      -(((9584566060753889679357543140180253504725830325122748494091 * 10 ^ 70 +
        9584736767781182590535257797371868806873247977562013353921255535155324) * 10 ^ 70 +
        3907313687324623426607847004159751055403513070329942690783991299028913) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 39 +
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
  rw [recurrence2Scalar4Exceptional_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (218 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_218 :
    recurrence2Scalar4Exceptional.coeff 218 =
      (((3863454284969980283377188096789395655490692622981033804189 * 10 ^ 70 +
        2089067876185165996302626800679717802329050962010298577296477002230905) * 10 ^ 70 +
        8742965028868003520614332032549443220235052816637008745687615315212611) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 40 +
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
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (219 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_219 :
    recurrence2Scalar4Exceptional.coeff 219 =
      (((1580980924797705480744710123791640071368909661645928936646 * 10 ^ 70 +
        5171923365514235818822107623220815863604107745850226286333930859001368) * 10 ^ 70 +
        0979819724811744241862221220768269495233062069376857438525010666748819) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 41 +
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
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (220 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_220 :
    recurrence2Scalar4Exceptional.coeff 220 =
      -(((6006077437941323644480685065930613794457795717558526850884 * 10 ^ 70 +
        6531938385924799664656054505760662860015523068774365700578319547806095) * 10 ^ 70 +
        5096634436464637133573754594317006406580752854096948984362414020579760) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 42 +
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
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (221 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_221 :
    recurrence2Scalar4Exceptional.coeff 221 =
      (((8947480312828402986922632891180827522608485628562376042751 * 10 ^ 70 +
        5036139825141760313643814480927780892384772363738270583915993294771204) * 10 ^ 70 +
        8079594822625272429174392632734867001884047793638526270870383061582242) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 43 +
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
  rw [recurrence2Scalar4Exceptional_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (222 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_222 :
    recurrence2Scalar4Exceptional.coeff 222 =
      -(((10269423319194229880520883326404986677704385614345727049125 * 10 ^ 70 +
        7734646404203192577095278503144226846399676558165713268768023044120988) * 10 ^ 70 +
        3319773626819006172356894364463676348304474880624802768509348577347212) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 44 +
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (223 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_223 :
    recurrence2Scalar4Exceptional.coeff 223 =
      (((10134321802662813010263617223579950786128638634082267663589 * 10 ^ 70 +
        4708265686835933925815015844293692431047119773917405389093860856058307) * 10 ^ 70 +
        4897573822650027085357345794974237496082145330950458509388629748716239) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 45 +
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
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (224 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_224 :
    recurrence2Scalar4Exceptional.coeff 224 =
      -(((8912369251311182115322244623456193040099545239745026970485 * 10 ^ 70 +
        8321390072064130037180680202239782893264882753702245180823182241831485) * 10 ^ 70 +
        0437475997810214965099275196231361696204928775609828963939337718888007) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 46 +
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
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (225 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_225 :
    recurrence2Scalar4Exceptional.coeff 225 =
      (((7064322422984259091895334622238664619606426463937167799438 * 10 ^ 70 +
        9609885381130153001339250944355526244695293228710929078381612639480815) * 10 ^ 70 +
        9084674728125521208330596495967670772976390714335163408887585195212069) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 47 +
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
  rw [recurrence2Scalar4Exceptional_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (226 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_226 :
    recurrence2Scalar4Exceptional.coeff 226 =
      -(((5031313772558879349981628386535455786204448899318672914174 * 10 ^ 70 +
        2976715810083566383777710939794399340065602792732540867395987199157881) * 10 ^ 70 +
        1957553941836871392082621265583211986797513076964538277807201973015973) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 48 +
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
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (227 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_227 :
    recurrence2Scalar4Exceptional.coeff 227 =
      (((3156363147052915624012906863003185055262887260065674140895 * 10 ^ 70 +
        8609266369692650102598413020150336552371446613346827386349738884823792) * 10 ^ 70 +
        0174110153319859106957932739352163813460738844078898243080541124752205) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 49 +
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
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (228 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_228 :
    recurrence2Scalar4Exceptional.coeff 228 =
      -(((1648135293194997571158356728926270553708745901875360116580 * 10 ^ 70 +
        7151288392580466252009797596175441907259244726597418579240271191143970) * 10 ^ 70 +
        5827610989374421678765136566130910428557903019624231496134517052091211) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 50 +
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (229 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_229 :
    recurrence2Scalar4Exceptional.coeff 229 =
      (((583838539178580256363199143168787037339531171033897062861 * 10 ^ 70 +
        7781555156541236594691950136884195805206009298144324678464574287152015) * 10 ^ 70 +
        6103476088269012072772662329227010176865543517602031482644930218382484) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 51 +
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
  rw [recurrence2Scalar4Exceptional_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
