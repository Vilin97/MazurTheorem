/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
