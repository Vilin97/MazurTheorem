/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B2_coeff_0
  recurrence4B2_coeff_1
  recurrence4B2_coeff_10
  recurrence4B2_coeff_100
  recurrence4B2_coeff_101
  recurrence4B2_coeff_102
  recurrence4B2_coeff_103
  recurrence4B2_coeff_104
  recurrence4B2_coeff_105
  recurrence4B2_coeff_106
  recurrence4B2_coeff_107
  recurrence4B2_coeff_108
  recurrence4B2_coeff_109
  recurrence4B2_coeff_11
  recurrence4B2_coeff_110
  recurrence4B2_coeff_111
  recurrence4B2_coeff_112
  recurrence4B2_coeff_113
  recurrence4B2_coeff_114
  recurrence4B2_coeff_115
  recurrence4B2_coeff_116
  recurrence4B2_coeff_117
  recurrence4B2_coeff_118
  recurrence4B2_coeff_119
  recurrence4B2_coeff_12
  recurrence4B2_coeff_120
  recurrence4B2_coeff_121
  recurrence4B2_coeff_122
  recurrence4B2_coeff_123
  recurrence4B2_coeff_124
  recurrence4B2_coeff_125
  recurrence4B2_coeff_126
  recurrence4B2_coeff_127
  recurrence4B2_coeff_128
  recurrence4B2_coeff_129
  recurrence4B2_coeff_13
  recurrence4B2_coeff_130
  recurrence4B2_coeff_131
  recurrence4B2_coeff_132
  recurrence4B2_coeff_133
  recurrence4B2_coeff_134
  recurrence4B2_coeff_135
  recurrence4B2_coeff_136
  recurrence4B2_coeff_137
  recurrence4B2_coeff_138
  recurrence4B2_coeff_139
  recurrence4B2_coeff_14
  recurrence4B2_coeff_140
  recurrence4B2_coeff_141
  recurrence4B2_coeff_142
  recurrence4B2_coeff_143
  recurrence4B2_coeff_144
  recurrence4B2_coeff_145
  recurrence4B2_coeff_146
  recurrence4B2_coeff_147
  recurrence4B2_coeff_148
  recurrence4B2_coeff_149
  recurrence4B2_coeff_15
  recurrence4B2_coeff_150
  recurrence4B2_coeff_151
  recurrence4B2_coeff_152
  recurrence4B2_coeff_153
  recurrence4B2_coeff_154
  recurrence4B2_coeff_155

attribute [local simp]
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157
  recurrence4B2_coeff_158
  recurrence4B2_coeff_159
  recurrence4B2_coeff_16
  recurrence4B2_coeff_160
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167
  recurrence4B2_coeff_168
  recurrence4B2_coeff_17
  recurrence4B2_coeff_18
  recurrence4B2_coeff_19
  recurrence4B2_coeff_2
  recurrence4B2_coeff_20
  recurrence4B2_coeff_21
  recurrence4B2_coeff_22
  recurrence4B2_coeff_23
  recurrence4B2_coeff_24
  recurrence4B2_coeff_25
  recurrence4B2_coeff_26
  recurrence4B2_coeff_27
  recurrence4B2_coeff_28
  recurrence4B2_coeff_29
  recurrence4B2_coeff_3
  recurrence4B2_coeff_30
  recurrence4B2_coeff_31
  recurrence4B2_coeff_32
  recurrence4B2_coeff_33
  recurrence4B2_coeff_34
  recurrence4B2_coeff_35
  recurrence4B2_coeff_36
  recurrence4B2_coeff_37
  recurrence4B2_coeff_38
  recurrence4B2_coeff_39
  recurrence4B2_coeff_4
  recurrence4B2_coeff_40
  recurrence4B2_coeff_41
  recurrence4B2_coeff_42
  recurrence4B2_coeff_43
  recurrence4B2_coeff_44
  recurrence4B2_coeff_45
  recurrence4B2_coeff_46
  recurrence4B2_coeff_47
  recurrence4B2_coeff_48
  recurrence4B2_coeff_49
  recurrence4B2_coeff_5
  recurrence4B2_coeff_50
  recurrence4B2_coeff_51
  recurrence4B2_coeff_52
  recurrence4B2_coeff_53
  recurrence4B2_coeff_54
  recurrence4B2_coeff_55
  recurrence4B2_coeff_56
  recurrence4B2_coeff_57
  recurrence4B2_coeff_58
  recurrence4B2_coeff_59
  recurrence4B2_coeff_6
  recurrence4B2_coeff_60
  recurrence4B2_coeff_61

attribute [local simp]
  recurrence4B2_coeff_62
  recurrence4B2_coeff_63
  recurrence4B2_coeff_64
  recurrence4B2_coeff_65
  recurrence4B2_coeff_66
  recurrence4B2_coeff_67
  recurrence4B2_coeff_68
  recurrence4B2_coeff_69
  recurrence4B2_coeff_7
  recurrence4B2_coeff_70
  recurrence4B2_coeff_71
  recurrence4B2_coeff_72
  recurrence4B2_coeff_73
  recurrence4B2_coeff_74
  recurrence4B2_coeff_75
  recurrence4B2_coeff_76
  recurrence4B2_coeff_77
  recurrence4B2_coeff_78
  recurrence4B2_coeff_79
  recurrence4B2_coeff_8
  recurrence4B2_coeff_80
  recurrence4B2_coeff_81
  recurrence4B2_coeff_82
  recurrence4B2_coeff_83
  recurrence4B2_coeff_84
  recurrence4B2_coeff_85
  recurrence4B2_coeff_86
  recurrence4B2_coeff_87
  recurrence4B2_coeff_88
  recurrence4B2_coeff_89
  recurrence4B2_coeff_9
  recurrence4B2_coeff_90
  recurrence4B2_coeff_91
  recurrence4B2_coeff_92
  recurrence4B2_coeff_93
  recurrence4B2_coeff_94
  recurrence4B2_coeff_95
  recurrence4B2_coeff_96
  recurrence4B2_coeff_97
  recurrence4B2_coeff_98
  recurrence4B2_coeff_99
  recurrence4QuotientConstant_coeff_0
  recurrence4QuotientConstant_coeff_1
  recurrence4QuotientConstant_coeff_10
  recurrence4QuotientConstant_coeff_100
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_11
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115
  recurrence4QuotientConstant_coeff_116
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118

attribute [local simp]
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_12
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122
  recurrence4QuotientConstant_coeff_123
  recurrence4QuotientConstant_coeff_124
  recurrence4QuotientConstant_coeff_125
  recurrence4QuotientConstant_coeff_126
  recurrence4QuotientConstant_coeff_127
  recurrence4QuotientConstant_coeff_128
  recurrence4QuotientConstant_coeff_129
  recurrence4QuotientConstant_coeff_13
  recurrence4QuotientConstant_coeff_130
  recurrence4QuotientConstant_coeff_131
  recurrence4QuotientConstant_coeff_132
  recurrence4QuotientConstant_coeff_133
  recurrence4QuotientConstant_coeff_134
  recurrence4QuotientConstant_coeff_135
  recurrence4QuotientConstant_coeff_136
  recurrence4QuotientConstant_coeff_137
  recurrence4QuotientConstant_coeff_138
  recurrence4QuotientConstant_coeff_139
  recurrence4QuotientConstant_coeff_14
  recurrence4QuotientConstant_coeff_140
  recurrence4QuotientConstant_coeff_141
  recurrence4QuotientConstant_coeff_142
  recurrence4QuotientConstant_coeff_143
  recurrence4QuotientConstant_coeff_144
  recurrence4QuotientConstant_coeff_145
  recurrence4QuotientConstant_coeff_146
  recurrence4QuotientConstant_coeff_147
  recurrence4QuotientConstant_coeff_148
  recurrence4QuotientConstant_coeff_149
  recurrence4QuotientConstant_coeff_15
  recurrence4QuotientConstant_coeff_150
  recurrence4QuotientConstant_coeff_151
  recurrence4QuotientConstant_coeff_152
  recurrence4QuotientConstant_coeff_153
  recurrence4QuotientConstant_coeff_154
  recurrence4QuotientConstant_coeff_155
  recurrence4QuotientConstant_coeff_156
  recurrence4QuotientConstant_coeff_157
  recurrence4QuotientConstant_coeff_158
  recurrence4QuotientConstant_coeff_159
  recurrence4QuotientConstant_coeff_16
  recurrence4QuotientConstant_coeff_160
  recurrence4QuotientConstant_coeff_161
  recurrence4QuotientConstant_coeff_162
  recurrence4QuotientConstant_coeff_163
  recurrence4QuotientConstant_coeff_164
  recurrence4QuotientConstant_coeff_165
  recurrence4QuotientConstant_coeff_166
  recurrence4QuotientConstant_coeff_167
  recurrence4QuotientConstant_coeff_168
  recurrence4QuotientConstant_coeff_169
  recurrence4QuotientConstant_coeff_17
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176

attribute [local simp]
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_18
  recurrence4QuotientConstant_coeff_180
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_19
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_2
  recurrence4QuotientConstant_coeff_20
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
  recurrence4QuotientConstant_coeff_209
  recurrence4QuotientConstant_coeff_21
  recurrence4QuotientConstant_coeff_210
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_22
  recurrence4QuotientConstant_coeff_23
  recurrence4QuotientConstant_coeff_24
  recurrence4QuotientConstant_coeff_25
  recurrence4QuotientConstant_coeff_26
  recurrence4QuotientConstant_coeff_27
  recurrence4QuotientConstant_coeff_28
  recurrence4QuotientConstant_coeff_29
  recurrence4QuotientConstant_coeff_3
  recurrence4QuotientConstant_coeff_30
  recurrence4QuotientConstant_coeff_31
  recurrence4QuotientConstant_coeff_32
  recurrence4QuotientConstant_coeff_33
  recurrence4QuotientConstant_coeff_34
  recurrence4QuotientConstant_coeff_35
  recurrence4QuotientConstant_coeff_36
  recurrence4QuotientConstant_coeff_37
  recurrence4QuotientConstant_coeff_38
  recurrence4QuotientConstant_coeff_39

attribute [local simp]
  recurrence4QuotientConstant_coeff_4
  recurrence4QuotientConstant_coeff_40
  recurrence4QuotientConstant_coeff_41
  recurrence4QuotientConstant_coeff_42
  recurrence4QuotientConstant_coeff_43
  recurrence4QuotientConstant_coeff_44
  recurrence4QuotientConstant_coeff_45
  recurrence4QuotientConstant_coeff_46
  recurrence4QuotientConstant_coeff_47
  recurrence4QuotientConstant_coeff_48
  recurrence4QuotientConstant_coeff_49
  recurrence4QuotientConstant_coeff_5
  recurrence4QuotientConstant_coeff_50
  recurrence4QuotientConstant_coeff_51
  recurrence4QuotientConstant_coeff_52
  recurrence4QuotientConstant_coeff_53
  recurrence4QuotientConstant_coeff_54
  recurrence4QuotientConstant_coeff_55
  recurrence4QuotientConstant_coeff_56
  recurrence4QuotientConstant_coeff_57
  recurrence4QuotientConstant_coeff_58
  recurrence4QuotientConstant_coeff_59
  recurrence4QuotientConstant_coeff_6
  recurrence4QuotientConstant_coeff_60
  recurrence4QuotientConstant_coeff_61
  recurrence4QuotientConstant_coeff_62
  recurrence4QuotientConstant_coeff_63
  recurrence4QuotientConstant_coeff_64
  recurrence4QuotientConstant_coeff_65
  recurrence4QuotientConstant_coeff_66
  recurrence4QuotientConstant_coeff_67
  recurrence4QuotientConstant_coeff_68
  recurrence4QuotientConstant_coeff_69
  recurrence4QuotientConstant_coeff_7
  recurrence4QuotientConstant_coeff_70
  recurrence4QuotientConstant_coeff_71
  recurrence4QuotientConstant_coeff_72
  recurrence4QuotientConstant_coeff_73
  recurrence4QuotientConstant_coeff_74
  recurrence4QuotientConstant_coeff_75
  recurrence4QuotientConstant_coeff_76
  recurrence4QuotientConstant_coeff_77
  recurrence4QuotientConstant_coeff_78
  recurrence4QuotientConstant_coeff_79
  recurrence4QuotientConstant_coeff_8
  recurrence4QuotientConstant_coeff_80
  recurrence4QuotientConstant_coeff_81
  recurrence4QuotientConstant_coeff_82
  recurrence4QuotientConstant_coeff_83
  recurrence4QuotientConstant_coeff_84
  recurrence4QuotientConstant_coeff_85
  recurrence4QuotientConstant_coeff_86
  recurrence4QuotientConstant_coeff_87
  recurrence4QuotientConstant_coeff_88
  recurrence4QuotientConstant_coeff_89
  recurrence4QuotientConstant_coeff_9
  recurrence4QuotientConstant_coeff_90
  recurrence4QuotientConstant_coeff_91
  recurrence4QuotientConstant_coeff_92
  recurrence4QuotientConstant_coeff_93
  recurrence4QuotientConstant_coeff_94
  recurrence4QuotientConstant_coeff_95
  recurrence4QuotientConstant_coeff_96
  recurrence4QuotientConstant_coeff_97

attribute [local simp]
  recurrence4QuotientConstant_coeff_98
  recurrence4QuotientConstant_coeff_99

theorem recurrence4Scalar2Second_coeff_0 :
    recurrence4Scalar2Second.coeff 0 =
      (-58110081283624854118480555109909753495552 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_1 :
    recurrence4Scalar2Second.coeff 1 =
      (322812217990679240913213129991663909694439424 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_2 :
    recurrence4Scalar2Second.coeff 2 =
      (1744299746800717689180199903581668219332980366336 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_3 :
    recurrence4Scalar2Second.coeff 3 =
      (-17374360191690494783445856547786413522640011498574784 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_4 :
    recurrence4Scalar2Second.coeff 4 =
      (52178580157867919626240581380201344059181692940181277376 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_5 :
    recurrence4Scalar2Second.coeff 5 =
      (-83738689134426836974607595293969777354170836455258915672464 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_6 :
    recurrence4Scalar2Second.coeff 6 =
      (85531441245667780327896067645199331323499574423433253766275728 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_7 :
    recurrence4Scalar2Second.coeff 7 =
      (-59785513990014649150910081830506369331041577651477707239010887400 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_8 :
    recurrence4Scalar2Second.coeff 8 =
      (29786620574334966548729391704706900025665120792010880085483191126696 : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_9 :
    recurrence4Scalar2Second.coeff 9 =
      -((1 * 10 ^ 70 +
        1465926794302609485530099327306422737142384212072487807961333056860304) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_10 :
    recurrence4Scalar2Second.coeff 10 =
      ((296 * 10 ^ 70 +
        1967065066289048725336183827425650594159195288841752045305853669757440) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_11 :
    recurrence4Scalar2Second.coeff 11 =
      ((66945 * 10 ^ 70 +
        6548869620735684225315886562132320473802880635246440248050723942954300) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_12 :
    recurrence4Scalar2Second.coeff 12 =
      -((163132437 * 10 ^ 70 +
        5438278684743379203425310164165932166331253774898497709909354014431500) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_13 :
    recurrence4Scalar2Second.coeff 13 =
      ((118106557165 * 10 ^ 70 +
        7982074781740472446167304536169282886932261025395541313821423461099004) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_14 :
    recurrence4Scalar2Second.coeff 14 =
      -((40653694539513 * 10 ^ 70 +
        6296581964710344524403304010902157123424754399583001634157088903292742) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_15 :
    recurrence4Scalar2Second.coeff 15 =
      -((5634178564552503 * 10 ^ 70 +
        2923035861169164925730792325070333104931567458207803741984234811733140) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_16 :
    recurrence4Scalar2Second.coeff 16 =
      ((14742902646052147040 * 10 ^ 70 +
        6536839008583880667653322464879683733824403902198321092678583886466582) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_17 :
    recurrence4Scalar2Second.coeff 17 =
      -((8178315865343037741791 * 10 ^ 70 +
        3574890898037461409037289083634047427752099869898076570337398261221032) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_18 :
    recurrence4Scalar2Second.coeff 18 =
      ((2041308000088218431082991 * 10 ^ 70 +
        7753396697125284729755221958077130842405232683975953617673811151697799) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_19 :
    recurrence4Scalar2Second.coeff 19 =
      ((209473467970624586763096292 * 10 ^ 70 +
        7017011419269597886539713730071876371812550116433780882712567571826999) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_20 :
    recurrence4Scalar2Second.coeff 20 =
      -((416697232225868745498349043206 * 10 ^ 70 +
        6116625386197567957227861641632450676759675445615300421124755903965313) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_21 :
    recurrence4Scalar2Second.coeff 21 =
      ((200707038879728289929038555945540 * 10 ^ 70 +
        3864326200207873915745006584286152230169761696371878712885057042046009) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_22 :
    recurrence4Scalar2Second.coeff 22 =
      -((61870918686052040709694697135466964 * 10 ^ 70 +
        9954947956573672485446651928425711728201643371425336494750977166150480) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_23 :
    recurrence4Scalar2Second.coeff 23 =
      ((13797184590713267590558558226602008209 * 10 ^ 70 +
        0111979706931211880478437182686695688658687660954769259895425215228207) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_24 :
    recurrence4Scalar2Second.coeff 24 =
      -((2246792635775128049086282640905841188106 * 10 ^ 70 +
        5276768594252947911638151276233743336050998870241254596102275889562429) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_25 :
    recurrence4Scalar2Second.coeff 25 =
      ((234106577809044693179831977664926362070213 * 10 ^ 70 +
        4183705674347292050897814274387026281466847025033546014307562703490138) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_26 :
    recurrence4Scalar2Second.coeff 26 =
      ((2297688587075095261217634267528780839043326 * 10 ^ 70 +
        2840770986893161670552802674253267717325608166192366817148677788822636) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_27 :
    recurrence4Scalar2Second.coeff 27 =
      -((9608849082258186187299392037919233599849554450 * 10 ^ 70 +
        1300672514440780053841070758790922464797428008292350499425093821577716) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_28 :
    recurrence4Scalar2Second.coeff 28 =
      ((3623309886217847225531144247618443873083220775800 * 10 ^ 70 +
        0643656982218829065771627993466420895119159691053894631817752936909054) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_29 :
    recurrence4Scalar2Second.coeff 29 =
      -((1049058571894203013780701084546510801432199259939378 * 10 ^ 70 +
        1412829735553291118925046817013623744879921663314297915899518546122277) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_30 :
    recurrence4Scalar2Second.coeff 30 =
      ((263293698774647645008102704590785198214285380526337078 * 10 ^ 70 +
        9968603347478972272750850931615048772111061523742923971848001187507123) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_31 :
    recurrence4Scalar2Second.coeff 31 =
      -((57974351029749906451370508840296715056126453675294036883 * 10 ^ 70 +
        4559088836902347437928101879764804933118510890174124975511428360679867) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_32 :
    recurrence4Scalar2Second.coeff 32 =
      ((11162782926567630335283935122721697404594872789408113882132 * 10 ^ 70 +
        8626380208732933446290264704298985011566742893013308827307629476974284) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_33 :
    recurrence4Scalar2Second.coeff 33 =
      -((1872677245970218887153055433049304594861778287362935666769128 * 10 ^ 70 +
        3221080005454578951487781109248772305372141387575502830186156311104415) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (33 - x)) = _
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_34 :
    recurrence4Scalar2Second.coeff 34 =
      ((272166003061016492058578045399058143969463215437440890167525140 * 10 ^ 70 +
        2573443317594211364934293155242020415108738759940795240211082483785397) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (34 - x)) = _
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_35 :
    recurrence4Scalar2Second.coeff 35 =
      -((33800256025267097036184407171182394940520138202051666105747721754 * 10 ^ 70 +
        6581367861611269597145326327671384225791445526051580246995084271284530) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (35 - x)) = _
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_36 :
    recurrence4Scalar2Second.coeff 36 =
      ((3462760483111482112363307098976330443980552635491030825731998742696 * 10 ^ 70 +
        6356828983086794649730609242107884099580942379949915930548328522393015) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (36 - x)) = _
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_37 :
    recurrence4Scalar2Second.coeff 37 =
      -((263067937310920808008677370361747142505381994142172325081514004637251 * 10 ^ 70 +
        3418618862198455715425682533201140324199391632583320533679732293625513) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (37 - x)) = _
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_38 :
    recurrence4Scalar2Second.coeff 38 =
      ((7786462935484278121468903632654145437110156444072975875113119786561924 * 10 ^ 70 +
        3522571943657399792953006703326746490792550181394827402312654048518357) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (38 - x)) = _
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_39 :
    recurrence4Scalar2Second.coeff 39 =
      (((183 * 10 ^ 70 +
        7651028363591259202415061937130307419842467763460198656518341420904833) * 10 ^ 70 +
        5859386990009521107766450389904485762637979924406111645767599065390071) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (39 - x)) = _
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_40 :
    recurrence4Scalar2Second.coeff 40 =
      -(((46283 * 10 ^ 70 +
        8470703364903556246910357040702608781614245803879793344064462534350110) * 10 ^ 70 +
        0042759330092533749088500621124109797772055728394282463296839044126020) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (40 - x)) = _
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_41 :
    recurrence4Scalar2Second.coeff 41 =
      (((6864620 * 10 ^ 70 +
        4531740835167869378158706358102232867116945403792762786178559951674041) * 10 ^ 70 +
        9702135795693943851264951991465165938674087346050511594120656527611449) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (41 - x)) = _
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_42 :
    recurrence4Scalar2Second.coeff 42 =
      -(((795700635 * 10 ^ 70 +
        0558909949384080654993935017502141925363412599481960376242009795023392) * 10 ^ 70 +
        6639523825102475167948826626999319401171432835608650058249946561395927) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (42 - x)) = _
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_43 :
    recurrence4Scalar2Second.coeff 43 =
      (((76795329633 * 10 ^ 70 +
        0124454066156492090898153136089000105505630534672742860551234184306959) * 10 ^ 70 +
        3077059100859378183716254067467224685378497668706851340506013465482557) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (43 - x)) = _
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_44 :
    recurrence4Scalar2Second.coeff 44 =
      -(((6230125998010 * 10 ^ 70 +
        1564339904572061841284635281651007322904833773712746030949828233120853) * 10 ^ 70 +
        7580146608579568281565718690091259796335827877309889903365893937585266) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (44 - x)) = _
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_45 :
    recurrence4Scalar2Second.coeff 45 =
      (((411275613914392 * 10 ^ 70 +
        5679454200146021015846358045365276628955211803124043910987128436138889) * 10 ^ 70 +
        5464899533185953641747142994081165186346302195946026940827795986920040) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (45 - x)) = _
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_46 :
    recurrence4Scalar2Second.coeff 46 =
      -(((19180861380290733 * 10 ^ 70 +
        0892746095250145326300398859524891507864072441948610727560166987083264) * 10 ^ 70 +
        0895238969212421067972628364163428475967903377407651927053593884784887) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (46 - x)) = _
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_47 :
    recurrence4Scalar2Second.coeff 47 =
      (((116069586896972661 * 10 ^ 70 +
        0378879890064548395606649802913228473638007563496670572082390662518020) * 10 ^ 70 +
        7320122415817647773089970276792822332033689940467193210392162333345281) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (47 - x)) = _
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_48 :
    recurrence4Scalar2Second.coeff 48 =
      (((105629127162875427312 * 10 ^ 70 +
        2151004638790522474184567691125002427049294487323368768870028405151539) * 10 ^ 70 +
        5732583726959272619903222781707197483521501431473228163376868758186068) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (48 - x)) = _
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_49 :
    recurrence4Scalar2Second.coeff 49 =
      -(((15934731581219058753990 * 10 ^ 70 +
        2975129473626052320890929679310875323419942224846442449161996614249524) * 10 ^ 70 +
        0996904045568147531676657331769212496659139015613369369484716416195062) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (49 - x)) = _
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_50 :
    recurrence4Scalar2Second.coeff 50 =
      (((1642756492153570191719066 * 10 ^ 70 +
        3482997870646649529902829322304974248493130481962924830810763999663767) * 10 ^ 70 +
        0648919870281801315090167463877105058742902817205449320779796229015549) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (50 - x)) = _
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_51 :
    recurrence4Scalar2Second.coeff 51 =
      -(((140488523310061313423472183 * 10 ^ 70 +
        8051894764767617325451257022237823088543533588428947213845960221719193) * 10 ^ 70 +
        9191849672598385160684476337614085396167931668801622050063516563009315) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (51 - x)) = _
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_52 :
    recurrence4Scalar2Second.coeff 52 =
      (((10578124192149063684498628665 * 10 ^ 70 +
        0662247927695406911375397113500248255913918992907616799545991780238298) * 10 ^ 70 +
        5798359294758098336807362789370062998867462317284014639582935385829630) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (52 - x)) = _
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_53 :
    recurrence4Scalar2Second.coeff 53 =
      -(((720404388915757985405594132284 * 10 ^ 70 +
        4072883811172550946961804116802876217358624873135053701509206147617537) * 10 ^ 70 +
        6736104255829316351269421943937963624522499698710307077157915305913922) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (53 - x)) = _
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_54 :
    recurrence4Scalar2Second.coeff 54 =
      (((45039472980699910044233668918163 * 10 ^ 70 +
        2168355746312590918077559674017304908750870725617179951115446172127843) * 10 ^ 70 +
        9809060615324957993125671968167855968033945875600089408454662023579201) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (54 - x)) = _
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_55 :
    recurrence4Scalar2Second.coeff 55 =
      -(((2609046875676393092198456022790615 * 10 ^ 70 +
        2961525743330438916771160581216703759487892012388116445542466588438494) * 10 ^ 70 +
        1016859632734986053301132709000549347152792545090542778844195843667685) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (55 - x)) = _
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_56 :
    recurrence4Scalar2Second.coeff 56 =
      (((140919746159617449607241113015498811 * 10 ^ 70 +
        3512276859051199533830188032276275124809274516066056150431088678769208) * 10 ^ 70 +
        1967970347125101163824467669104333163414717604470737509878900818264794) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (56 - x)) = _
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_57 :
    recurrence4Scalar2Second.coeff 57 =
      -(((7129037392768937231479830873703432812 * 10 ^ 70 +
        7024438433046305828713110172802655794512865247361048515105128980939868) * 10 ^ 70 +
        8322613725826643930271772791547103143173388217136672052341397898406376) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (57 - x)) = _
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_58 :
    recurrence4Scalar2Second.coeff 58 =
      (((338953750557183489936739635131581282169 * 10 ^ 70 +
        4164998340878906921839724603306392112786085642879081122476418059457952) * 10 ^ 70 +
        3385376902919782236004854007291052357075511664670254308796593376225796) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (58 - x)) = _
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_59 :
    recurrence4Scalar2Second.coeff 59 =
      -(((15186248970864459161722463751859127990158 * 10 ^ 70 +
        9566349692723231281034285822015477248312814361068282295345695570265456) * 10 ^ 70 +
        1243988373456954039792668194060175696422811598233607902276079263947098) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (59 - x)) = _
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_60 :
    recurrence4Scalar2Second.coeff 60 =
      (((642497456180382636590977347226527838186575 * 10 ^ 70 +
        0732434821268421985264710792419181172011454865932634970132929114072770) * 10 ^ 70 +
        6870227234923393407206872305785284831298217709415681759881966200994976) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (60 - x)) = _
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_61 :
    recurrence4Scalar2Second.coeff 61 =
      -(((25711646644659568902060571591110822669546436 * 10 ^ 70 +
        6408971375935208927611973358542283850231092570796776168570588172924478) * 10 ^ 70 +
        3527155024965091851100953730077126807457830798794342316502315747874808) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (61 - x)) = _
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_62 :
    recurrence4Scalar2Second.coeff 62 =
      (((974549072495923776581635931944647533772085558 * 10 ^ 70 +
        0578686238519575445763590151103781192213870654507433006943434614351008) * 10 ^ 70 +
        8786081545657127381388348331328625373882223798116093633587863997307572) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (62 - x)) = _
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_63 :
    recurrence4Scalar2Second.coeff 63 =
      -(((35022080206047026405583471441596878487837130547 * 10 ^ 70 +
        2239279753731126488637737122797329499888945798297501540638008116226788) * 10 ^ 70 +
        0354757161630703712152285974869407877134044760147572003170256775428494) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (63 - x)) = _
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_64 :
    recurrence4Scalar2Second.coeff 64 =
      (((1194193673043088320626407355329632972092608633589 * 10 ^ 70 +
        7215011523876635806302992984931197374294989602833037999140217033601712) * 10 ^ 70 +
        9634570747824321808919117555690257009803665221982258521706127137943919) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (64 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4Scalar2Second_coeff_65 :
    recurrence4Scalar2Second.coeff 65 =
      -(((38655789419423240769932163550024160678907624902733 * 10 ^ 70 +
        7554150324224186637623238749522746299589773336430189393463531676634623) * 10 ^ 70 +
        0702991254058991071851388261754255368407000461203018588700498300232747) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (65 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
