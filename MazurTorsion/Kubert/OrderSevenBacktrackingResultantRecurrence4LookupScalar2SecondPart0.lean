/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_66 :
    recurrence4Scalar2Second.coeff 66 =
      (((1188086339929135193552618948478582658218770887070240 * 10 ^ 70 +
        0608986251142448573795834351422682847885966112042403691187766160029085) * 10 ^ 70 +
        4800913096202868718233376947494334187479201039018508299435776297131516) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (66 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_67 :
    recurrence4Scalar2Second.coeff 67 =
      -(((34667141728207446724050124909937190406161772851836180 * 10 ^ 70 +
        4830720364491576453290640065916974250554684138327148320096238680560627) * 10 ^ 70 +
        1762358556572240897642777266594263561714549541655292442832869584124505) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (67 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_68 :
    recurrence4Scalar2Second.coeff 68 =
      (((959823442557517152984234620302053185328734975210387226 * 10 ^ 70 +
        6461016291227357396413284921716174016399098930431888191884848993859027) * 10 ^ 70 +
        1555931677283544694734720266716394385478115122086562633715714935891839) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (68 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_69 :
    recurrence4Scalar2Second.coeff 69 =
      -(((25188629046204620369564242311071462007000613569831627298 * 10 ^ 70 +
        2752313975431869292936805677414521999620984015750640341143714203635785) * 10 ^ 70 +
        8394393641189768894199158517748927432434224813888173305638436761751024) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (69 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_70 :
    recurrence4Scalar2Second.coeff 70 =
      (((625423866137673611035224743176323397267396468642685479113 * 10 ^ 70 +
        1861085835236898232086819825807606153558472180965798843464106117562960) * 10 ^ 70 +
        6175197652861765166830220305009112934172664233931054752675540478656493) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (70 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_71 :
    recurrence4Scalar2Second.coeff 71 =
      -(((14650255139834851551333690296435588237958777576180902882077 * 10 ^ 70 +
        4960465201908441785485811405096212510970970213455401282323245469123878) * 10 ^ 70 +
        9316206583562314649131175746105241370187326890669954030570652701197663) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (71 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_72 :
    recurrence4Scalar2Second.coeff 72 =
      (((322264395319051118065467695344271574586139274726393509292312 * 10 ^ 70 +
        1655965811798922810073607140261510337145352064036907889532735563431378) * 10 ^ 70 +
        2356003347368869769143085667723062804132115640356758887230365180330137) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (72 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_73 :
    recurrence4Scalar2Second.coeff 73 =
      -(((6606746978101934570427934976156198793798255509100441107799432 * 10 ^ 70 +
        6118060431272698923539295883196385353035940455671435648353323339703982) * 10 ^ 70 +
        2861410591060772066748833890355222753397985452253567201616125048948404) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (73 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_74 :
    recurrence4Scalar2Second.coeff 74 =
      (((124578876348991385015863247297925451803955248721570577474870737 * 10 ^ 70 +
        1792212596022340198976914282743649959732713637684697750599225992737755) * 10 ^ 70 +
        5241726651915194935534115227856577309767021830522665943216631469932304) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (74 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_75 :
    recurrence4Scalar2Second.coeff 75 =
      -(((2106275149389905536208076263749099908678689136133942276028534961 * 10 ^ 70 +
        7155681319451105261576636606228623179679947620826164740567348756346491) * 10 ^ 70 +
        3067069613179779100968054089672557084447452596909522097370134577700731) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (75 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_76 :
    recurrence4Scalar2Second.coeff 76 =
      (((30096689252320667930372896774627823239117473601177113705616424982 * 10 ^ 70 +
        6326102035288798054758823707662825327691169607738717704780967418257241) * 10 ^ 70 +
        3841994499140168191386297731333712579086742654243990976179945085215507) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (76 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_77 :
    recurrence4Scalar2Second.coeff 77 =
      -(((297257331140007345420351625915339585101787765451419994219867750218 * 10 ^ 70 +
        5563850111570296608492071744734020310112408401503293706149767589976462) * 10 ^ 70 +
        8093032019407818014756576917801047884093518078627687514629971622715425) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (77 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_78 :
    recurrence4Scalar2Second.coeff 78 =
      -(((740035252812824005877131717189427756408101660173019551898046924038 * 10 ^ 70 +
        8969592013247523709444133290299133048656669099877206539411031094256198) * 10 ^ 70 +
        9134541476272108951996686067467105962492341910964509514632621464625943) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (78 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_79 :
    recurrence4Scalar2Second.coeff 79 =
      (((144066362585058243845745427659883409981624914691721587576982210673106 * 10 ^ 70 +
        4960721316893568006308877364093279588888005533614293556994287556241165) * 10 ^ 70 +
        2065685517086991088399551849428828781087698784557833225330023432018158) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (79 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_80 :
    recurrence4Scalar2Second.coeff 80 =
      -(((5064193354605047402782758512945269010735285755356039043145146269696583 * 10 ^ 70 +
        9409831541084856406628150248984312989389165632453393333621264532002035) * 10 ^ 70 +
        7158185250461232939343595653845987164200475865625387999835516645976017) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (80 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_81 :
    recurrence4Scalar2Second.coeff 81 =
      ((((13 * 10 ^ 70 +
        2027337073985005383037671566197647341746430155766611458988264313199447) * 10 ^ 70 +
        4369505291060253126240720339709719547069023358884550219796940392266460) * 10 ^ 70 +
        6152979027451919571247900663331841145892840346183284522923427905219320) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (81 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_82 :
    recurrence4Scalar2Second.coeff 82 =
      -((((294 * 10 ^ 70 +
        4740364294647808617766947863864506594195664789895103595757935225452399) * 10 ^ 70 +
        7413343082094074060084680983892168490092218250519731566059254489692684) * 10 ^ 70 +
        9192010704927520317000637076995803378134679575582421722373293176401808) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (82 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_83 :
    recurrence4Scalar2Second.coeff 83 =
      ((((5873 * 10 ^ 70 +
        9103014618976823436456600673949846179006008307154343078449469210767756) * 10 ^ 70 +
        8078734259493552922824459572585225160627987374140371164040415452792496) * 10 ^ 70 +
        8401447064040546198211730002525062443917609378943341562099662312207518) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (83 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_84 :
    recurrence4Scalar2Second.coeff 84 =
      -((((106479 * 10 ^ 70 +
        2543568903067150323483064921317349250248613905979938146244313399491633) * 10 ^ 70 +
        1471633930770774601122308243940645133298448857568295439878477616235740) * 10 ^ 70 +
        1737329466232096787727445906939098859206439258993690134836813828754126) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (84 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_85 :
    recurrence4Scalar2Second.coeff 85 =
      ((((1757487 * 10 ^ 70 +
        8892122588952416440306693872972049393233867620342349829331110223884186) * 10 ^ 70 +
        3308769791011938192650389819920876584102616912500922042441877921426551) * 10 ^ 70 +
        4391771130204690743093667230403198204316091037932426684946335688586584) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (85 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_86 :
    recurrence4Scalar2Second.coeff 86 =
      -((((26121012 * 10 ^ 70 +
        6478427180080693807487549582972094203510534003266578038984634296237416) * 10 ^ 70 +
        0007873470606286602397681931741053088715343162870515644605648576755730) * 10 ^ 70 +
        3189979582605137408285600159958464780350735127801177382887847708272964) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (86 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_87 :
    recurrence4Scalar2Second.coeff 87 =
      ((((337937030 * 10 ^ 70 +
        4155958236124595452629875804893246553584938385379695924387971077938770) * 10 ^ 70 +
        9093011766026378909806963918254918929840872864945080178549972653615404) * 10 ^ 70 +
        5162145254246075229665014026785691188814867360828424541925016463801390) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (87 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_88 :
    recurrence4Scalar2Second.coeff 88 =
      -((((3434389965 * 10 ^ 70 +
        0946552862816366709409819666780492282984628001352899387966925801250433) * 10 ^ 70 +
        0790026858453360070972217375414246274657352336795701179965809706914550) * 10 ^ 70 +
        7920369663656239964011202876359303887839244552852773548871665555312988) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (88 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_89 :
    recurrence4Scalar2Second.coeff 89 =
      ((((15182020997 * 10 ^ 70 +
        4308794749809329959154919967923453845203479353481520675048102443355321) * 10 ^ 70 +
        0376543540130855678917716608456766601223982561656049128023028243745740) * 10 ^ 70 +
        8034503363099568420999596512489580704942767422796329494196077555983415) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (89 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_90 :
    recurrence4Scalar2Second.coeff 90 =
      ((((459393289015 * 10 ^ 70 +
        2594671297353716302712122802426959433501796208003646259651280112010051) * 10 ^ 70 +
        8772593106864960756066494912542224320429576152605097903716692570453589) * 10 ^ 70 +
        2360163660972062218719517088635833728502332035782931885331038935735482) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (90 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_91 :
    recurrence4Scalar2Second.coeff 91 =
      -((((18466143959016 * 10 ^ 70 +
        8716069964694598542723497415947764014602026164308170660623853170466705) * 10 ^ 70 +
        9448993561639580140023492617285139543731278119867276815130857455977777) * 10 ^ 70 +
        0409450309073942605052104645091201149501413620703714897190479920420815) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (91 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_92 :
    recurrence4Scalar2Second.coeff 92 =
      ((((453520789165496 * 10 ^ 70 +
        8303335156114339212076992755662893565630916998495463901610687589765875) * 10 ^ 70 +
        4664230887147489360862037864556194346286165642299183847893189304767837) * 10 ^ 70 +
        9449184833946750499506516951057346573852745818477299596238924642396960) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (92 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_93 :
    recurrence4Scalar2Second.coeff 93 =
      -((((9242124426432472 * 10 ^ 70 +
        7078770821266662131353244714168373010277647355478016839185311353829057) * 10 ^ 70 +
        0318214910836053012710818893577117327943046018278957280976725079569887) * 10 ^ 70 +
        4885564934645430014286524362917968370170254114303239627378344003111076) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (93 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_94 :
    recurrence4Scalar2Second.coeff 94 =
      ((((168736339302323804 * 10 ^ 70 +
        7571492892887034645035643049518508496280103265413219152694199159208606) * 10 ^ 70 +
        5984135536980380105370380368636305130564620323149694144326823847833830) * 10 ^ 70 +
        9078106607620278516790264323606736028639734276314380730586173819808876) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (94 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_95 :
    recurrence4Scalar2Second.coeff 95 =
      -((((2848548734281252426 * 10 ^ 70 +
        5486698976061323115345676691622066038193611678430259423811704575015793) * 10 ^ 70 +
        6882650002997882076194732316963153838322314075646095559831008221542842) * 10 ^ 70 +
        0341897513792374086107632310235499893600256456975348460227995735442116) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (95 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_96 :
    recurrence4Scalar2Second.coeff 96 =
      ((((45196196857582199541 * 10 ^ 70 +
        3084753825052694459013247552682127693909542102889466614722210932160810) * 10 ^ 70 +
        2753163511209521959963145818424987080625041287726353150991592873682881) * 10 ^ 70 +
        3166175550175337826228550936728700803053841712725765578147128883975751) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (96 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_97 :
    recurrence4Scalar2Second.coeff 97 =
      -((((680514964267919895294 * 10 ^ 70 +
        8617318259823180121892807358661111322015839462338227730013458911993540) * 10 ^ 70 +
        5205212327352570209413595930157734456636219862568832422937121113098393) * 10 ^ 70 +
        7131016087321299394993984052063847658141119397657642087469171972767196) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (97 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_98 :
    recurrence4Scalar2Second.coeff 98 =
      ((((9784880746095259490535 * 10 ^ 70 +
        5933552742981861157159292578672333648094365103868903005418748405703523) * 10 ^ 70 +
        8850458001817866595321009770643411140431209168500026617828524148807846) * 10 ^ 70 +
        5871963336208679552836456859862164272834117325681714021327631121415334) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (98 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_99 :
    recurrence4Scalar2Second.coeff 99 =
      -((((134942765626567266982919 * 10 ^ 70 +
        4789696699047320020604305797160999631084579064398881738107475302945764) * 10 ^ 70 +
        9684881272057259262567546506398459934757732284609965720791556787448846) * 10 ^ 70 +
        3929150752571444710468873747648466275442032114788232867251114611041731) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (99 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_100 :
    recurrence4Scalar2Second.coeff 100 =
      ((((1790635693520388832422279 * 10 ^ 70 +
        4431385822732769558908366756319004180906984191979455858778089937280491) * 10 ^ 70 +
        0248423222626065940251251837400114483531321654967473841495025577547772) * 10 ^ 70 +
        4357235696632092467018825293076934926745828932717869855759435253116260) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (100 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_101 :
    recurrence4Scalar2Second.coeff 101 =
      -((((22918571574687880972988568 * 10 ^ 70 +
        7074838075844619508251018571838547804638030579933625250589919487987275) * 10 ^ 70 +
        4697411291982297261409318058232831428794783892430815758164807529342382) * 10 ^ 70 +
        3193789402571520180004391877987166998093464740973442088169023637904592) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (101 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_102 :
    recurrence4Scalar2Second.coeff 102 =
      ((((283482845132699797004307019 * 10 ^ 70 +
        5428483352412598686806089686629808823528913483319015275662138540066256) * 10 ^ 70 +
        2951988116300581518207843336680127343727360169841111596179557592148955) * 10 ^ 70 +
        8021652067665592724207087856622490812965134390275076370618129090558910) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (102 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_103 :
    recurrence4Scalar2Second.coeff 103 =
      -((((3393938060034945146249261443 * 10 ^ 70 +
        2086116311006027204241362212837532344533652018543196380554328326478080) * 10 ^ 70 +
        6711677024306394202876917284328310434444360856323711876541307756080803) * 10 ^ 70 +
        4488896253443354002144893976980916675568119102028237024679268650976535) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (103 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_104 :
    recurrence4Scalar2Second.coeff 104 =
      ((((39380684959590227017979604252 * 10 ^ 70 +
        6259243008184703510368750720309903325255888831279699715993715384894647) * 10 ^ 70 +
        8888948984231404571257473911609377364128673805572459158032922959186812) * 10 ^ 70 +
        2750418226946330967575640750901854057857338412065372935026430533020143) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (104 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_105 :
    recurrence4Scalar2Second.coeff 105 =
      -((((443346525697960534671413526816 * 10 ^ 70 +
        1834110595200410838960538786378048128266833698627149840094445536866114) * 10 ^ 70 +
        6351061142331489617492939813905386178204347071618044318014951732526376) * 10 ^ 70 +
        1612393003226185553394713995184427213837107894622876483501773150548515) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (105 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_106 :
    recurrence4Scalar2Second.coeff 106 =
      ((((4847263821306448428602718656041 * 10 ^ 70 +
        8055502938740079525231650118359210512342764614936011489325466551382117) * 10 ^ 70 +
        7016358740944232548823661936696095616491682139203065402094895883635164) * 10 ^ 70 +
        6875113206946639777546652138356382146499488666149551016968179552321557) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (106 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_107 :
    recurrence4Scalar2Second.coeff 107 =
      -((((51511520849696006536038280669475 * 10 ^ 70 +
        0556679445894859928685785064432087288339910037047855993723008901938309) * 10 ^ 70 +
        0493668897423505698423051619979016248732923316937271342910200256640730) * 10 ^ 70 +
        0683496400469447784463223946896322071316159162995789721570930603446878) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (107 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_108 :
    recurrence4Scalar2Second.coeff 108 =
      ((((532459302928519599402751338216938 * 10 ^ 70 +
        2099884479506911871858881555642092750644112660916029776020865872555799) * 10 ^ 70 +
        9764507612979758375589170779749260320209221264057472500537924103108922) * 10 ^ 70 +
        6900858045578525620773887659434119286789049263487928643023209329304664) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (108 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_109 :
    recurrence4Scalar2Second.coeff 109 =
      -((((5357096495088929647100551502304381 * 10 ^ 70 +
        8305686949989922463363820183610196819311404385893666705215085849797650) * 10 ^ 70 +
        7623895193652999212919075944480239264230287967606326013160857264676435) * 10 ^ 70 +
        0315579641799284575574083536224259519776763075912577267969421207707131) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (109 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_110 :
    recurrence4Scalar2Second.coeff 110 =
      ((((52491964365163984094204051050004938 * 10 ^ 70 +
        9251330111350944132309552970424660728353982560691071266696438060149481) * 10 ^ 70 +
        9372116296518883848207636873219574589442005314287723032385333382694790) * 10 ^ 70 +
        6651149516296704868721962289366950583772203383944144600737602399665203) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (110 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_111 :
    recurrence4Scalar2Second.coeff 111 =
      -((((501202234432557544649340939576789997 * 10 ^ 70 +
        6405099055039751841310732413261523524692500654031234095521073329501085) * 10 ^ 70 +
        6806076575690805624303970315877349230642770101095035811380462954809359) * 10 ^ 70 +
        0451623947523884250722968035056805795442231342053246961961095018204322) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (111 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_112 :
    recurrence4Scalar2Second.coeff 112 =
      ((((4665597723612261991596842509354781106 * 10 ^ 70 +
        7279279932470257830906498159921210400832840443425178807097703493266685) * 10 ^ 70 +
        0208457578307592416643103395184776894125360022338616895534277518514062) * 10 ^ 70 +
        8398493343993960482561220461307280736027700328285242645112813173272857) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (112 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_113 :
    recurrence4Scalar2Second.coeff 113 =
      -((((42362017643231985120446195332559711933 * 10 ^ 70 +
        4887088800531644391952372381856949258007416130590985961466326887353932) * 10 ^ 70 +
        7488129534112890885366626018163451741267984927697095715229440753567778) * 10 ^ 70 +
        4918204640324954379468797119852326035588159213686145526460155572567878) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (113 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_114 :
    recurrence4Scalar2Second.coeff 114 =
      ((((375325342338927330544481769100428252109 * 10 ^ 70 +
        7131373369901096741784614159377852635973123479159703268365125099883232) * 10 ^ 70 +
        6691349673044964842814911847105142780001364918713868234014546537537973) * 10 ^ 70 +
        4488174164706077928476730561664692411405583700059859881880274854699680) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (114 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_115 :
    recurrence4Scalar2Second.coeff 115 =
      -((((3246202953326465396305448031078004816272 * 10 ^ 70 +
        2514534764477998380141559861150106931038634038068400557720229963502125) * 10 ^ 70 +
        4355131266166525772591966225629569843233733716062005183981630174933887) * 10 ^ 70 +
        2453218442507881595870489065407018697371336969270876557210292487414854) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (115 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_116 :
    recurrence4Scalar2Second.coeff 116 =
      ((((27418511920547538430758836526247172449994 * 10 ^ 70 +
        3645570038449488609572357494515960794243879918981953086934803843633408) * 10 ^ 70 +
        3729487926717280805656518553645837323809188485052049476681000811307084) * 10 ^ 70 +
        7267453814635774979237036206492690541306796417236285626504931879007901) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (116 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_117 :
    recurrence4Scalar2Second.coeff 117 =
      -((((226238740504639036522822287657396386085485 * 10 ^ 70 +
        3163948655515330692088160594174557915011004045825625394405258345702065) * 10 ^ 70 +
        4103655899095554546410885210629699072753575647158277103000883251608245) * 10 ^ 70 +
        4399841967454295613625085277966145203380754411473818999345557843289069) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (117 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_118 :
    recurrence4Scalar2Second.coeff 118 =
      ((((1824277857568715956884194901178753194267920 * 10 ^ 70 +
        3179520418412672060455643331903037078135029460324370961270311743564769) * 10 ^ 70 +
        4512203115186277498301502988352615670065618169839386877826206260810885) * 10 ^ 70 +
        7515816441491318098042084659669453642030148890904467933392275097461189) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (118 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_119 :
    recurrence4Scalar2Second.coeff 119 =
      -((((14379852285551879765528573467819495739342394 * 10 ^ 70 +
        7215108065646878226611986193764829906788311543698015813194914058826462) * 10 ^ 70 +
        5374179037744682820301620849667988945587753815113385709433067934806209) * 10 ^ 70 +
        6883249220787872193154566463049528181321104806842257676002414559009809) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (119 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_120 :
    recurrence4Scalar2Second.coeff 120 =
      ((((110838083983102502372176118282031321332255946 * 10 ^ 70 +
        2560720659242003751983250118999864502087214922748724756321711537380013) * 10 ^ 70 +
        0297789233476251546606354108827791513347509768225579691733785468133576) * 10 ^ 70 +
        3413717292796954921769440118040603382461813162102087807598957051934400) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (120 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_121 :
    recurrence4Scalar2Second.coeff 121 =
      -((((835642101918079925340579338257179272199723040 * 10 ^ 70 +
        1449400151324803445235244882927805375072629658263638792830015719965167) * 10 ^ 70 +
        0081523132998966694683475183526940701460331322180477137785862581686494) * 10 ^ 70 +
        0704647232923934245768293026904276864511714257947053780433081344321659) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (121 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_122 :
    recurrence4Scalar2Second.coeff 122 =
      ((((6164080489554067023919492662849379072770863223 * 10 ^ 70 +
        7744286611376376691005392831084391344224828497929195888825308246686848) * 10 ^ 70 +
        1354850666188000133420285181097420703236632215687300969425135489833918) * 10 ^ 70 +
        8676151941998025427407070865469422931680075290941551800314847085256602) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (122 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_123 :
    recurrence4Scalar2Second.coeff 123 =
      -((((44498749567058463078665743163459370575342850679 * 10 ^ 70 +
        8135213947129707003118106548367996586956337288082390410385823570451935) * 10 ^ 70 +
        7951695709774439827208832523009069057301984388344220313118446082213195) * 10 ^ 70 +
        8630592648005092323604383338208480684699538888165741233113785466136103) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (123 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_124 :
    recurrence4Scalar2Second.coeff 124 =
      ((((314462555309080638851389768440465908177723103584 * 10 ^ 70 +
        6850350376307798037933471426560423159643286456693942761988643560960415) * 10 ^ 70 +
        3785059892584524610958323720946606631388625935441653826474429282243053) * 10 ^ 70 +
        3356289313510532519212526776014258708940723704934030901657503172731726) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (124 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_125 :
    recurrence4Scalar2Second.coeff 125 =
      -((((2175892500797444509262505325699373037132358428462 * 10 ^ 70 +
        5831655147071950317172751916628199168185244880421874126118156414005869) * 10 ^ 70 +
        4514343850324782592928103404562752296942682745665243485473222675684133) * 10 ^ 70 +
        5416837838856101705957091893906427407664810022286125370571730765823363) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (125 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_126 :
    recurrence4Scalar2Second.coeff 126 =
      ((((14745346376653907683947931974352018525862641565522 * 10 ^ 70 +
        9736368183827904764220332085769018355127230122808263821467377912484865) * 10 ^ 70 +
        3067462558458444005138229061068371133508263469035256596471688341783767) * 10 ^ 70 +
        4686490503181759099716819570324754159901704711485024542996269744645841) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (126 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_127 :
    recurrence4Scalar2Second.coeff 127 =
      -((((97885749861353806999632137078832971342721197268017 * 10 ^ 70 +
        3601368138360132929829444655096299737824267047453801143338252372162066) * 10 ^ 70 +
        4025679878325415042722482445058603220857429874979008122764802078659866) * 10 ^ 70 +
        1268589105038779041873271674660006424693895260849829174033518654368316) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (127 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_128 :
    recurrence4Scalar2Second.coeff 128 =
      ((((636685972904229379524524559785168399327379787362477 * 10 ^ 70 +
        7861835385634343718203995595602871519665171104931764199314549770537457) * 10 ^ 70 +
        4635200182194010005505230198355429520176219542150400563121558530893137) * 10 ^ 70 +
        0626010277080108850392758554450825645365974281994065134139621853509376) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (128 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_129 :
    recurrence4Scalar2Second.coeff 129 =
      -((((4058480426635912607171760613634136650689745278121381 * 10 ^ 70 +
        8455570679136819253881373411902757509838206921757591039922850404330772) * 10 ^ 70 +
        7494205043501853903875865816971519156259695259063136726361188302309799) * 10 ^ 70 +
        6166725003594539698540266308288933310365740526602348154502819990252013) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (129 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_130 :
    recurrence4Scalar2Second.coeff 130 =
      ((((25358404017510691696033621294240595781273517994422066 * 10 ^ 70 +
        4627284999189500994108820642201249743084871354590636778966111425921572) * 10 ^ 70 +
        4610335431200848370019954881922286878935098309524575983214300162097709) * 10 ^ 70 +
        0125982547001429555760659483383239182439184620442247743324363749290366) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (130 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_131 :
    recurrence4Scalar2Second.coeff 131 =
      -((((155340835702729222605850624514905018372819295462316786 * 10 ^ 70 +
        4514730978633686624923938665982693239503074148998888175862409190136192) * 10 ^ 70 +
        7365778215558646577103512051750123605383453751052105449832722369193706) * 10 ^ 70 +
        1617985594157657899959918141546301491700530379694502672667458352968866) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (131 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_132 :
    recurrence4Scalar2Second.coeff 132 =
      ((((933118489418185596948912976203127468106334948041736375 * 10 ^ 70 +
        5870792274633873119501049603209448192627966877068303570488281679414369) * 10 ^ 70 +
        6464637428423686470371990162447944299441743779056767257875277406481236) * 10 ^ 70 +
        2162727436528399917179297523871570938697415187167074786974456813996320) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (132 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_133 :
    recurrence4Scalar2Second.coeff 133 =
      -((((5497369332275514294755083413474673393530363358049312931 * 10 ^ 70 +
        5427592229614253011196030666056677263385562707050375425410338837791599) * 10 ^ 70 +
        0529182654668468463611152040580210210546140347306680485175370307395028) * 10 ^ 70 +
        8655881169601006303679449802432460814810811853767870033165190647536974) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (133 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_134 :
    recurrence4Scalar2Second.coeff 134 =
      ((((31769984285743978625343318859441327809878601342867584708 * 10 ^ 70 +
        9564356989240934847844639663149363533871172150644820046220451549587604) * 10 ^ 70 +
        0785319202243967879246777762366085970846284858011898394528529310501225) * 10 ^ 70 +
        3401189559389786904977937973686908424808175713522395729416008706731686) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (134 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_135 :
    recurrence4Scalar2Second.coeff 135 =
      -((((180134808940821470947501365448614856951041553095539798200 * 10 ^ 70 +
        1536508890182036793093747070288216482752716850572159322356109570412658) * 10 ^ 70 +
        0741776368274037963462286884263993877391879889632726748013504438183486) * 10 ^ 70 +
        0167032475084996219908705227317146592693202577977880736947928263200196) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (135 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_136 :
    recurrence4Scalar2Second.coeff 136 =
      ((((1002234017069652638571952441319834768508881974272075786151 * 10 ^ 70 +
        2908169254205600206162894320310535863191057702117678959608607458198948) * 10 ^ 70 +
        7508367980120851298225074657515548011718849788261408431883606870563503) * 10 ^ 70 +
        4036146604814320920474295383669886352850912188556367568316167889440873) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (136 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_137 :
    recurrence4Scalar2Second.coeff 137 =
      -((((5472699214431687145784748625065934970855908226889730718005 * 10 ^ 70 +
        0910129188464958054964459846352569103317624483715922156390095231774567) * 10 ^ 70 +
        1129614225589435325673388699132809990680139534224885171353167612870804) * 10 ^ 70 +
        2510844648734605000383422710971292616197548764688390972221818382207427) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (137 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_138 :
    recurrence4Scalar2Second.coeff 138 =
      ((((29333436426348903757243148293418277838276041751693745701498 * 10 ^ 70 +
        9385649524632294783008125654141447115267064135872204434716217204223042) * 10 ^ 70 +
        3671639965506065709027217966568229678697157850018023070131900247582687) * 10 ^ 70 +
        2537064804231411224077684728103972552761354160622339844132347948608633) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (138 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_139 :
    recurrence4Scalar2Second.coeff 139 =
      -((((154354459825311923069012885817593074819337610597435016662059 * 10 ^ 70 +
        6598548609819700927843512431979050600954021456856930410281697847604212) * 10 ^ 70 +
        0453037935742870974924604534821090542626796226931355629785848307004682) * 10 ^ 70 +
        1513043662802078578314291667676385795688240049066418133496629222213993) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (139 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_140 :
    recurrence4Scalar2Second.coeff 140 =
      ((((797506612735728062560019672802394793200706734487765070999605 * 10 ^ 70 +
        5035099213983802897194115949346873498166460019912698051418915216700139) * 10 ^ 70 +
        6228504759387419528860775973253042829502181571438728702317128926962798) * 10 ^ 70 +
        9633275360754025875456230575262110339765262247568963079801864916915022) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (140 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_141 :
    recurrence4Scalar2Second.coeff 141 =
      -((((4046414724033965653151902492176764147204228552420366255295635 * 10 ^ 70 +
        8792531641871198197149912630038996111396662744451223526176475991527296) * 10 ^ 70 +
        2485657512966931239541323572321775571417825840821760618497525291488361) * 10 ^ 70 +
        6734223493756201711672638212508298730383042838353381272143565560692703) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (141 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_142 :
    recurrence4Scalar2Second.coeff 142 =
      ((((20164515098520038962441575887374040814049591584144464318214494 * 10 ^ 70 +
        3242094488172151555121692875914932108262618121067098533666467930368779) * 10 ^ 70 +
        5277578256601098321973609169051559480269005620602442112985185168055192) * 10 ^ 70 +
        8502226419701178043676684862885270071682855227346794843367871388448647) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (142 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_143 :
    recurrence4Scalar2Second.coeff 143 =
      -((((98706332085755950042446802569194845919138867023280813075037620 * 10 ^ 70 +
        6820298966756314529805633553137645575745710358756346892227910484762562) * 10 ^ 70 +
        5103967371936649396576948127053431423586169741218951475534266940846002) * 10 ^ 70 +
        4707506620581240391657160589303234957586346613421408585019956416901273) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (143 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_144 :
    recurrence4Scalar2Second.coeff 144 =
      ((((474677820783567688129748399179461313423399051185408223162768074 * 10 ^ 70 +
        5982221091305307695765367889354951608083595577304098350527673189444544) * 10 ^ 70 +
        7889874985551565749615589739196523253236525428257451861382422252551670) * 10 ^ 70 +
        9534348074694182929497087379581842503654808374304108177480828275925203) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (144 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_145 :
    recurrence4Scalar2Second.coeff 145 =
      -((((2242873475405397237598090923018367800488542416750986587130465812 * 10 ^ 70 +
        7451207092853374840741841580052743242121317143450258583273980404840872) * 10 ^ 70 +
        5716753256444410452675442559850488108024189282524721600583530937535011) * 10 ^ 70 +
        9586796844953553034330647186570418002933185230822323054330107769786855) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (145 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_146 :
    recurrence4Scalar2Second.coeff 146 =
      ((((10413965718905676913871876664443315840460709455641996390158616302 * 10 ^ 70 +
        4078270598404052644134774933672821587784343900699145752287445692637013) * 10 ^ 70 +
        6720530240806940634346296908996613215774548144421406791928735982728074) * 10 ^ 70 +
        1026152624755040525703894099466501226648615127569542295511712767996413) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (146 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_147 :
    recurrence4Scalar2Second.coeff 147 =
      -((((47520951704258527895899948809378198203211454906688889384872569976 * 10 ^ 70 +
        0397714385965585010465771879145838489246788165843514764133126846465733) * 10 ^ 70 +
        7848333866315778490660547338120558904986870069786739355109170774157498) * 10 ^ 70 +
        2670613307793733658782661363647637815758657632065182519118716596388660) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (147 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_148 :
    recurrence4Scalar2Second.coeff 148 =
      ((((213138703938694147497754895984808420793901172956916062545075547675 * 10 ^ 70 +
        8178477760298723051122932218795258600068118640927167470426257366307181) * 10 ^ 70 +
        8652451679263247155831528191346619377179850141038107915804203738652400) * 10 ^ 70 +
        5482895563834839792390014016642370954956564546097347583867523998471568) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (148 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_149 :
    recurrence4Scalar2Second.coeff 149 =
      -((((939716497553435268607495019861326916931692517713195908698559149359 * 10 ^ 70 +
        6869888498854714016263849811345341648622019133723086122496627369052934) * 10 ^ 70 +
        8984985430024589772473230092854125551868779725342886670823407540650665) * 10 ^ 70 +
        0868575301654833662081009680156201703261876458793025375909734876069308) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (149 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_150 :
    recurrence4Scalar2Second.coeff 150 =
      ((((4073206658788866523911778204273267276315136104210132896594764832527 * 10 ^ 70 +
        5628831766103847281111671412980908007230685947451497530982839077213753) * 10 ^ 70 +
        6354117111943577348386131791601241903172212363606892835044518423299294) * 10 ^ 70 +
        0035843755023290354393926934024458543102076212127068199725360823781680) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (150 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_151 :
    recurrence4Scalar2Second.coeff 151 =
      -((((17359109858968852173892856778194042587511286127267871134116894513506 * 10 ^ 70 +
        8484876582196133733095152065783042432893142714639464581118286334070777) * 10 ^ 70 +
        1357321099735813689543484203965641618005334267069194671499953255394764) * 10 ^ 70 +
        2502857455390081608613579168182589319182308093437615341137211108223957) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (151 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_152 :
    recurrence4Scalar2Second.coeff 152 =
      ((((72746965893900696466705129368868556759422483445272397576115759783170 * 10 ^ 70 +
        2973680615252669568759622828585733836541597933198573914119237822955653) * 10 ^ 70 +
        5550298147564543701307510729011986067063279465360380852186342186643066) * 10 ^ 70 +
        5657659239789449623060981134616063927603623378315173016777428858602473) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (152 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_153 :
    recurrence4Scalar2Second.coeff 153 =
      -((((299807474711121626988118385901511826812878575421734877995908094215214 * 10 ^ 70 +
        1709379153934336512031789379198061321697935782508119670259973728251593) * 10 ^ 70 +
        8254416731182558780838695832743909550953781892929930772922874452053415) * 10 ^ 70 +
        5289419495063654527209426971616009498889394849625890584064573497066877) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (153 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_154 :
    recurrence4Scalar2Second.coeff 154 =
      ((((1215213572307428011942431630158983617141184110722044489670236877485173 * 10 ^ 70 +
        3638940765409059585726393608131679294195900394920506740300287857328678) * 10 ^ 70 +
        8421243204000104675516977625863162682164237703841098053308011749162969) * 10 ^ 70 +
        2036273012716367427712980823707941669565258158280825076402187180326316) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (154 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_155 :
    recurrence4Scalar2Second.coeff 155 =
      -((((4844919421082908184102158711321914980303903295909257679816296815519659 * 10 ^ 70 +
        3541976112264241802346869739606341837463644208537177842708963033096380) * 10 ^ 70 +
        0457651737666029622925377450617036049635184485356060067509496375551250) * 10 ^ 70 +
        4573856836155816515355169035679736240517299409468190180453715186851934) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (155 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_156 :
    recurrence4Scalar2Second.coeff 156 =
      (((((1 * 10 ^ 70 +
        9001343143873514160402824088546988945032789689286583266395577535900629) * 10 ^ 70 +
        8000141681388661049312784879157563321861574881232079158161306350271138) * 10 ^ 70 +
        5974361619969642604152703657888783338580455028600566034474168317249751) * 10 ^ 70 +
        3637430261807916662505368851245031931666051232146380294825543203777585) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (156 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_157 :
    recurrence4Scalar2Second.coeff 157 =
      -(((((7 * 10 ^ 70 +
        3313620333024724055013686638859485839471052806620541453559653796858124) * 10 ^ 70 +
        2932609444248122817573266895161505273327966413400090262175144449767852) * 10 ^ 70 +
        1935415195386330839624172112053422498926551820285966675586601636839752) * 10 ^ 70 +
        0639858521840403748590101816675740843024800912948058493712051264991767) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (157 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_158 :
    recurrence4Scalar2Second.coeff 158 =
      (((((27 * 10 ^ 70 +
        8307771020730729018863090747325350285042468696890238190970487810290043) * 10 ^ 70 +
        2980960255869707886248815170017857672653990838375731192287303417714579) * 10 ^ 70 +
        2456919679496768245811808895276590878672305342726061036018453297720513) * 10 ^ 70 +
        8508369899810169348659174974120446931594104894858612278224643080451320) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (158 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_159 :
    recurrence4Scalar2Second.coeff 159 =
      -(((((103 * 10 ^ 70 +
        9543959238042016690972193574948489511326502917950080230849223805081616) * 10 ^ 70 +
        2823708381434518490623669965954762548202146897833198891351601025784150) * 10 ^ 70 +
        8030217035059372112961467084062766144922355469439390383291524943841287) * 10 ^ 70 +
        9012181125609054818537834826744104935720626458045976766596935994675725) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (159 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_160 :
    recurrence4Scalar2Second.coeff 160 =
      (((((382 * 10 ^ 70 +
        0961885338739942339961124863358510675276696750457777314157359286171759) * 10 ^ 70 +
        5107269755010076065235212647242112616306877807020882660641135861788318) * 10 ^ 70 +
        6747421660194932858221932353636964511387132214601583826128375466675302) * 10 ^ 70 +
        1164159093556365848321708266482406162798485298123276246642183190605330) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (160 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_161 :
    recurrence4Scalar2Second.coeff 161 =
      -(((((1382 * 10 ^ 70 +
        1311723447273302369704166254023671303527036727304784091877642106284610) * 10 ^ 70 +
        3335284113296369697961260990832581386585810462688645940382436360699780) * 10 ^ 70 +
        5995980839877761642721279001469021133054125230418222753367874302571038) * 10 ^ 70 +
        2977451188620517098623401035799375341383680696930608863032770507961993) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (161 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_162 :
    recurrence4Scalar2Second.coeff 162 =
      (((((4920 * 10 ^ 70 +
        4618607606282418134693657858824627465073831804001899280278371678734488) * 10 ^ 70 +
        2967407598664785227450157059157825712548228939728827201508606481642027) * 10 ^ 70 +
        1056969535798771859009453877486823617196102295940111439464609716457183) * 10 ^ 70 +
        5544066918583770442219007281901237617903360029861405671305733885016928) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (162 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_163 :
    recurrence4Scalar2Second.coeff 163 =
      -(((((17241 * 10 ^ 70 +
        4919601782642287727548353093473251063420997423507623284870064716462252) * 10 ^ 70 +
        0947248614095601563703317952792250087525442034729196846873484631086929) * 10 ^ 70 +
        4969563065658037049771640773760009508120853187349995807024943221778446) * 10 ^ 70 +
        1395121582599719256397194613126772906031046899966205123421525779968855) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (163 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_164 :
    recurrence4Scalar2Second.coeff 164 =
      (((((59468 * 10 ^ 70 +
        5698670842800584941178310002303050016055180037745915332317634330316776) * 10 ^ 70 +
        1174076417165483327317137728255306861188185062190164802576937662010297) * 10 ^ 70 +
        1239482999336124338003502636527153729154101892287165116266033567033411) * 10 ^ 70 +
        2001986686427835195998216613624114512723110993453689934163319607904999) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (164 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_165 :
    recurrence4Scalar2Second.coeff 165 =
      -(((((201917 * 10 ^ 70 +
        5865810559236549735081880196589095631157126031950533897781268067961087) * 10 ^ 70 +
        6254092042765489992338522745715383808465762284242788032267584805623289) * 10 ^ 70 +
        0624448958630692393599688342923090937834116076308660849520209631495481) * 10 ^ 70 +
        6874570560734378175794925347812205228363007849012669387948923667952818) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (165 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_166 :
    recurrence4Scalar2Second.coeff 166 =
      (((((674938 * 10 ^ 70 +
        4353480722536629928611956071731199545812723120334416828801744782358190) * 10 ^ 70 +
        2303710163390392297428692620042263926670000566547788196944288536201123) * 10 ^ 70 +
        6066718885743592730407762367507271532833370060578262830964858141817171) * 10 ^ 70 +
        4859805080062088043706419205087205285286660935145290247183334657390436) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (166 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_167 :
    recurrence4Scalar2Second.coeff 167 =
      -(((((2221191 * 10 ^ 70 +
        2187289515010708930236941520015134891768883107393783230072626079580371) * 10 ^ 70 +
        9767735160735702230018332700928820523637324365365201791500174798996042) * 10 ^ 70 +
        2278072078133944505080748144152466756194854369700929109539701921578801) * 10 ^ 70 +
        1041116737069264884043898783130014522641988582690515483242403248018264) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (167 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Second_coeff_168 :
    recurrence4Scalar2Second.coeff 168 =
      (((((7197256 * 10 ^ 70 +
        6770492490552049410964052351935061190997459651895375252926647841805819) * 10 ^ 70 +
        8681648097903121426843972567770201192425232096691067588408214399297166) * 10 ^ 70 +
        2424969491955143583670274331264336397554031222809011041107294089402308) * 10 ^ 70 +
        7907794343543411960318625226424597449236192170312114243282946508997402) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (168 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (169 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_169 :
    recurrence4Scalar2Second.coeff 169 =
      -(((((22963276 * 10 ^ 70 +
        6896395356480641574934841102395014811412310383882210419343234950146069) * 10 ^ 70 +
        9531314220961993421670490877602477720932435998130917852246306075409239) * 10 ^ 70 +
        7358561540951587255939376622527814916316315214522935415505041703562701) * 10 ^ 70 +
        8158566747980086767439458461827138279245368789809798383183624594931000) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (169 - x)) = _
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
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (170 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_170 :
    recurrence4Scalar2Second.coeff 170 =
      (((((72145993 * 10 ^ 70 +
        7020129517561145946776923077863721090440312686657606567878107046958867) * 10 ^ 70 +
        3561588680186888508122187698369321684663488831088372902951395886295770) * 10 ^ 70 +
        0770811703535004255416429615851534726668511374174407903513699540424114) * 10 ^ 70 +
        9645507790310656253061317262483066256732537425134629252554112500060858) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (170 - x)) = _
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
    rw [show 11 = 9 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (171 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_171 :
    recurrence4Scalar2Second.coeff 171 =
      -(((((223216789 * 10 ^ 70 +
        9004591899046775369383943161625755057474191290742764568508594756325584) * 10 ^ 70 +
        1332170535572711976504199443451246997849652890412401108109850302865885) * 10 ^ 70 +
        3069355610501943609405918474364590819276747239510804770081544354281124) * 10 ^ 70 +
        9715684896909982537898220282741258186072002119719168155238347743628251) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (171 - x)) = _
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
    rw [show 12 = 9 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (172 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_172 :
    recurrence4Scalar2Second.coeff 172 =
      (((((680145278 * 10 ^ 70 +
        8567424314195398412790271236971789057773579009208866206731877237259536) * 10 ^ 70 +
        6925683188496765498821005872173550385500320354834036472246388338745549) * 10 ^ 70 +
        0837680879087690600912185392081906122743439516303090705108242749897390) * 10 ^ 70 +
        0151520457090932352002830953708835372718389279248223579554907303065236) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (172 - x)) = _
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
    rw [show 13 = 9 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (173 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_173 :
    recurrence4Scalar2Second.coeff 173 =
      -(((((2041078752 * 10 ^ 70 +
        7939325205842330345547882485802939338799274483386934569424235318930439) * 10 ^ 70 +
        2923443928982501163046099842201852044075255158393155947434179845265398) * 10 ^ 70 +
        9684175866087753667092935233338442665327827777928320761527787911578472) * 10 ^ 70 +
        1634535607160979698566145886704003095103398020639944048270377118981930) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (173 - x)) = _
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
    rw [show 14 = 9 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (174 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_174 :
    recurrence4Scalar2Second.coeff 174 =
      (((((6032860530 * 10 ^ 70 +
        0820404922312253598429538916908575835043398261117429524654675728518810) * 10 ^ 70 +
        9740425568477050594835156459471724051291479087270165272497152739250791) * 10 ^ 70 +
        4467074244726517990794871965357322725919240062690029636061533884007916) * 10 ^ 70 +
        6759115462197051195653293860232539506881641097473952969122956269409457) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (174 - x)) = _
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
    rw [show 15 = 9 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (175 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_175 :
    recurrence4Scalar2Second.coeff 175 =
      -(((((17563603505 * 10 ^ 70 +
        6022543973685858761843005007378436627926129442476256824578599321353318) * 10 ^ 70 +
        4778786785152908907195659164385431951776033937143480248503080382028522) * 10 ^ 70 +
        3998129843860938383204895715589988279967112998867907786937189557181763) * 10 ^ 70 +
        0522344636683539630506497301009735385318785171540545389466819637010490) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (175 - x)) = _
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
    rw [show 16 = 9 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (176 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_176 :
    recurrence4Scalar2Second.coeff 176 =
      (((((50367606776 * 10 ^ 70 +
        5839930529790621525798059305885608289466520869788116721469580457807829) * 10 ^ 70 +
        3619592314421819778172756070297723853812239420721355307592266403552073) * 10 ^ 70 +
        9505654861786175035041595822415604344348518168278363046049227991429734) * 10 ^ 70 +
        8157510248723624244441956335698754213279777505553128744731404676815231) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (176 - x)) = _
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
    rw [show 17 = 9 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (177 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_177 :
    recurrence4Scalar2Second.coeff 177 =
      -(((((142284002407 * 10 ^ 70 +
        4395710475194304402251720836321959018379332772451227430686506583689011) * 10 ^ 70 +
        6842342382372668806501768609448802536399293011707691859057859474700110) * 10 ^ 70 +
        5135640428408017102785150780852410508285481076050266159035648131069645) * 10 ^ 70 +
        7454615543416550799316237739778604481487853946729083938905538570007277) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (177 - x)) = _
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
    rw [show 18 = 9 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (178 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_178 :
    recurrence4Scalar2Second.coeff 178 =
      (((((395955878187 * 10 ^ 70 +
        8684985799396297035312906387169868860252932768272892820673626469844334) * 10 ^ 70 +
        2030816371159017724722812420678787566239070008938334887870422414776723) * 10 ^ 70 +
        7286444024872485544905439731098222725547710217208824351938526181608839) * 10 ^ 70 +
        2330648732430415488153697392221367543821073544258170639699910670377271) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (178 - x)) = _
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
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (179 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_179 :
    recurrence4Scalar2Second.coeff 179 =
      -(((((1085529341443 * 10 ^ 70 +
        0926297751641284277243233419976153423072986168920392654308650129455139) * 10 ^ 70 +
        4136497934786110903103495453484646901359373402399911433445669619811180) * 10 ^ 70 +
        6712020867553003759778765383154015794707542412071697554012318363201102) * 10 ^ 70 +
        7931002371754993064151364268486702038260889114265041347120684025520265) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (179 - x)) = _
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
    rw [show 20 = 9 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (180 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_180 :
    recurrence4Scalar2Second.coeff 180 =
      (((((2931957485719 * 10 ^ 70 +
        5238928131160108641864223219193334393506613398823734631245740298971913) * 10 ^ 70 +
        6922818962358887497462408311143531966365696957671362124995999119691557) * 10 ^ 70 +
        6316511100369888325111142432826698893957282408909285855460630078304807) * 10 ^ 70 +
        1350064350359788210648888430537321402579866755121803749798919874336061) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (180 - x)) = _
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
    rw [show 21 = 9 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (181 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_181 :
    recurrence4Scalar2Second.coeff 181 =
      -(((((7802101107919 * 10 ^ 70 +
        5912630796961496180114481702312120712471123736422241906105239234526493) * 10 ^ 70 +
        0885851191308281466731098063134555090366136986903400951962754116758463) * 10 ^ 70 +
        3158700524308182917867233166531870215476017414550198424703874314849454) * 10 ^ 70 +
        5758114549847164683948124403677533778432802265384451317476395408327017) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (181 - x)) = _
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
    rw [show 22 = 9 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (182 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_182 :
    recurrence4Scalar2Second.coeff 182 =
      (((((20455916973096 * 10 ^ 70 +
        0629142873913741583234153001464571074637191647064125912079097919038778) * 10 ^ 70 +
        3841623640518959867487261911388976518993276533037673433586043121769566) * 10 ^ 70 +
        9108773009679163326277238753968075533811789020637406365783205420714831) * 10 ^ 70 +
        2919152956687300480234750297693802418516511357049046804868283725342901) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (182 - x)) = _
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
    rw [show 23 = 9 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (183 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_183 :
    recurrence4Scalar2Second.coeff 183 =
      -(((((52843876263808 * 10 ^ 70 +
        7813323591526975818916764854412535319790543057567524518238629738021244) * 10 ^ 70 +
        4829629437654609644842684725836230461080569002397954225203284169642326) * 10 ^ 70 +
        2146993909858714758371468932498820841971461097182288795477681493312056) * 10 ^ 70 +
        0492763487448916926571660230294161484770814109063801663569149501168738) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (183 - x)) = _
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
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 9 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (184 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_184 :
    recurrence4Scalar2Second.coeff 184 =
      (((((134509442783461 * 10 ^ 70 +
        7334037551123808925758930819694774628605529798902037443375776028865613) * 10 ^ 70 +
        6567225970693174859701660623353853714296164273296091637834153487128671) * 10 ^ 70 +
        7011898528926900574567734935918464005751511940984035886047944277556314) * 10 ^ 70 +
        9235357968320824457295682617686118774476714123352665085323393954438315) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (184 - x)) = _
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
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 9 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (185 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_185 :
    recurrence4Scalar2Second.coeff 185 =
      -(((((337370041938363 * 10 ^ 70 +
        5453131464496378876638916012165115786643203741546324190589639365407774) * 10 ^ 70 +
        6389836133597014881290121130318763887727745169324822190095567887308888) * 10 ^ 70 +
        4917155047768786808408822035901178322804046357784033863034838603451878) * 10 ^ 70 +
        4647852612034019319885615535265178597114815751935950031108106779260836) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (185 - x)) = _
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 9 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (186 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_186 :
    recurrence4Scalar2Second.coeff 186 =
      (((((833812335111696 * 10 ^ 70 +
        8117978518819967472051113981491683558812017761705549918641309213284071) * 10 ^ 70 +
        2345190284639074729373605231561339377432596228118965382263073109089727) * 10 ^ 70 +
        8370237786617835917736144449839732083672667466759440698726798429563944) * 10 ^ 70 +
        4896526014817849214756302210775083907816120453350534541429989548359412) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (186 - x)) = _
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 9 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (187 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_187 :
    recurrence4Scalar2Second.coeff 187 =
      -(((((2030718717484386 * 10 ^ 70 +
        5247386039087932795072709946778889550605711275354878460055844614506098) * 10 ^ 70 +
        8687258168960562523670545774241736095132574605234392866186926122296753) * 10 ^ 70 +
        1310511763335711337713836776446711686428895230994258816087900662065942) * 10 ^ 70 +
        3569821708324448349186758016195567249393708851659999576633740279685554) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (187 - x)) = _
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
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 9 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (188 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_188 :
    recurrence4Scalar2Second.coeff 188 =
      (((((4873731978191837 * 10 ^ 70 +
        2875325943328287488856625895292737849550509920056763069584683669314984) * 10 ^ 70 +
        2644085565227781720992456494241337119068399556151032425411787015527169) * 10 ^ 70 +
        3471587473354538840947257633110372257759956268218685199767420528579290) * 10 ^ 70 +
        6366752000304747406466917519587934066060840411948777869357588871714375) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (188 - x)) = _
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
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 9 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (189 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_189 :
    recurrence4Scalar2Second.coeff 189 =
      -(((((11526934743377917 * 10 ^ 70 +
        5622252648615491893258664881148584238476888805612871636621537013267050) * 10 ^ 70 +
        4689447614345328380938918880831959011166023759260566329713985558857485) * 10 ^ 70 +
        3840273591596968480494761065110696622629976767625308351611046248068323) * 10 ^ 70 +
        3427156802308350950134154031637089186631564867995074270170589719872708) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (189 - x)) = _
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
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 9 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (190 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_190 :
    recurrence4Scalar2Second.coeff 190 =
      (((((26866765760867292 * 10 ^ 70 +
        3914245277040041693796894188214191996753947553428232749491153925191352) * 10 ^ 70 +
        5044405560318638107171622779536861075669810849155763818958067573185380) * 10 ^ 70 +
        8112715456462249434551999938986513819493767594786981622600180495241631) * 10 ^ 70 +
        9104324895962791901807252108366276683998372601975051718448685347254591) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (190 - x)) = _
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 9 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (191 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_191 :
    recurrence4Scalar2Second.coeff 191 =
      -(((((61712687556374619 * 10 ^ 70 +
        7325997529062949729314002013848140287644720491061062553104787997179010) * 10 ^ 70 +
        0576837625455929376520193472354648960975974603479023582384617255939203) * 10 ^ 70 +
        7074978045389166328436255622444187082405708642911924504239770187490509) * 10 ^ 70 +
        7269817310109984868594542686529889110469754135139515946670422011406253) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (191 - x)) = _
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
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 9 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (192 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_192 :
    recurrence4Scalar2Second.coeff 192 =
      (((((139700607647497358 * 10 ^ 70 +
        0735455864556194263341558342733505525281993976254617920531639803598128) * 10 ^ 70 +
        2928923491167283541883162542096669972839374041773660942638799130787408) * 10 ^ 70 +
        4578213046222303256023974305683304527229321265289041049787117179447742) * 10 ^ 70 +
        6868557902265917954608867646555988535185821420353964140275367736419571) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (192 - x)) = _
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
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 9 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (193 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_193 :
    recurrence4Scalar2Second.coeff 193 =
      -(((((311668713152455927 * 10 ^ 70 +
        2148202871081949923090617693563508044564864047776592747747627361936694) * 10 ^ 70 +
        3089333719811736969078794629955210903811999083322139347179594533326183) * 10 ^ 70 +
        0711359650658645442213407634869528706231821187617043150063786713483228) * 10 ^ 70 +
        8934836256088699172328652165399907171640488845320150144051359863818235) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (193 - x)) = _
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
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 9 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (194 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_194 :
    recurrence4Scalar2Second.coeff 194 =
      (((((685274465653650451 * 10 ^ 70 +
        0687732969787357079974124509879077822935692621810372381699191491733496) * 10 ^ 70 +
        7941406161795039555449849605693578531000381471539168343336659354389013) * 10 ^ 70 +
        1899477677342195659536347458981227812778276835618340322356384668164330) * 10 ^ 70 +
        4334837457156654064844065783784060917949829940764638886599496374474978) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (194 - x)) = _
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 9 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (195 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_195 :
    recurrence4Scalar2Second.coeff 195 =
      -(((((1484966567276350065 * 10 ^ 70 +
        5049254221399608906614115834970508288544908662157855304720761080776219) * 10 ^ 70 +
        9907637554984644415787993036831813721193191618607804567711016774510404) * 10 ^ 70 +
        9348876506772230264123328637402624868043638156036401375268385328827006) * 10 ^ 70 +
        7955733833881013523799163196768125859437039360792289620054626236143754) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (195 - x)) = _
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
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 9 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (196 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_196 :
    recurrence4Scalar2Second.coeff 196 =
      (((((3171413771574968235 * 10 ^ 70 +
        8890148570598250493071859419636631736014829339222492634018657819436538) * 10 ^ 70 +
        7252458663297939434909324108975679325770002984367120212376498562784110) * 10 ^ 70 +
        0704523188140973814694086470786590201699827282127734412240135014881032) * 10 ^ 70 +
        8364278100045485414011665410118013248399597941238625615361499762579773) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (196 - x)) = _
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (197 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_197 :
    recurrence4Scalar2Second.coeff 197 =
      -(((((6675372225939336358 * 10 ^ 70 +
        8892705635622491064825197938999781747171404048103506520923620565850883) * 10 ^ 70 +
        6418988993967919661536507794045485287282463783775043249176078144158708) * 10 ^ 70 +
        1010870656198812204951747326395790109034954714875036757731982642598953) * 10 ^ 70 +
        2001155143911526993049721529574377862654860086498698862186824459078299) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (197 - x)) = _
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
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 9 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (198 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_198 :
    recurrence4Scalar2Second.coeff 198 =
      (((((13847951360760626321 * 10 ^ 70 +
        1597343200386334933138593658061109402957715366805179150011168171980043) * 10 ^ 70 +
        7945371579145089956272886692591908202053551376702060861323639382159475) * 10 ^ 70 +
        5337285192613649300335437861610113660804327076777952171390700188903726) * 10 ^ 70 +
        2521193218724192830823667042311203298272836015978304834264157847950750) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (198 - x)) = _
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
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 9 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (199 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_199 :
    recurrence4Scalar2Second.coeff 199 =
      -(((((28312809271627582405 * 10 ^ 70 +
        8199338386998475560806305259836434785503488799117417690821039997927149) * 10 ^ 70 +
        7992742226228972949581556039719381525606277729530297817752377094281793) * 10 ^ 70 +
        5371188200039524677075325110130779937473342552706747881852857147835527) * 10 ^ 70 +
        4212861118343899363161599933849948569581363532979419991466808252110379) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (199 - x)) = _
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
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 9 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (200 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_200 :
    recurrence4Scalar2Second.coeff 200 =
      (((((57051421445719341199 * 10 ^ 70 +
        5629812791199478404466243321359794430640938231786869523065551105130646) * 10 ^ 70 +
        8643589979573198572133801496920664105209378657191921400964837266338821) * 10 ^ 70 +
        3213553874550815205279455068729479630231475382731543343056892465327505) * 10 ^ 70 +
        2576136345411156082627767537022414345964898243711993676073897552904124) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (200 - x)) = _
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
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 9 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (201 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_201 :
    recurrence4Scalar2Second.coeff 201 =
      -(((((113300911988694870162 * 10 ^ 70 +
        1343854555088590802471966048463163860345781931637106370309381429385900) * 10 ^ 70 +
        2021108081529226554354109958558355957319796209941898239971310416556097) * 10 ^ 70 +
        7839124306267874553520488092340497699017401540797898777712591173906988) * 10 ^ 70 +
        8576480151380873485089324018229319472953713027970644995983006607334386) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (201 - x)) = _
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
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 9 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (202 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_202 :
    recurrence4Scalar2Second.coeff 202 =
      (((((221758218750791532100 * 10 ^ 70 +
        2232582985068870672762340346622991021076245216851823094162291476333518) * 10 ^ 70 +
        9891757123789427678944220328342864272225578023656095630271312072500598) * 10 ^ 70 +
        6614817562968331569890293228477497314640268124778191538589673542143752) * 10 ^ 70 +
        0948751779309164920304413275511232726284345560755400073454716489906617) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (202 - x)) = _
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
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 9 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (203 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_203 :
    recurrence4Scalar2Second.coeff 203 =
      -(((((427759711881343102765 * 10 ^ 70 +
        9731564162659130280018145341932097856770406578564220783121808612327447) * 10 ^ 70 +
        7952622408807118111106646948589525101715306305897459178043900852395197) * 10 ^ 70 +
        8684744017107067374532408429598465367080876691697428221969246967874562) * 10 ^ 70 +
        6285156747604356863725182998793470953641407995329043188372284616206019) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (203 - x)) = _
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
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 9 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (204 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_204 :
    recurrence4Scalar2Second.coeff 204 =
      (((((813180044468260105113 * 10 ^ 70 +
        9369885727075235924419205448550340992921191970685170287076857935130367) * 10 ^ 70 +
        1665691561113388069829709448136416566333790672643973093068753986990380) * 10 ^ 70 +
        9695842647314086468510412829975129686574070998791356520336067267260125) * 10 ^ 70 +
        7239305927526976435473606098232234603873295657679457242395727414227695) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (204 - x)) = _
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 9 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (205 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_205 :
    recurrence4Scalar2Second.coeff 205 =
      -(((((1523460996949468429561 * 10 ^ 70 +
        7611055501692692876005197661792039857219607642543072947231544731982588) * 10 ^ 70 +
        5797630165276635639122246894791362535373672580330185749190554902140036) * 10 ^ 70 +
        8949745399645635852779242823927435567542759346838142473573354211891580) * 10 ^ 70 +
        5291489350247735705813671855637926736376061869060666644609075299229016) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (205 - x)) = _
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
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 9 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (206 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_206 :
    recurrence4Scalar2Second.coeff 206 =
      (((((2812697348341088543075 * 10 ^ 70 +
        2021133283366201346821019174521898853239608533073685028187776876039305) * 10 ^ 70 +
        2676044087887793722248375526019733888576214451719029890016790181611613) * 10 ^ 70 +
        2192666607153638874955501443622749109261141918121151098079658766741931) * 10 ^ 70 +
        5570720017784267337614669919459617153774531648761583024598246904207653) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (206 - x)) = _
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
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 9 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (207 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_207 :
    recurrence4Scalar2Second.coeff 207 =
      -(((((5117394676927073910549 * 10 ^ 70 +
        2546181117708236738513489217464705080630481708655024626015552048739193) * 10 ^ 70 +
        3248990690859208812842893217306397621338452876863445733476575207094495) * 10 ^ 70 +
        5932397323013596859675650155368329979076686727955959227115012845798462) * 10 ^ 70 +
        2917630997617728422948392833124024079964457728412987893585449713765076) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (207 - x)) = _
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
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 9 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (208 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_208 :
    recurrence4Scalar2Second.coeff 208 =
      (((((9174746195036349656077 * 10 ^ 70 +
        8281146785276939880390886303061189042905323570310023207789714959349905) * 10 ^ 70 +
        6974839929804962777127689953155369915349588769632305684672773666271626) * 10 ^ 70 +
        8919178318318677923341889755123610531331733390986674379743519575925520) * 10 ^ 70 +
        2330985266219640745025354594109407412652977250547534661371276235821392) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (208 - x)) = _
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 9 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (209 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_209 :
    recurrence4Scalar2Second.coeff 209 =
      -(((((16208431884267178277318 * 10 ^ 70 +
        8764122045821344751416273221363342359124476202262460764515115869497771) * 10 ^ 70 +
        0309096496703398502382674275011783753513350771999068596935871416337043) * 10 ^ 70 +
        5796664762159442581667728253643542634469241142968965598829250969829791) * 10 ^ 70 +
        9371768420826108956197832975465220376168201391933979297471472857561649) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (209 - x)) = _
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
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 9 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (210 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_210 :
    recurrence4Scalar2Second.coeff 210 =
      (((((28214321764309905233662 * 10 ^ 70 +
        5902686410678378816636810419367445329827839355251504866682083573906403) * 10 ^ 70 +
        0909011988906104102917623564137146036948643093526004985636307084615169) * 10 ^ 70 +
        1334138360813142285593857224588412667138492253537943752916221573496379) * 10 ^ 70 +
        5232265198828707784538014544639573902908969560214347864192394428443332) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (210 - x)) = _
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (211 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_211 :
    recurrence4Scalar2Second.coeff 211 =
      -(((((48390132638288227902049 * 10 ^ 70 +
        6958594310975560806478011701813604567059822051678132592716941734255519) * 10 ^ 70 +
        0913800181524071101807427646358346419783295027028818896034557037548108) * 10 ^ 70 +
        7216342427563092771954871619499491292315959082274552550094524984927077) * 10 ^ 70 +
        8244926480726151420971049960974085917144582539464752217269307149705433) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (211 - x)) = _
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
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 9 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (212 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_212 :
    recurrence4Scalar2Second.coeff 212 =
      (((((81766648684862995283599 * 10 ^ 70 +
        6569393581995608273344664225100444587185525081782349380997104096530400) * 10 ^ 70 +
        1946158537973988122430477918631609644856609440002040648232327043594246) * 10 ^ 70 +
        7750498530867661786744835728428965135107125174038136060607191626026088) * 10 ^ 70 +
        1044153685157033454992648361272445139267616691543578734373511709836241) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (212 - x)) = _
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
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 9 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (213 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_213 :
    recurrence4Scalar2Second.coeff 213 =
      -(((((136112395269813046014165 * 10 ^ 70 +
        2289881853891344894417686208598955726302816850169607155476007415959182) * 10 ^ 70 +
        2904223817385666082450630431216758695160914932634921549312101723026530) * 10 ^ 70 +
        5170582538851987427392577964122652878820476014377090075412648899663461) * 10 ^ 70 +
        5985888619917089701023833323810168748941645099509472423782867653205261) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (213 - x)) = _
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
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 9 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (214 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_214 :
    recurrence4Scalar2Second.coeff 214 =
      (((((223196299376592521190681 * 10 ^ 70 +
        1636736487816946343940175387989508495363580501757640915589767322314357) * 10 ^ 70 +
        0333947863820557247486563888407337681806575305609905610950320254045300) * 10 ^ 70 +
        0802942307994358994579606021010740756667194834679051963696939976876150) * 10 ^ 70 +
        5541161033667689364905344974732223050847111933586492779147514933663848) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (214 - x)) = _
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
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 9 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (215 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_215 :
    recurrence4Scalar2Second.coeff 215 =
      -(((((360499911778597616071713 * 10 ^ 70 +
        0158849365133044347891343735449423757348036300878284891999074837321594) * 10 ^ 70 +
        5056097945360680070616313685652250538519467899127755286775271499514970) * 10 ^ 70 +
        0967329602127643598781692058104374529041542264875770897452587607444697) * 10 ^ 70 +
        0196470809754470606488414672878602325694622433045548336540149749131636) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (215 - x)) = _
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
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 9 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (216 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_216 :
    recurrence4Scalar2Second.coeff 216 =
      (((((573466231107560592523791 * 10 ^ 70 +
        1898487076734113320928895857873415722679664038510600413415555617440787) * 10 ^ 70 +
        6312868604954235752822991860555975642478100340353253206175458327622653) * 10 ^ 70 +
        0906298606917841640678924341129128048564330067481731076308969498501481) * 10 ^ 70 +
        5927092153193701803615505988174420289467926980188372867057264587855821) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (216 - x)) = _
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
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 9 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
