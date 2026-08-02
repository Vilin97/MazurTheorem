/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60

attribute [local simp]
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
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

attribute [local simp]
  recurrence4QuotientConstant_coeff_118
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
  recurrence4QuotientConstant_coeff_18
  recurrence4QuotientConstant_coeff_19
  recurrence4QuotientConstant_coeff_2
  recurrence4QuotientConstant_coeff_20
  recurrence4QuotientConstant_coeff_21
  recurrence4QuotientConstant_coeff_22

attribute [local simp]
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

attribute [local simp]
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
  recurrence4QuotientConstant_coeff_98
  recurrence4QuotientConstant_coeff_99

private theorem recurrence4Scalar1Second_coeff_0_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (0 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (0 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_0 :
    recurrence4Scalar1Second.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (0 - x)) = _
  rw [show 1 = 1 +
    0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_0_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_1_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (1 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (1 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_1 :
    recurrence4Scalar1Second.coeff 1 =
      (-23258498993769499515486843778796935654080512 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (1 - x)) = _
  rw [show 2 = 1 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_1_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_2_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (2 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (2 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_2 :
    recurrence4Scalar1Second.coeff 2 =
      (43343313797901907018939542499351105956102348800 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (2 - x)) = _
  rw [show 3 = 1 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_2_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_3_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (3 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (3 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_3 :
    recurrence4Scalar1Second.coeff 3 =
      (796597013113031302361269243973936816112924614245504 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (3 - x)) = _
  rw [show 4 = 1 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_3_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_4_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (4 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (4 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_4 :
    recurrence4Scalar1Second.coeff 4 =
      (-3922660850047364316643640564165730230850625169062068384 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (4 - x)) = _
  rw [show 5 = 1 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_4_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_5_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (5 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (5 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_5 :
    recurrence4Scalar1Second.coeff 5 =
      (8629628332779613448579122407978770435762855384161926343072 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (5 - x)) = _
  rw [show 6 = 1 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_5_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_6_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (6 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (6 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_6 :
    recurrence4Scalar1Second.coeff 6 =
      (-11198717867188625909517053141347385330792438431788356252516968 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (6 - x)) = _
  rw [show 7 = 1 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_6_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_7_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (7 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (7 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_7 :
    recurrence4Scalar1Second.coeff 7 =
      (9105915855745081354232097627611180923714547852947266504964234368 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (7 - x)) = _
  rw [show 8 = 1 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_7_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_8_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (8 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (8 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_8 :
    recurrence4Scalar1Second.coeff 8 =
      (-4233315028703934316901376589418998724620202660473017114961692280080 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (8 - x)) = _
  rw [show 9 = 1 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_8_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_9_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (9 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (9 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_9 :
    recurrence4Scalar1Second.coeff 9 =
      (339148560301988707501224831380727688080114693939942651697981818909992 : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (9 - x)) = _
  rw [show 10 = 1 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_9_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_10_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (10 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (10 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_10 :
    recurrence4Scalar1Second.coeff 10 =
      ((92 * 10 ^ 70 +
        5461615694163654284441100063810557462543812386493163732144891339761352) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (10 - x)) = _
  rw [show 11 = 1 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_10_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_11_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (11 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (11 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_11 :
    recurrence4Scalar1Second.coeff 11 =
      -((60007 * 10 ^ 70 +
        7296035836807923124828322872795499023111959981741561812985104272439980) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (11 - x)) = _
  rw [show 12 = 1 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_11_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_12_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (12 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (12 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_12 :
    recurrence4Scalar1Second.coeff 12 =
      ((6373948 * 10 ^ 70 +
        0167943696378537555737891554122516745342987878920722647867687272271236) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (12 - x)) = _
  rw [show 13 = 1 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_12_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_13_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (13 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (13 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_13 :
    recurrence4Scalar1Second.coeff 13 =
      ((14143561579 * 10 ^ 70 +
        0078114755590490924122292716303587061586468721244704989027444397476622) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (13 - x)) = _
  rw [show 14 = 1 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_13_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_14_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (14 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (14 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_14 :
    recurrence4Scalar1Second.coeff 14 =
      -((10715051710589 * 10 ^ 70 +
        2410454001469608552169500898183886889711982793467374231576783592994394) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (14 - x)) = _
  rw [show 15 = 1 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_14_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_15_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (15 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (15 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_15 :
    recurrence4Scalar1Second.coeff 15 =
      ((3457874017127725 * 10 ^ 70 +
        3738250729115014501882085716661963447779846883062901610874217556535156) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (15 - x)) = _
  rw [show 16 = 1 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_15_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_16_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (16 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (16 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_16 :
    recurrence4Scalar1Second.coeff 16 =
      -((78952199732126044 * 10 ^ 70 +
        8126084039860486055430307372784442522255385782338054128797334892263110) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (16 - x)) = _
  rw [show 17 = 1 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_16_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_17_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (17 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (17 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_17 :
    recurrence4Scalar1Second.coeff 17 =
      -((418384238643930457685 * 10 ^ 70 +
        8224586052848214960997116935261680137081466458699440392680330997649000) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (17 - x)) = _
  rw [show 18 = 1 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_17_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_18_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (18 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (18 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_18 :
    recurrence4Scalar1Second.coeff 18 =
      ((164338580131879063266575 * 10 ^ 70 +
        0232038197382250709606870028695162184568311083484554631453828452409057) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (18 - x)) = _
  rw [show 19 = 1 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_18_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_19_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (19 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (19 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_19 :
    recurrence4Scalar1Second.coeff 19 =
      ((255419694450834122595886 * 10 ^ 70 +
        7094315998870935160539476233467841448694934178345524435934353663521146) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (19 - x)) = _
  rw [show 20 = 1 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_19_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_20_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (20 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (20 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_20 :
    recurrence4Scalar1Second.coeff 20 =
      -((28724500340295172723213284655 * 10 ^ 70 +
        3060739998792037546276316163260642967232584940785252394615439289663161) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (20 - x)) = _
  rw [show 21 = 1 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_20_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_21_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (21 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (21 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_21 :
    recurrence4Scalar1Second.coeff 21 =
      ((16201389799189513301481550840285 * 10 ^ 70 +
        5327067933749524782024727463677977945190493617685600301817758956676013) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (21 - x)) = _
  rw [show 22 = 1 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_21_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_22_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (22 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (22 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_22 :
    recurrence4Scalar1Second.coeff 22 =
      -((5498464001908456301952592294634542 * 10 ^ 70 +
        0513368429014424606339040576805966506316858837716049438602925999737205) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (22 - x)) = _
  rw [show 23 = 1 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_22_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_23_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (23 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (23 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_23 :
    recurrence4Scalar1Second.coeff 23 =
      ((1327790307220918242304386687329358709 * 10 ^ 70 +
        7065162077634345582460492223723753016587105423146823739103707609579207) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (23 - x)) = _
  rw [show 24 = 1 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_23_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_24_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (24 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (24 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_24 :
    recurrence4Scalar1Second.coeff 24 =
      -((233669642040000239752510547829835243965 * 10 ^ 70 +
        6684721157230454052218714618864769294225871535022409935566672541693116) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (24 - x)) = _
  rw [show 25 = 1 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_24_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_25_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (25 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (25 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_25 :
    recurrence4Scalar1Second.coeff 25 =
      ((27169623390358290231678160941600571464806 * 10 ^ 70 +
        1019318360619824668961194962513231974589930252909958525583506512912119) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (25 - x)) = _
  rw [show 26 = 1 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_25_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_26_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (26 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (26 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_26 :
    recurrence4Scalar1Second.coeff 26 =
      -((509497992788664404885190792510403617236057 * 10 ^ 70 +
        0690776184265672912249546825546606741884443035476320300665474010879825) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (26 - x)) = _
  rw [show 27 = 1 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_26_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_27_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (27 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (27 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_27 :
    recurrence4Scalar1Second.coeff 27 =
      -((827204639002434422403624426038237894797020099 * 10 ^ 70 +
        7547270687262527342452132450454657024885375737541838636359032520013734) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (27 - x)) = _
  rw [show 28 = 1 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_27_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_28_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (28 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (28 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_28 :
    recurrence4Scalar1Second.coeff 28 =
      ((330728999718793919558036573691826458104195608123 * 10 ^ 70 +
        0729837500106668071642770887982763320654898339937027444901429213241086) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (28 - x)) = _
  rw [show 29 = 1 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_28_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_29_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (29 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (29 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_29 :
    recurrence4Scalar1Second.coeff 29 =
      -((96913528217298798485252249105455410780076491239079 * 10 ^ 70 +
        4658487137992241157582182615006278992174368756156651759593389733151452) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (29 - x)) = _
  rw [show 30 = 1 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_29_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_30_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (30 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (30 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_30 :
    recurrence4Scalar1Second.coeff 30 =
      ((24703552422366824045958441724750343720424124460911411 * 10 ^ 70 +
        5717371477819386348980609126388792325092401721159969217339067753107527) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (30 - x)) = _
  rw [show 31 = 1 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_30_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_31_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (31 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (31 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_31 :
    recurrence4Scalar1Second.coeff 31 =
      -((5567922160777240612024869251806276424944154059688496221 * 10 ^ 70 +
        1375903069155677863846579537202812158706831305317917540671188257795667) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (31 - x)) = _
  rw [show 32 = 1 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_31_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_32_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (32 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (32 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_32 :
    recurrence4Scalar1Second.coeff 32 =
      ((1100611286117814183351360718204609957344575312064278222814 * 10 ^ 70 +
        0462996910090575003768419274527639040746470279821772409224477019124982) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (32 - x)) = _
  rw [show 33 = 1 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_32_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_33_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (33 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (33 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_33 :
    recurrence4Scalar1Second.coeff 33 =
      -((189105106315087707807414363115397346596869051863459773211006 * 10 ^ 70 +
        8676472136776161698934869867929676648501975176027625408029837675709370) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (33 - x)) = _
  rw [show 34 = 1 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_33_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_34_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (34 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (34 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_34 :
    recurrence4Scalar1Second.coeff 34 =
      ((27941247037242231791573673887983842731517305096099934571899850 * 10 ^ 70 +
        7048949741234522462899232726753255443314358697018140131793220413297616) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (34 - x)) = _
  rw [show 35 = 1 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_34_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_35_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (35 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (35 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_35 :
    recurrence4Scalar1Second.coeff 35 =
      -((3474627229158903459562894486110169773301032506810156281741548701 * 10 ^ 70 +
        4739041949271994557907141551814254680319409319751136423958118656284094) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (35 - x)) = _
  rw [show 36 = 1 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_35_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_36_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (36 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (36 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_36 :
    recurrence4Scalar1Second.coeff 36 =
      ((343823498238018294142636579208666831870372227239892821029467225400 * 10 ^ 70 +
        8571518117031868299680930868132375247707182781415750129916178900430194) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (36 - x)) = _
  rw [show 37 = 1 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_36_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_37_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (37 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (37 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_37 :
    recurrence4Scalar1Second.coeff 37 =
      -((22037786149526422758256845730808790839495396525607827596966076393097 * 10 ^ 70 +
        5856383215275812040229624263259492809931748845363236292288360980450493) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (37 - x)) = _
  rw [show 38 = 1 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_37_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_38_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (38 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (38 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_38 :
    recurrence4Scalar1Second.coeff 38 =
      -((440875861552979054781595186611970014021216969867033210446120243276461 * 10 ^ 70 +
        6220705092555797675672563592884002158966099797971758497548978319459956) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (38 - x)) = _
  rw [show 39 = 1 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_38_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_39_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (39 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (39 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_39 :
    recurrence4Scalar1Second.coeff 39 =
      (((42 * 10 ^ 70 +
        2680529105777972016788837601100053055671964557958456961158411611822837) * 10 ^ 70 +
        5036530181217493538682918768511384347298208622791157768164521575490899) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (39 - x)) = _
  rw [show 40 = 1 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_39_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_40_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (40 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (40 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_40 :
    recurrence4Scalar1Second.coeff 40 =
      -(((8379 * 10 ^ 70 +
        0943226556339050985571177308525741722752672810969093410255224603788549) * 10 ^ 70 +
        4755132181961535622475276186766633509497791877933799323559104083904774) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (40 - x)) = _
  rw [show 41 = 1 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_40_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_41_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (41 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (41 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_41 :
    recurrence4Scalar1Second.coeff 41 =
      (((1183985 * 10 ^ 70 +
        1862418431534282183801819317178978587395675367912189150704076422004818) * 10 ^ 70 +
        9260661108304850873176546808403734310113429783634871279248098356212467) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (41 - x)) = _
  rw [show 42 = 1 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_41_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_42_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (42 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (42 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_42 :
    recurrence4Scalar1Second.coeff 42 =
      -(((136587737 * 10 ^ 70 +
        1079656294665858199465814854359055763946277051851989773255624190591066) * 10 ^ 70 +
        8898267274830768364787578500478516831921538704839989463023593312110186) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (42 - x)) = _
  rw [show 43 = 1 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_42_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_43_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (43 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (43 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_43 :
    recurrence4Scalar1Second.coeff 43 =
      (((13363487203 * 10 ^ 70 +
        8286923521390587419696826038979206867485940757149421573026899271581446) * 10 ^ 70 +
        3326065058703710542354145729876101165051585645002578144991043352423510) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (43 - x)) = _
  rw [show 44 = 1 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_43_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_44_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (44 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (44 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_44 :
    recurrence4Scalar1Second.coeff 44 =
      -(((1112547353141 * 10 ^ 70 +
        6539308356060534532707328564040357918896144026985132031756301721586544) * 10 ^ 70 +
        6813106742093882073397658074474184053112171269467712299358058191789041) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (44 - x)) = _
  rw [show 45 = 1 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_44_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_45_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (45 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (45 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_45 :
    recurrence4Scalar1Second.coeff 45 =
      (((76512717934902 * 10 ^ 70 +
        1838650413993188565574636135945774568975679219672204198091478585022106) * 10 ^ 70 +
        3295769244953011526217595402327295823844756278080803277370262479693703) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (45 - x)) = _
  rw [show 46 = 1 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_45_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_46_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (46 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (46 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_46 :
    recurrence4Scalar1Second.coeff 46 =
      -(((3875635362144529 * 10 ^ 70 +
        7447273403637954977427962223776515093857136791499921548944471011024307) * 10 ^ 70 +
        5062540786768067302394635314913154965986083125775581624854124346373105) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (46 - x)) = _
  rw [show 47 = 1 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_46_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_47_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (47 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (47 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_47 :
    recurrence4Scalar1Second.coeff 47 =
      (((62049266652454143 * 10 ^ 70 +
        6926319397984837641289432479875933750295921711504482045002203914764092) * 10 ^ 70 +
        3979167664894684508211905068554027265828619096488973723100900436495657) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (47 - x)) = _
  rw [show 48 = 1 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_47_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_48_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (48 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (48 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_48 :
    recurrence4Scalar1Second.coeff 48 =
      (((16307957003077802363 * 10 ^ 70 +
        9813878617967353105764579523373974319432429340757295279248307258405481) * 10 ^ 70 +
        0043753681674109550089221051439906765497223755659980644012625875010055) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (48 - x)) = _
  rw [show 49 = 1 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_48_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_49_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (49 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (49 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_49 :
    recurrence4Scalar1Second.coeff 49 =
      -(((2781678912555335689253 * 10 ^ 70 +
        5725358103026850657833917153162156601723582662541795525451991807222472) * 10 ^ 70 +
        2832617003479688485175107487549775310917294564840890586599784485444894) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (49 - x)) = _
  rw [show 50 = 1 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_49_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_50_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (50 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (50 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_50 :
    recurrence4Scalar1Second.coeff 50 =
      (((302592226294341766135289 * 10 ^ 70 +
        9060996372974384266394081041487213850807842019196191597383396840673291) * 10 ^ 70 +
        6703688632214399798302366331895393776599705876671276826826711391927824) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (50 - x)) = _
  rw [show 51 = 1 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_50_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (51 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_51 :
    recurrence4Scalar1Second.coeff 51 =
      -(((26900213583834822298577790 * 10 ^ 70 +
        9555235546062042251114298474063133922471889797577282365085476716352405) * 10 ^ 70 +
        5289980299335765694452521471591394315965564484964316133698122784395621) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (51 - x)) = _
  rw [show 52 = 1 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_51_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (52 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_52 :
    recurrence4Scalar1Second.coeff 52 =
      (((2093687569635902176166939677 * 10 ^ 70 +
        6419193918739562389898469269828997171108833577753413091211705828270568) * 10 ^ 70 +
        4838954938321635985563800236629607486706128843669783139574356862101276) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (52 - x)) = _
  rw [show 53 = 1 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_52_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (53 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_53 :
    recurrence4Scalar1Second.coeff 53 =
      -(((146989244554405261300038980760 * 10 ^ 70 +
        0207070494372213749270050135796431734303005107094111789636618054656710) * 10 ^ 70 +
        6109275865461639969164488067757623375104891511845208756961799053624639) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (53 - x)) = _
  rw [show 54 = 1 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_53_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (54 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_54 :
    recurrence4Scalar1Second.coeff 54 =
      (((9458895420227966807758073300719 * 10 ^ 70 +
        9263849862972683365215749062576940670842177120310597055391855248726714) * 10 ^ 70 +
        2687204002393044023681000199041259525017978521245808420744968741740250) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (54 - x)) = _
  rw [show 55 = 1 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_54_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (55 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_55 :
    recurrence4Scalar1Second.coeff 55 =
      -(((563438183225537894787199603785792 * 10 ^ 70 +
        0427379254240743805061440472282438314194099727222872567841794966197584) * 10 ^ 70 +
        5493095706124906917346377283883203331305916704617303821371721916351234) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (55 - x)) = _
  rw [show 56 = 1 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_55_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (56 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_56 :
    recurrence4Scalar1Second.coeff 56 =
      (((31272775380886608632480226205861824 * 10 ^ 70 +
        2620320624096471535747988334806095927712915449614350572345542267808425) * 10 ^ 70 +
        5255959490567703554103686915933261182727070330774967738655862281367123) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (56 - x)) = _
  rw [show 57 = 1 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_56_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (57 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_57 :
    recurrence4Scalar1Second.coeff 57 =
      -(((1624978055789363818234727645937166222 * 10 ^ 70 +
        1683344178794677644654706521725245586526878262414262467898931567799825) * 10 ^ 70 +
        0014553808861978417738776169927590039462929239572076829008208096699765) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (57 - x)) = _
  rw [show 58 = 1 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_57_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (58 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_58 :
    recurrence4Scalar1Second.coeff 58 =
      (((79327089037597508705764221908580233009 * 10 ^ 70 +
        4987580004873314780466701334642504121221463853877105873826180591535068) * 10 ^ 70 +
        9690028613686847972682208247246870812067971451829815597862099036703207) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (58 - x)) = _
  rw [show 59 = 1 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_58_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (59 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_59 :
    recurrence4Scalar1Second.coeff 59 =
      -(((3648157418793751727024489840650537927377 * 10 ^ 70 +
        8417956230845401768808208386075050309929951572807145915989794679513239) * 10 ^ 70 +
        3308219633262261393120512386055846205749544307871018385411719377392502) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (59 - x)) = _
  rw [show 60 = 1 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_59_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (60 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_60 :
    recurrence4Scalar1Second.coeff 60 =
      (((158394619845056610420448113332024201787164 * 10 ^ 70 +
        7494785714016015598121164905111317210405681299702182310959592554568663) * 10 ^ 70 +
        2021065231651545082679132182618564989665042970768373205372636267712825) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (60 - x)) = _
  rw [show 61 = 1 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_60_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (61 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_61 :
    recurrence4Scalar1Second.coeff 61 =
      -(((6503852541715651886547720757817855938715732 * 10 ^ 70 +
        1597735047131207132404921135814641924142115829821706757877285261939330) * 10 ^ 70 +
        5902073990429682852977363691647968172882457960748011805415435223432526) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (61 - x)) = _
  rw [show 62 = 1 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_61_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (62 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_62 :
    recurrence4Scalar1Second.coeff 62 =
      (((252907611082918772373976376216871346798540342 * 10 ^ 70 +
        2419841353109400559426039762729733372431425793053669216709733964255166) * 10 ^ 70 +
        5519884777483053801945159031013743958162994605454076365776081937886055) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (62 - x)) = _
  rw [show 63 = 1 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_62_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (63 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_63 :
    recurrence4Scalar1Second.coeff 63 =
      -(((9323580641335413698883267721279278969248387840 * 10 ^ 70 +
        5673741528034971171199043082132793627548030982314211433228810733010341) * 10 ^ 70 +
        3800136003675502421208301358803369919833272808868278599410308012076317) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (63 - x)) = _
  rw [show 64 = 1 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_63_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (64 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_64 :
    recurrence4Scalar1Second.coeff 64 =
      (((326125251331428782690949216515483401232796407834 * 10 ^ 70 +
        4397501009625699504410239789325926798759555175590835287922845392021368) * 10 ^ 70 +
        0634085489698098403304369405217177160542779912072601690605075209311467) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (64 - x)) = _
  rw [show 65 = 1 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_64_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (65 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_65 :
    recurrence4Scalar1Second.coeff 65 =
      -(((10829378162513013765623009937046754857009931270359 * 10 ^ 70 +
        4649305628384741970904098224789335078891705371838477009737597613544325) * 10 ^ 70 +
        2331150816390130737674044430997243968527866527247684904209916464405478) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (65 - x)) = _
  rw [show 66 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_65_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (66 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_66 :
    recurrence4Scalar1Second.coeff 66 =
      (((341472814276140021263964998083658929320616715546332 * 10 ^ 70 +
        5059020472036021551135738800602263908291051555329762305304208344390612) * 10 ^ 70 +
        5650558852538764752719277229934387433911905135547285069718532988881961) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (66 - x)) = _
  rw [show 67 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_66_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (67 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_67 :
    recurrence4Scalar1Second.coeff 67 =
      -(((10224043483105576133553906296673864792795715317164420 * 10 ^ 70 +
        5237261978630290945445667527503248247297346276945135852517215920756828) * 10 ^ 70 +
        1653838055714846323526941293773737484781936487557110530189205190285494) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (67 - x)) = _
  rw [show 68 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_67_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (68 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_68 :
    recurrence4Scalar1Second.coeff 68 =
      (((290549343732831706834598006959522495080349526109019848 * 10 ^ 70 +
        0537469922738299803206309333039948485336209288817412089693369302659220) * 10 ^ 70 +
        9469558662717818838169320319262874032300154562146498349833408546740186) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (68 - x)) = _
  rw [show 69 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_68_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (69 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_69 :
    recurrence4Scalar1Second.coeff 69 =
      -(((7829859086896803528460370127666766048057698616306872925 * 10 ^ 70 +
        0478489631662833131088692186272252930371551280169888638170978943484021) * 10 ^ 70 +
        9179112046918345781729497988147215651350668498683341360900952752793409) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (69 - x)) = _
  rw [show 70 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_69_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (70 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_70 :
    recurrence4Scalar1Second.coeff 70 =
      (((199775910879583997044631827907738338972845106211511426105 * 10 ^ 70 +
        8977551635397033556622964833586402472177154927118137714883452705788022) * 10 ^ 70 +
        7638477497298729968526244530948090735455474155628475978457935732771546) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (70 - x)) = _
  rw [show 71 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_70_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (71 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_71 :
    recurrence4Scalar1Second.coeff 71 =
      -(((4813790255661651732843961280076167285045531684668982675011 * 10 ^ 70 +
        3694091870135586748124592660077228678357878671714640918486784525196906) * 10 ^ 70 +
        0580626493716009203663112412191011796020757809168312818014823183428585) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (71 - x)) = _
  rw [show 72 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_71_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (72 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_72 :
    recurrence4Scalar1Second.coeff 72 =
      (((109102862409731779360228955463799250210765332289052397954441 * 10 ^ 70 +
        2995822355832252852498944183908742884100566564840356066983565271852401) * 10 ^ 70 +
        2130083134929167178083144901059722877710821892770501483341348882031507) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (72 - x)) = _
  rw [show 73 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_72_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (73 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_73 :
    recurrence4Scalar1Second.coeff 73 =
      -(((2310747964675155680500277545763405872687304086790351748277310 * 10 ^ 70 +
        2114018420643319351799348452351543903616430865771872163250436497422651) * 10 ^ 70 +
        4500941210061616412353493223655118041207051559726384492815181957029658) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (73 - x)) = _
  rw [show 74 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_73_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (74 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_74 :
    recurrence4Scalar1Second.coeff 74 =
      (((45227078972290098366094813085613045744316292421498484726910513 * 10 ^ 70 +
        3640826015948029553758689275563134319753121293559794236477901046869675) * 10 ^ 70 +
        2581507631099365011370463848676296591449890001891839464319374136879688) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (74 - x)) = _
  rw [show 75 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_74_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (75 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_75 :
    recurrence4Scalar1Second.coeff 75 =
      -(((801225131469620572758144814035163487813737051572439214014602284 * 10 ^ 70 +
        2710606646193013900310867376996064083347734827688502101931632486225226) * 10 ^ 70 +
        2186585881999729103427118402097937490536653316483724452180912726116093) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (75 - x)) = _
  rw [show 76 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_75_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (76 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_76 :
    recurrence4Scalar1Second.coeff 76 =
      (((12280154812546290702064157630053417355933220603854633166400381744 * 10 ^ 70 +
        3610498219936193740406892060446224655851073027415013664736074162462822) * 10 ^ 70 +
        9521562798396746385568468761342775938500052840501221004379896305106280) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (76 - x)) = _
  rw [show 77 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_76_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (77 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_77 :
    recurrence4Scalar1Second.coeff 77 =
      -(((142632045093989035120483611148968250572331446722555397903852545303 * 10 ^ 70 +
        2413896819763762476062429341320804346577294945492116900736296035473040) * 10 ^ 70 +
        3919250631888625201443903067059857102005160839920633408708128481919312) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (77 - x)) = _
  rw [show 78 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_77_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (78 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_78 :
    recurrence4Scalar1Second.coeff 78 =
      (((445223428423989860017286271646788039445311089369280361542759257582 * 10 ^ 70 +
        4251193447493157894321391725952806885371269481899524187794542025565769) * 10 ^ 70 +
        7468451273012946701651212626147600513979466961331822003304917967455444) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (78 - x)) = _
  rw [show 79 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_78_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (79 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_79 :
    recurrence4Scalar1Second.coeff 79 =
      (((40511619728178186806259156432602553583538324928427367238128996645808 * 10 ^ 70 +
        4643041706403831414623558927508089781238112997424978963189235783407864) * 10 ^ 70 +
        5458334452697521845115928230532295786867461104738411139838428703065999) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (79 - x)) = _
  rw [show 80 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_79_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (80 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_80 :
    recurrence4Scalar1Second.coeff 80 =
      -(((1702320258667531653972431386404351649836019840512336530591199380665791 * 10 ^ 70 +
        4807636682015874947485067833246742336037867873993044042587333629974574) * 10 ^ 70 +
        3622609843090970790192051940434654724891932864779683285445680909033119) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (80 - x)) = _
  rw [show 81 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_80_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (81 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_81 :
    recurrence4Scalar1Second.coeff 81 =
      ((((4 * 10 ^ 70 +
        7835795447179386162068895787646819030882266684259662790727643619074570) * 10 ^ 70 +
        7913590102178984608988888584083283421741289512574786440617240237515806) * 10 ^ 70 +
        6407842773199468479643797556891928811151705605933192708467760133861753) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (81 - x)) = _
  rw [show 82 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_81_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (82 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_82 :
    recurrence4Scalar1Second.coeff 82 =
      -((((112 * 10 ^ 70 +
        2787328736844764108631288899323909669798610274652359953284167059763524) * 10 ^ 70 +
        8782208602040108958551076034461244578655472259241957966894234856398249) * 10 ^ 70 +
        4386030019567203512281268759630029609186238286250056239006441629420069) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (82 - x)) = _
  rw [show 83 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_82_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (83 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_83 :
    recurrence4Scalar1Second.coeff 83 =
      ((((2337 * 10 ^ 70 +
        7863506251543522808082719085815179718152599042247623362295963585760416) * 10 ^ 70 +
        4198852259371273432742859256685973666304613711150498661103687479016375) * 10 ^ 70 +
        4517285244253702782624809173543531376468956798839173892856389230117593) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (83 - x)) = _
  rw [show 84 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_83_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (84 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_84 :
    recurrence4Scalar1Second.coeff 84 =
      -((((44142 * 10 ^ 70 +
        2885534397524988014548721614239435780437907894202094327583731402437810) * 10 ^ 70 +
        1641970488902685848099976380387085343997912962921126088079398693981923) * 10 ^ 70 +
        3868902302137519097384142143104752702760382419433557529761000897935060) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (84 - x)) = _
  rw [show 85 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_84_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (85 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_85 :
    recurrence4Scalar1Second.coeff 85 =
      ((((760416 * 10 ^ 70 +
        1491343566069396573580791995124646545344169598545954608654305751059092) * 10 ^ 70 +
        7215400744899009342479019608963368235366813110159279224110120080966390) * 10 ^ 70 +
        0668116063317492707201218141952115532078758546618003646074818525831172) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (85 - x)) = _
  rw [show 86 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (86 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_86 :
    recurrence4Scalar1Second.coeff 86 =
      -((((11880710 * 10 ^ 70 +
        7644162184318430387488543606541824690037553897946263503194361224756898) * 10 ^ 70 +
        0244560406086800777556150301548241022178068481001402983602845295021214) * 10 ^ 70 +
        5760888532792677220572461684161824523654320450264716002206546408595642) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (86 - x)) = _
  rw [show 87 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (87 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_87 :
    recurrence4Scalar1Second.coeff 87 =
      ((((164595676 * 10 ^ 70 +
        0561327912938184365032642030995423411005983118020852659811738853562483) * 10 ^ 70 +
        1278720661316082532540564569417630624702079021504182620984338141005200) * 10 ^ 70 +
        8835961335418672038290547191237603501594250888574565273706807181708287) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (87 - x)) = _
  rw [show 88 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (88 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_88 :
    recurrence4Scalar1Second.coeff 88 =
      -((((1897487156 * 10 ^ 70 +
        7918857421890883520230209612564900033723113407293800178358377083697238) * 10 ^ 70 +
        9222522713313810194454067878129047711591604208464748103301129051179547) * 10 ^ 70 +
        8735469688842999947055391306621761406604336982320851429877766326108004) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (88 - x)) = _
  rw [show 89 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (89 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_89 :
    recurrence4Scalar1Second.coeff 89 =
      ((((14216237134 * 10 ^ 70 +
        4564272758664543532953348610208880755272915143036469926050660879946420) * 10 ^ 70 +
        3409088873253747721504799642040795328002599621887996766702892909710431) * 10 ^ 70 +
        1531216846413863347650538601127287079216209147376335133377453036255998) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (89 - x)) = _
  rw [show 90 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (90 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_90 :
    recurrence4Scalar1Second.coeff 90 =
      ((((76072247001 * 10 ^ 70 +
        6529373284483495968073964227620715307380919430715818016623105313620428) * 10 ^ 70 +
        5726506545020885183898197815994429572813088203914977907470742406067058) * 10 ^ 70 +
        3612992013263697661519738725567661002667054927431758979984593369784107) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (90 - x)) = _
  rw [show 91 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (91 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_91 :
    recurrence4Scalar1Second.coeff 91 =
      -((((6299245603606 * 10 ^ 70 +
        7639728977516624114141267041471180688166533758944024143443040523262400) * 10 ^ 70 +
        3187487351907472462286916403304779660716655324973869319070995446963874) * 10 ^ 70 +
        5117864583402264508528136227977521851880278518316733762754273291602035) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (91 - x)) = _
  rw [show 92 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (92 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_92 :
    recurrence4Scalar1Second.coeff 92 =
      ((((177398408470698 * 10 ^ 70 +
        2369774277003872940952235822799527369737660946616997090713467418665096) * 10 ^ 70 +
        6709027101959793295882003974142940892974137264658713047911867460496003) * 10 ^ 70 +
        8424043645052424774242547486221240382475384720865526037506994128780623) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (92 - x)) = _
  rw [show 93 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (93 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_93 :
    recurrence4Scalar1Second.coeff 93 =
      -((((3871622063605650 * 10 ^ 70 +
        5683729452292173721279678166409427423653699848574225226070340491843954) * 10 ^ 70 +
        9965899627252275177532641309869582987329939060585936037503457646189750) * 10 ^ 70 +
        9384653924816338672730440954773088020779939828247303599007279882412329) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (93 - x)) = _
  rw [show 94 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (94 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_94 :
    recurrence4Scalar1Second.coeff 94 =
      ((((74040892164298664 * 10 ^ 70 +
        8382648156904913237440992745922444143598605945246905516548796271420454) * 10 ^ 70 +
        2883271271028417067456687168761049106915181957952017960681072210768570) * 10 ^ 70 +
        3882243793893270583992720915820609412797997230570356335593435117273936) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (94 - x)) = _
  rw [show 95 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (95 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_95 :
    recurrence4Scalar1Second.coeff 95 =
      -((((1296179283119867702 * 10 ^ 70 +
        0332853120593000070986621680290849568872788963797569720121562039681796) * 10 ^ 70 +
        1222301021125128426729327535460568955154132596094607773444527233410098) * 10 ^ 70 +
        8247623863600209136737737957046598981732979029589251492666613182247575) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (95 - x)) = _
  rw [show 96 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (96 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_96 :
    recurrence4Scalar1Second.coeff 96 =
      ((((21210572116093729214 * 10 ^ 70 +
        9920040792130723163596115903005477670164814443077523189341828496782181) * 10 ^ 70 +
        1698895064513000342779506508553733334867631117366124839129170074927726) * 10 ^ 70 +
        1055644990890652259398728830375995152762185334504669034125335844528683) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (96 - x)) = _
  rw [show 97 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (97 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_97 :
    recurrence4Scalar1Second.coeff 97 =
      -((((328286288918901576503 * 10 ^ 70 +
        9201607462267648146147593301127808591236222392767571779867276397722308) * 10 ^ 70 +
        9014559717350262081684427755311915792961664201787398933576053392461571) * 10 ^ 70 +
        5244382636385344821140124678368390038598306501115875208055175266951335) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (97 - x)) = _
  rw [show 98 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (98 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_98 :
    recurrence4Scalar1Second.coeff 98 =
      ((((4841496915538642849253 * 10 ^ 70 +
        3315988055841678782345611746868645924456441089048994053194551546773386) * 10 ^ 70 +
        5427223795059958867172413293449403293755570279045286927093841954166050) * 10 ^ 70 +
        6257975463202238913865732087919914183822351728111304210145756522451553) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (98 - x)) = _
  rw [show 99 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (99 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_99 :
    recurrence4Scalar1Second.coeff 99 =
      -((((68377141619858681346852 * 10 ^ 70 +
        3634839470802604180101169719412327074309827194349505463220497683576077) * 10 ^ 70 +
        4228828271384341770143954938804297395390098082639084363354789982573667) * 10 ^ 70 +
        9131065399487803059879394158146574644710697639250548373947647910184990) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (99 - x)) = _
  rw [show 100 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (100 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_100 :
    recurrence4Scalar1Second.coeff 100 =
      ((((928133314536126146210359 * 10 ^ 70 +
        0985619325104072902914416738585393091407367372620407368267472713377985) * 10 ^ 70 +
        6709445686492279480940541077857300516864129885809079516398322846346440) * 10 ^ 70 +
        7425689518457250047268237021165407964044767386715110716907846323783613) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (100 - x)) = _
  rw [show 101 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (101 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_101 :
    recurrence4Scalar1Second.coeff 101 =
      -((((12140955885862257880671757 * 10 ^ 70 +
        5857753288188636190196654574526536376341963021797240264030939597855096) * 10 ^ 70 +
        0969663397164393622294729489414491902335163603263964591301744135869675) * 10 ^ 70 +
        4189591492858287895733218704468343095843011991503768187157320339646581) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (101 - x)) = _
  rw [show 102 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (102 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_102 :
    recurrence4Scalar1Second.coeff 102 =
      ((((153374874601805698632263933 * 10 ^ 70 +
        4673779273104952837465251040116914726373111335112214584853600223839868) * 10 ^ 70 +
        6378268306419969687897508141459592423788061474172378379351127288835626) * 10 ^ 70 +
        6411621592952411693844474819416720824607223145258411107176585554041832) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (102 - x)) = _
  rw [show 103 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (103 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_103 :
    recurrence4Scalar1Second.coeff 103 =
      -((((1874346454184736215579882574 * 10 ^ 70 +
        9231191536175759483046586829873220831357966844878301859421293365626630) * 10 ^ 70 +
        4907659300818294046925681853168161351037879682956598337280629910861074) * 10 ^ 70 +
        9403676108778891052322117900453794862929617421950741059370934655918412) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (103 - x)) = _
  rw [show 104 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (104 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_104 :
    recurrence4Scalar1Second.coeff 104 =
      ((((22189402214568714762833258214 * 10 ^ 70 +
        0735373659499371906539249124439266590864133264735712428279900487911505) * 10 ^ 70 +
        6770476753355856080148904781817167221914234811338892541993992460353631) * 10 ^ 70 +
        3491303945967365630200356976913701595727381215560857121475331984825964) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (104 - x)) = _
  rw [show 105 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (105 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_105 :
    recurrence4Scalar1Second.coeff 105 =
      -((((254771637661068648669697303203 * 10 ^ 70 +
        0375157157967061449378092993570250257607676187921349203399486854948360) * 10 ^ 70 +
        0555017315553816843375786998468374962383712271869478775490116453962237) * 10 ^ 70 +
        6198422794766931947779216884111580534627048896520102798890381647800507) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (105 - x)) = _
  rw [show 106 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (106 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_106 :
    recurrence4Scalar1Second.coeff 106 =
      ((((2839899203498641273268502856365 * 10 ^ 70 +
        5887197371087665400166642192422690405144374242124921424736780149160450) * 10 ^ 70 +
        0708261251587634368202148400654248603745133022659770659896824033948575) * 10 ^ 70 +
        1884861127336086267414691692812443598338487293945496273395781836282246) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (106 - x)) = _
  rw [show 107 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (107 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_107 :
    recurrence4Scalar1Second.coeff 107 =
      -((((30759627169648309360526610030823 * 10 ^ 70 +
        8172157099996843007499007537529290080476610839752618540612637446796656) * 10 ^ 70 +
        4637766535961882434573167396196284755727003299189734310993064497885483) * 10 ^ 70 +
        0727877066221767078372679615457726503266957943193344465355277679225983) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (107 - x)) = _
  rw [show 108 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (108 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_108 :
    recurrence4Scalar1Second.coeff 108 =
      ((((323981750858884384998736307093178 * 10 ^ 70 +
        5797111033896282529992611107585557639911579640640866062303413400931237) * 10 ^ 70 +
        2613233171755729004152937424916246675504064386449947576245346940692761) * 10 ^ 70 +
        2193033388402788286228049599221454887977643616034889354746889978480089) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (108 - x)) = _
  rw [show 109 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (109 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_109 :
    recurrence4Scalar1Second.coeff 109 =
      -((((3320628500362314448700453657291850 * 10 ^ 70 +
        1387566410969661047686464330696173634839154130932808135126559696270099) * 10 ^ 70 +
        6152027737242711025950991184025687153237326136987122158653216792595345) * 10 ^ 70 +
        0561629419707489416898304654299359188462208179320871941129134136145368) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (109 - x)) = _
  rw [show 110 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (110 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_110 :
    recurrence4Scalar1Second.coeff 110 =
      ((((33139785907859160065908972672443078 * 10 ^ 70 +
        4956537578223738594905406531594718908768114109917118685699826261894910) * 10 ^ 70 +
        0448444536169309680009590018446377411881766561787545137514404654150359) * 10 ^ 70 +
        1028529482302024229882168791085136353082563300541756538779227014344311) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (110 - x)) = _
  rw [show 111 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (111 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_111 :
    recurrence4Scalar1Second.coeff 111 =
      -((((322220908185192319298113062845035519 * 10 ^ 70 +
        5060603436085947457810304401894736081779861746806807153729237809490245) * 10 ^ 70 +
        3880434923764594032392190416439022458826025078468261238263743707033595) * 10 ^ 70 +
        4252841379759770488982606994303849452685602524492124545500360164350300) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (111 - x)) = _
  rw [show 112 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (112 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_112 :
    recurrence4Scalar1Second.coeff 112 =
      ((((3053913863869695780533301742459293551 * 10 ^ 70 +
        6362320360236522073517648246906724740061586375501231820435395661329562) * 10 ^ 70 +
        5767427246942581922207658510161349700213120752382122672801160045539335) * 10 ^ 70 +
        6406371224814752830925063069893175141423564884212517357509600656991011) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (112 - x)) = _
  rw [show 113 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (113 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_113 :
    recurrence4Scalar1Second.coeff 113 =
      -((((28227078666715740325282157394305612632 * 10 ^ 70 +
        4815213268969093545160620418422792948318460879761305777307873216924611) * 10 ^ 70 +
        3414955965588754814871412131297135804671250968141514278894658193742693) * 10 ^ 70 +
        1763974442481340157273732526740156946441091355534178290869832426845995) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (113 - x)) = _
  rw [show 114 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (114 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_114 :
    recurrence4Scalar1Second.coeff 114 =
      ((((254550111858951214022539538208232628250 * 10 ^ 70 +
        3871886107624015318447698971975288269403781971701014184741017646078328) * 10 ^ 70 +
        6499084410384084135468195490591853016523505693000373465456424903203270) * 10 ^ 70 +
        2413255932199404826563502123568616039215881229919141575420330038204289) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (114 - x)) = _
  rw [show 115 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (115 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_115 :
    recurrence4Scalar1Second.coeff 115 =
      -((((2240567754952038080530204224761466155885 * 10 ^ 70 +
        7626460574618506606370414227621747158964946233918157726215147385909961) * 10 ^ 70 +
        7897991592057331350590262710632572731692795805643934117479695285929410) * 10 ^ 70 +
        0106009795845322100310382080834815214412405581450205642631182568757246) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (115 - x)) = _
  rw [show 116 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (116 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_116 :
    recurrence4Scalar1Second.coeff 116 =
      ((((19256983644691710176536133210929193679001 * 10 ^ 70 +
        5050381570912709100591714513831864817501733841217854179814008187856984) * 10 ^ 70 +
        9785295030600254038883171679769479107189754836528106137467954099386127) * 10 ^ 70 +
        1301773172213354010620605074398718370921800206111616297418014683626741) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (116 - x)) = _
  rw [show 117 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (117 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_117 :
    recurrence4Scalar1Second.coeff 117 =
      -((((161667187021924945604917362836369592623930 * 10 ^ 70 +
        3367452493220866559344205537031999091896499207379228696047641212324104) * 10 ^ 70 +
        3034409599698048472374867507799574734420963384838384029793829634483178) * 10 ^ 70 +
        0420111515579507079302996085258809808021382550867865031883836376757870) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (117 - x)) = _
  rw [show 118 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (118 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_118 :
    recurrence4Scalar1Second.coeff 118 =
      ((((1326197499806119769127357729604034622197608 * 10 ^ 70 +
        1336699211994961238534418882504645967317545647114907709636288034517814) * 10 ^ 70 +
        5415211167573931126556918409071711140375027977822452891599148567925473) * 10 ^ 70 +
        4411138075185466627608869477993991124292024923221236039151414433393711) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (118 - x)) = _
  rw [show 119 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (119 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_119 :
    recurrence4Scalar1Second.coeff 119 =
      -((((10633803928696759386183710193410799549325483 * 10 ^ 70 +
        0832560538789902325261955326921726950553403260629023225162433219903799) * 10 ^ 70 +
        8865208128911884453655606210285190817330794226524551918305262276997765) * 10 ^ 70 +
        0661931034231266376393980426734866533476840655470306408751800283296518) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (119 - x)) = _
  rw [show 120 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (120 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_120 :
    recurrence4Scalar1Second.coeff 120 =
      ((((83367653818177664848850492352217473908132031 * 10 ^ 70 +
        1577835549418719209629200653503486244977362533981608499377528199152580) * 10 ^ 70 +
        1484085353975675071237438812636213179638308642216933423428589304515527) * 10 ^ 70 +
        8196586275288524230430206869333820858901383510910929327968263135603223) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (120 - x)) = _
  rw [show 121 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (121 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_121 :
    recurrence4Scalar1Second.coeff 121 =
      -((((639238599602956729628795274440310430337840317 * 10 ^ 70 +
        8216839338638162865405025931339214515824031152888895150844027823656243) * 10 ^ 70 +
        2237061376490130720640992270339470269754741616436070185842479069636616) * 10 ^ 70 +
        7958257635283354993841153342221266368782144002479458204289026536816021) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (121 - x)) = _
  rw [show 122 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (122 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_122 :
    recurrence4Scalar1Second.coeff 122 =
      ((((4795203928278954147262183445173572696921497188 * 10 ^ 70 +
        5768509722744073023660703083630318768687877764147886226886864461751686) * 10 ^ 70 +
        7421874835127762231679045601872801882347084884175972615045817521832279) * 10 ^ 70 +
        2304726555203428307631477741293439688657509978332998802416676114356018) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (122 - x)) = _
  rw [show 123 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (123 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_123 :
    recurrence4Scalar1Second.coeff 123 =
      -((((35200331152079836868697736248586729619467322782 * 10 ^ 70 +
        0768434597467226662767652372378184482975595689144116964945925844112387) * 10 ^ 70 +
        6943727304827322570666384558664149212657195790819495744648278100406559) * 10 ^ 70 +
        5925608533444216994521444152960227832276970093179066908770104748016200) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (123 - x)) = _
  rw [show 124 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (124 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_124 :
    recurrence4Scalar1Second.coeff 124 =
      ((((252926321978995265482443024998607586769403903746 * 10 ^ 70 +
        6642316413117445729442044013384624588073721564428720566202475477318396) * 10 ^ 70 +
        0803220041261708059792024862667911894920622715936525924337094305855298) * 10 ^ 70 +
        0181577292420476990789530966329125770296158296756561290970687695726989) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (124 - x)) = _
  rw [show 125 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (125 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_125 :
    recurrence4Scalar1Second.coeff 125 =
      -((((1779329845018888325672174430892569151527115744855 * 10 ^ 70 +
        5481249183865662937614193969429630073928606690387951101793345709142049) * 10 ^ 70 +
        3017544963179388996497161779421374581422164172476955267605431350241526) * 10 ^ 70 +
        5432752625211917621860900330391212995250436397045003262268740743141290) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (125 - x)) = _
  rw [show 126 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (126 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_126 :
    recurrence4Scalar1Second.coeff 126 =
      ((((12258502948038236458515362255942418937075495023061 * 10 ^ 70 +
        8448412485258679371459642220251863685306271868836976806622824612195005) * 10 ^ 70 +
        5895276869931187072315599641282280773562752339100937378887857984853582) * 10 ^ 70 +
        8801738907813398156526727729840960153479829855718572993828568340043258) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (126 - x)) = _
  rw [show 127 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (127 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_127 :
    recurrence4Scalar1Second.coeff 127 =
      -((((82724939300581406161016791985114751564515832836111 * 10 ^ 70 +
        3486304903244483664369665752357459020061732481632492305445018937247327) * 10 ^ 70 +
        0003526545890844700950497021895470973807019801884639414182979392676569) * 10 ^ 70 +
        0969229969723914716945573896491363189604385567725235331803853914119672) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (127 - x)) = _
  rw [show 128 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (128 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_128 :
    recurrence4Scalar1Second.coeff 128 =
      ((((546952261910770047140959531861254889194699776133671 * 10 ^ 70 +
        5789612925213611718461691610553630322429044607140096900209229260414263) * 10 ^ 70 +
        2830516819986684658919825994688083759486620900308670731849131390765886) * 10 ^ 70 +
        8570805378597832318119945218867571161000234004122934114746270306383733) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (128 - x)) = _
  rw [show 129 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (129 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_129 :
    recurrence4Scalar1Second.coeff 129 =
      -((((3543797026794601636665379509758595679116092508149394 * 10 ^ 70 +
        4577220788532556981864714513594241208947382006678230650752574696466037) * 10 ^ 70 +
        4587566080443904473805060332863012273864683578532501585121780593587591) * 10 ^ 70 +
        2385972451901019482571060500759863260574322986784242424186470092495354) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (129 - x)) = _
  rw [show 130 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (130 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_130 :
    recurrence4Scalar1Second.coeff 130 =
      ((((22505259698497455255541112404598702814328656694408955 * 10 ^ 70 +
        9861997308645325227382725840016718047237672935971558822273222493305255) * 10 ^ 70 +
        6160820341206055183776387999756517726022097124722363619727233003405122) * 10 ^ 70 +
        6554076431135622935580120444273080704001037199276574752540728547039507) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (130 - x)) = _
  rw [show 131 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (131 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_131 :
    recurrence4Scalar1Second.coeff 131 =
      -((((140113927927626669860252464940699119161960952302314094 * 10 ^ 70 +
        7537689984175880650776323502761845192313658281901147249087710445667204) * 10 ^ 70 +
        2029668386398692814927814300831545200968403409203301622141501189985364) * 10 ^ 70 +
        8290719155716812382184074207076094417107508637688274419258863798972865) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (131 - x)) = _
  rw [show 132 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (132 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_132 :
    recurrence4Scalar1Second.coeff 132 =
      ((((855350579441105737983437183013869880927897548014650711 * 10 ^ 70 +
        7117403492654386473691930768077184800615142986539288179323463763770511) * 10 ^ 70 +
        3968066585794160894595357388835747824277285550231013576682214730165758) * 10 ^ 70 +
        4072344991723383524946845313739809264190171435640437860287546185026708) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (132 - x)) = _
  rw [show 133 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (133 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_133 :
    recurrence4Scalar1Second.coeff 133 =
      -((((5120983175099577898591884686892383485332061619443956475 * 10 ^ 70 +
        3575494750570148547168573962120865557203638073387632655234233674825405) * 10 ^ 70 +
        5423034006217534125462459112465257059437734833335170988944767498186376) * 10 ^ 70 +
        5969282288472432975535536971526396198187861794535054746951391867568984) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (133 - x)) = _
  rw [show 134 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (134 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_134 :
    recurrence4Scalar1Second.coeff 134 =
      ((((30073717521251983423290048342347465192960142669190480691 * 10 ^ 70 +
        8706463331132762355725343334012366634405057452947936839194147891220189) * 10 ^ 70 +
        2731299069667266059364683801134753494028944821722794871032636223194833) * 10 ^ 70 +
        7136092160794652471132114981238871075118985373763915926230955310962215) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (134 - x)) = _
  rw [show 135 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (135 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_135 :
    recurrence4Scalar1Second.coeff 135 =
      -((((173269147847274985498674900539082658902213140158378257169 * 10 ^ 70 +
        2722316604696702329360027537273385895778521126979333417876821508911416) * 10 ^ 70 +
        3864322241096415914800292750977635545483451367361680492422297195811673) * 10 ^ 70 +
        2982651290271253124038547427722752231085643634161305707681800550043222) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (135 - x)) = _
  rw [show 136 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (136 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_136 :
    recurrence4Scalar1Second.coeff 136 =
      ((((979555788057191682236578533737684748910809031960784251931 * 10 ^ 70 +
        6353066825768230121819085029513422346731821336377117816571224883931217) * 10 ^ 70 +
        5849562928854053465367371317009678142817626424547578812812110724633263) * 10 ^ 70 +
        0907983275375305021994954050551706807293792208828850822686176808989892) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (136 - x)) = _
  rw [show 137 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (137 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_137 :
    recurrence4Scalar1Second.coeff 137 =
      -((((5434782302148314262868806856754992825130394514708444093037 * 10 ^ 70 +
        5449460156523381780976797654458993589894796716814582443516807443840718) * 10 ^ 70 +
        8669638843155557462346485975390949091456527921791542091239580169082692) * 10 ^ 70 +
        6524100207519875424366762735695203761420642283775840475569295328337895) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (137 - x)) = _
  rw [show 138 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (138 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_138 :
    recurrence4Scalar1Second.coeff 138 =
      ((((29597107328330049992735034745197736977941112985715734893345 * 10 ^ 70 +
        8593977804368707488408424383694808733582704919776750915228667572826602) * 10 ^ 70 +
        3819428578886236994977998407561963596086550664495499290216127020883238) * 10 ^ 70 +
        7666802450607143499372355535613832603092906156700360400797751618391351) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (138 - x)) = _
  rw [show 139 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (139 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_139 :
    recurrence4Scalar1Second.coeff 139 =
      -((((158233184271057252351720998056846810117750874151215915382545 * 10 ^ 70 +
        9348938805953600327987953051627545252856404977857653311335007138351842) * 10 ^ 70 +
        1095312471385928130475407695982727029103912696043583984694164867239029) * 10 ^ 70 +
        9413990473176165221502512151848197897462638540450112540020424162395980) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (139 - x)) = _
  rw [show 140 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (140 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_140 :
    recurrence4Scalar1Second.coeff 140 =
      ((((830600395337055060941975438809711759080639338934503124442175 * 10 ^ 70 +
        6590547892055074117371492284571208337271339868262301245055401785262940) * 10 ^ 70 +
        4581929646209959748231787308087247835711048784288457197174195499783340) * 10 ^ 70 +
        3955979652232979987061286480082048904170087287006254412833800197156841) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (140 - x)) = _
  rw [show 141 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (141 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_141 :
    recurrence4Scalar1Second.coeff 141 =
      -((((4281501974805879015355312710912584298474501973633068028105181 * 10 ^ 70 +
        9923969282134383018080099129751721654349811771134995402628770568149571) * 10 ^ 70 +
        9578545559309217951216945327908793791496695449316894345773245984932976) * 10 ^ 70 +
        5970380656847148160542408899413743550550742361634462341760677582614287) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (141 - x)) = _
  rw [show 142 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (142 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_142 :
    recurrence4Scalar1Second.coeff 142 =
      ((((21675592173221571353005074840392049849206993463366472096879386 * 10 ^ 70 +
        8290869340941145676810682670811557617521263425687459684090370549031487) * 10 ^ 70 +
        1638068220331227588164647361034360968054272911509886753227212917152909) * 10 ^ 70 +
        2057686900117656413776137964067505313881216399955749465013638249241311) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (142 - x)) = _
  rw [show 143 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (143 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_143 :
    recurrence4Scalar1Second.coeff 143 =
      -((((107789435020436196442685134712808443309846503819060350360701016 * 10 ^ 70 +
        8192568494840480992975673951912205995986025357969094280733674086221716) * 10 ^ 70 +
        6989355735911731401432166437543073378432260806061252990772788122987891) * 10 ^ 70 +
        2911397676719714576534425507106576526698041862681906281962681747138095) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (143 - x)) = _
  rw [show 144 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (144 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_144 :
    recurrence4Scalar1Second.coeff 144 =
      ((((526586490306744904492838591808857365314439289808644936854496551 * 10 ^ 70 +
        9216413491144511863124644558412274611705637485284802531250531165247222) * 10 ^ 70 +
        9741032991364289756328887888680287413303837856510692849900180888071670) * 10 ^ 70 +
        4645799069244275410324855770092985423564261916189759471171279123542436) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (144 - x)) = _
  rw [show 145 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (145 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_145 :
    recurrence4Scalar1Second.coeff 145 =
      -((((2527596624487934396822815036058854265028272626859917240558805019 * 10 ^ 70 +
        1972983569431121653205953858595687727733637878717440311320619375305835) * 10 ^ 70 +
        2761434872487970483582719301890787833730688446780312175538224478484172) * 10 ^ 70 +
        9201007114714985712349723876466358306173619891627622866591835351928004) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (145 - x)) = _
  rw [show 146 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (146 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_146 :
    recurrence4Scalar1Second.coeff 146 =
      ((((11921887096227140965737981048708551630116550850515118971691733259 * 10 ^ 70 +
        2203541471287478373268407442087166179466813711776215527857040456878452) * 10 ^ 70 +
        4753888987656516716612902486003022497466127710784608079241093430383565) * 10 ^ 70 +
        7884686448409709510866219966411783642068245648727608546805319409784382) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (146 - x)) = _
  rw [show 147 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (147 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_147 :
    recurrence4Scalar1Second.coeff 147 =
      -((((55263009070622287955994140445807628178029185341031149751096112370 * 10 ^ 70 +
        1816092156404794006061108171694844995782919450031497632356306929798491) * 10 ^ 70 +
        5521064408188829543300204990920456600466669490955210792952151861138149) * 10 ^ 70 +
        4494515663245299988421302533607507883342197477842525402160739433329934) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (147 - x)) = _
  rw [show 148 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (148 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_148 :
    recurrence4Scalar1Second.coeff 148 =
      ((((251783891081903045370461255387868494109345208078857872401737601811 * 10 ^ 70 +
        5798403182025761318801145638250233671496973726657870847096472255131913) * 10 ^ 70 +
        4253474087803595043270492023870123523299961046131121703126185479069537) * 10 ^ 70 +
        8807978574020378712288361971718385382430661297809938594451844807496512) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (148 - x)) = _
  rw [show 149 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (149 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_149 :
    recurrence4Scalar1Second.coeff 149 =
      -((((1127652763176749695648471435715279259109273039381214914347032753724 * 10 ^ 70 +
        0813435993276435513232014353442059485502752000921562363635715667172754) * 10 ^ 70 +
        5858810485558902140505575741937562487530183579435021123031989263454678) * 10 ^ 70 +
        0032316921106902499844582889629971385393060325024606747762696284914265) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (149 - x)) = _
  rw [show 150 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (150 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_150 :
    recurrence4Scalar1Second.coeff 150 =
      ((((4965072613333035337253281322455218553113823249994991067705598066498 * 10 ^ 70 +
        7101063912614801435555751228172766419216466061404946444533552967223433) * 10 ^ 70 +
        3666393713771011870636193290129058120410294228813147546064871664629889) * 10 ^ 70 +
        4093623728211785433991553172359508842166317545656697145679327973864687) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (150 - x)) = _
  rw [show 151 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (151 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_151 :
    recurrence4Scalar1Second.coeff 151 =
      -((((21494430735765727801032669477624820331222220869400499227331660591315 * 10 ^ 70 +
        8382164405221968869456638940348430780096319276347113049627768828174688) * 10 ^ 70 +
        6934885380749464714010341348034603352886897178707864337825413670895091) * 10 ^ 70 +
        5847234231289603626286678535770402460169789473685024294061208988421494) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (151 - x)) = _
  rw [show 152 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (152 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_152 :
    recurrence4Scalar1Second.coeff 152 =
      ((((91500283726196738396664666737950130202682503988720481955238719465990 * 10 ^ 70 +
        1577242959508985036378397559191047471657512185462049968378290856402369) * 10 ^ 70 +
        6423788645432671049303467687627910261727532826588719313678398599681688) * 10 ^ 70 +
        3460536930788980821455547884005126509886792599893041703828874532388923) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (152 - x)) = _
  rw [show 153 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (153 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_153 :
    recurrence4Scalar1Second.coeff 153 =
      -((((383053826905874075695607649650321187121192849119370251972318432209254 * 10 ^ 70 +
        6524281965801552562947644648169390136657972173778115323535287833508116) * 10 ^ 70 +
        3048573403118664490981789288819436484601097607048111741237419220608541) * 10 ^ 70 +
        5549346709130187628310417680594823221025615063470163786293377060484349) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (153 - x)) = _
  rw [show 154 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (154 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_154 :
    recurrence4Scalar1Second.coeff 154 =
      ((((1577180857748393775625656514130826866327977918238719139366878035640561 * 10 ^ 70 +
        1507119760996135841799030093507565508351282797324588307256544424486898) * 10 ^ 70 +
        4804747927704539108562559038833255728331984096125785233175940690048574) * 10 ^ 70 +
        9249646807966630960718777710283178116026416438756867753936474796836594) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (154 - x)) = _
  rw [show 155 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (155 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_155 :
    recurrence4Scalar1Second.coeff 155 =
      -((((6387482715948361475325628092441834208357739497370079337910922637161244 * 10 ^ 70 +
        6400865826095697104249409656476645529616367399130687483587557865633403) * 10 ^ 70 +
        1637239574545499495762489117207752775279537628546418244745265810638075) * 10 ^ 70 +
        3849416497533927335782151261415084047053264340502033933182454684663604) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (155 - x)) = _
  rw [show 156 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (156 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_156 :
    recurrence4Scalar1Second.coeff 156 =
      (((((2 * 10 ^ 70 +
        5447524799038498607078802672546999081086564396284684386464763753584585) * 10 ^ 70 +
        7900670894199604967564620409547288564135166174834723263346791485016374) * 10 ^ 70 +
        8648813618746883507772852753334837623998277233657403451071115481394484) * 10 ^ 70 +
        0839720742503378213706592827326959626320190110572656887304142850895003) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (156 - x)) = _
  rw [show 157 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (157 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_157 :
    recurrence4Scalar1Second.coeff 157 =
      -(((((9 * 10 ^ 70 +
        9739863266650916662845375860956317982406908032697302109544153699831994) * 10 ^ 70 +
        7220700473108737044140833838798792350227759718541256735111280112442090) * 10 ^ 70 +
        0412755460102267854625202879203616536002050382071540754364928723637052) * 10 ^ 70 +
        0109158343082829128862652494970895782038585251819979603083419333478905) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (157 - x)) = _
  rw [show 158 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (158 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_158 :
    recurrence4Scalar1Second.coeff 158 =
      (((((38 * 10 ^ 70 +
        4625529155494507136261188248135359837334013342047142578811885156588820) * 10 ^ 70 +
        0473409363267143840090891551490056355567292503165234895923924757922781) * 10 ^ 70 +
        0394318224941729518540158745664928949614573387548053743888097960740266) * 10 ^ 70 +
        0287175397854658114559853357018281861978932990494580828084604093279086) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (158 - x)) = _
  rw [show 159 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (159 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_159 :
    recurrence4Scalar1Second.coeff 159 =
      -(((((145 * 10 ^ 70 +
        9456469884395722426263978835757580947977539325558143739560675951333571) * 10 ^ 70 +
        9739156353433407243355082896004081540338262619195859686535493461410677) * 10 ^ 70 +
        5735611991309723114808024667390124976735006524118082391094493712504514) * 10 ^ 70 +
        5014294435135451264277875503435320990672660450570403399319293134457490) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (159 - x)) = _
  rw [show 160 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (160 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_160 :
    recurrence4Scalar1Second.coeff 160 =
      (((((544 * 10 ^ 70 +
        9596924512075697735774278195507254638770438067028366020969755058016147) * 10 ^ 70 +
        6422575700536084743798286729349175351375504145450297171385934207225145) * 10 ^ 70 +
        3660386142820250572245516511300187799198890604688421660229963191352288) * 10 ^ 70 +
        6403936680545733210267630340741645213341370840371085224093304854666801) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (160 - x)) = _
  rw [show 161 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (161 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_161 :
    recurrence4Scalar1Second.coeff 161 =
      -(((((2002 * 10 ^ 70 +
        5955223363551748598586498848334115581715223205371419501482853301889365) * 10 ^ 70 +
        7915627746647969758179523038939707716275459454407312131068220457859507) * 10 ^ 70 +
        2155428526865947497597819709150509954309406758717043885627404766241733) * 10 ^ 70 +
        4750772307832835767974420433567291270099082138588628188617458557614825) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (161 - x)) = _
  rw [show 162 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (162 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_162 :
    recurrence4Scalar1Second.coeff 162 =
      (((((7242 * 10 ^ 70 +
        8937147157132563688222792518359958691794259972662014177128333960314101) * 10 ^ 70 +
        4418309891293676438284034008636129136639392055437483165041493664524366) * 10 ^ 70 +
        3872040384605081813396418691004886947952771545216557844962888107360910) * 10 ^ 70 +
        1888725917542647495710233273380109546530221104400457301229313907201349) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (162 - x)) = _
  rw [show 163 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (163 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_163 :
    recurrence4Scalar1Second.coeff 163 =
      -(((((25784 * 10 ^ 70 +
        2417406955171280050154114730008534193010739128041963992776403003002743) * 10 ^ 70 +
        0754857844124944659317573886961049319862172703026174436952408810118878) * 10 ^ 70 +
        4147498096282193640066022366448932541296836852831383745101351067242238) * 10 ^ 70 +
        6640862190196564058555976127151604734199253804641840380261043476616439) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (163 - x)) = _
  rw [show 164 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (164 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_164 :
    recurrence4Scalar1Second.coeff 164 =
      (((((90355 * 10 ^ 70 +
        0371942864700056172575853643381531657548938728610825258140642541329203) * 10 ^ 70 +
        0011342386220157892011443726559169188440966472233516654821797725412054) * 10 ^ 70 +
        2825839066869293580286293037102191205132118414034769859547536981470403) * 10 ^ 70 +
        0869069120439709467120308351933288275926676281773242759300093907376386) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (164 - x)) = _
  rw [show 165 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (165 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_165 :
    recurrence4Scalar1Second.coeff 165 =
      -(((((311700 * 10 ^ 70 +
        5173064469472296774178139757307465054829032606981895599916487412300282) * 10 ^ 70 +
        8551473759752384106671867420938061647285997831211389585784603832316183) * 10 ^ 70 +
        6558237530632514263823477246960046170971000270405579943544138532983460) * 10 ^ 70 +
        7442181042828158960195741196958045755157096226040722039137347231163632) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (165 - x)) = _
  rw [show 166 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (166 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_166 :
    recurrence4Scalar1Second.coeff 166 =
      (((((1058620 * 10 ^ 70 +
        4210864060902671968822752444033669450490723094358064926379875153038090) * 10 ^ 70 +
        8556572167011922687931033048353208659352849116661706832483154896525269) * 10 ^ 70 +
        6982012382449393351044304553251088956956295648777828568098467118699525) * 10 ^ 70 +
        4411460322740073215915572627724671711116274659693033003919417329571508) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (166 - x)) = _
  rw [show 167 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (167 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_167 :
    recurrence4Scalar1Second.coeff 167 =
      -(((((3539892 * 10 ^ 70 +
        7708247811335617116699158006829877278910946164877176965490262772066655) * 10 ^ 70 +
        2666981400094963784237270241620650452624395781368362584011334398979194) * 10 ^ 70 +
        3990119379624395312434700541396071134277380632181977884231407672229370) * 10 ^ 70 +
        9469573493297320568824594593159157167480496786935945374871894370612325) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (167 - x)) = _
  rw [show 168 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (168 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_168 :
    recurrence4Scalar1Second.coeff 168 =
      (((((11655089 * 10 ^ 70 +
        8930355493236584436189644076992397469889188997409093494007718084714465) * 10 ^ 70 +
        5754730320171181865008040683417508054934098365289364178833440063523711) * 10 ^ 70 +
        2647135457557435563799512919805660373056219269831260023479420229720575) * 10 ^ 70 +
        9958565227557103295602266030323242009070580846167550579794790176363859) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (168 - x)) = _
  rw [show 169 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (169 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_169 :
    recurrence4Scalar1Second.coeff 169 =
      -(((((37787182 * 10 ^ 70 +
        8503931119493113917872010817363658237208081260276333308379725292869924) * 10 ^ 70 +
        6020815634272495319619592826111179097284506919178475871852243434297882) * 10 ^ 70 +
        3749605197962905482104432896763467268962104320490046601170390767711732) * 10 ^ 70 +
        2711300649601789057043939858028750008546487936560199904261593225182328) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (169 - x)) = _
  rw [show 170 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (170 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1Second_coeff_170 :
    recurrence4Scalar1Second.coeff 170 =
      (((((120643400 * 10 ^ 70 +
        6943289571013872616859869164920639273552406967721995798784092139766561) * 10 ^ 70 +
        1163110655540468294063638569795274685590965533146699008936293474930138) * 10 ^ 70 +
        0157273668898984511507473999981344835315257820270232436531885250277038) * 10 ^ 70 +
        1325878257331215465905527437541965110340559967695411587929765421874130) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (170 - x)) = _
  rw [show 171 = 1 +
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
  rw [recurrence4Scalar1Second_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
