/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
