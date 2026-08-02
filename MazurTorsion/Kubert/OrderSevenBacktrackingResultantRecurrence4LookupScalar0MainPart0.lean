/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_1
  recurrence4B0_coeff_10
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_11
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_12
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_13
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_14
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_15
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156

attribute [local simp]
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_16
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_17
  recurrence4B0_coeff_170
  recurrence4B0_coeff_18
  recurrence4B0_coeff_19
  recurrence4B0_coeff_2
  recurrence4B0_coeff_20
  recurrence4B0_coeff_21
  recurrence4B0_coeff_22
  recurrence4B0_coeff_23
  recurrence4B0_coeff_24
  recurrence4B0_coeff_25
  recurrence4B0_coeff_26
  recurrence4B0_coeff_27
  recurrence4B0_coeff_28
  recurrence4B0_coeff_29
  recurrence4B0_coeff_3
  recurrence4B0_coeff_30
  recurrence4B0_coeff_31
  recurrence4B0_coeff_32
  recurrence4B0_coeff_33
  recurrence4B0_coeff_34
  recurrence4B0_coeff_35
  recurrence4B0_coeff_36
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_4
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_5
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_6
  recurrence4B0_coeff_60

attribute [local simp]
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_7
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_8
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_9
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
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

private theorem recurrence4Scalar0Main_coeff_0_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (0 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (0 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_0 :
    recurrence4Scalar0Main.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (0 - x)) = _
  rw [show 1 = 1 +
    0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_0_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_1_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (1 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (1 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_1 :
    recurrence4Scalar0Main.coeff 1 =
      (-435825609627186405888604163324323151216640 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (1 - x)) = _
  rw [show 2 = 1 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_1_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_2_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (2 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (2 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_2 :
    recurrence4Scalar0Main.coeff 2 =
      (2116116209613328031798796630434159331093577728 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (2 - x)) = _
  rw [show 3 = 1 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_2_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_3_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (3 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (3 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_3 :
    recurrence4Scalar0Main.coeff 3 =
      (13201802557796501963933618362579337219325910227456 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (3 - x)) = _
  rw [show 4 = 1 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_3_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_4_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (4 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (4 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_4 :
    recurrence4Scalar0Main.coeff 4 =
      (-119489780296283556312355559268225234944183539148182336 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (4 - x)) = _
  rw [show 5 = 1 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_4_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_5_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (5 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (5 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_5 :
    recurrence4Scalar0Main.coeff 5 =
      (356361255999808623131583131131167291935524552689994504896 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (5 - x)) = _
  rw [show 6 = 1 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_5_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_6_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (6 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (6 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_6 :
    recurrence4Scalar0Main.coeff 6 =
      (-574411738728221473156549251771091254470352308527446853969120 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (6 - x)) = _
  rw [show 7 = 1 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_6_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_7_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (7 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (7 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_7 :
    recurrence4Scalar0Main.coeff 7 =
      (575182431377434986845617404673338944019311256502555251720206208 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (7 - x)) = _
  rw [show 8 = 1 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_7_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_8_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (8 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (8 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_8 :
    recurrence4Scalar0Main.coeff 8 =
      (-360038273207254347568309589344126725292914825882910556437446403380 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (8 - x)) = _
  rw [show 9 = 1 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_8_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_9_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (9 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (9 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_9 :
    recurrence4Scalar0Main.coeff 9 =
      (113699382593813184783524128811134550988326660151820960369544026146844 : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (9 - x)) = _
  rw [show 10 = 1 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_9_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_10_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (10 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (10 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_10 :
    recurrence4Scalar0Main.coeff 10 =
      ((1 * 10 ^ 70 +
        4298939520913294458117501030456356440461825634590980556613892120469364) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (10 - x)) = _
  rw [show 11 = 1 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_10_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_11_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (11 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (11 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_11 :
    recurrence4Scalar0Main.coeff 11 =
      -((3297 * 10 ^ 70 +
        4423109276605818013703360741947491050992987143982211874126232532147248) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (11 - x)) = _
  rw [show 12 = 1 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_11_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_12_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (12 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (12 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_12 :
    recurrence4Scalar0Main.coeff 12 =
      ((1298616 * 10 ^ 70 +
        1220131634804700832098906603670739728863507295802743148691407835973120) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (12 - x)) = _
  rw [show 13 = 1 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_12_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_13_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (13 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (13 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_13 :
    recurrence4Scalar0Main.coeff 13 =
      ((178801167 * 10 ^ 70 +
        6907642364822362038023054242851900285937695332915167382391618519738952) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (13 - x)) = _
  rw [show 14 = 1 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_13_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_14_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (14 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (14 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_14 :
    recurrence4Scalar0Main.coeff 14 =
      -((439823500908 * 10 ^ 70 +
        5385662356183846923844999122824588355492001319163587208912450424452212) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (14 - x)) = _
  rw [show 15 = 1 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_14_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_15_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (15 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (15 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_15 :
    recurrence4Scalar0Main.coeff 15 =
      ((227575145541816 * 10 ^ 70 +
        7894873059716703761549674715331146416351989964119349653206240836505179) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (15 - x)) = _
  rw [show 16 = 1 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_15_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_16_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (16 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (16 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_16 :
    recurrence4Scalar0Main.coeff 16 =
      -((57697309618153679 * 10 ^ 70 +
        0151985186543127599871889134039196056638974179935467621790122560058276) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (16 - x)) = _
  rw [show 17 = 1 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_16_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_17_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (17 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (17 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_17 :
    recurrence4Scalar0Main.coeff 17 =
      ((3099921679552154928 * 10 ^ 70 +
        2744783413800600530330113218291496250531862121727941654032478402917698) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (17 - x)) = _
  rw [show 18 = 1 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_17_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_18_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (18 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (18 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_18 :
    recurrence4Scalar0Main.coeff 18 =
      ((2218089241413580000281 * 10 ^ 70 +
        9601721879799424983222403108034569815710004388146507195771690435932323) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (18 - x)) = _
  rw [show 19 = 1 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_18_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_19_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (19 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (19 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_19 :
    recurrence4Scalar0Main.coeff 19 =
      ((76617062721843146618571 * 10 ^ 70 +
        6748452926091755373578959812040000935013725420303465646753800706289874) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (19 - x)) = _
  rw [show 20 = 1 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_19_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_20_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (20 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (20 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_20 :
    recurrence4Scalar0Main.coeff 20 =
      -((724488358164503132936966812 * 10 ^ 70 +
        0353093819247959300720862095172131713593220933129044634371679400662904) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (20 - x)) = _
  rw [show 21 = 1 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_20_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_21_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (21 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (21 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_21 :
    recurrence4Scalar0Main.coeff 21 =
      ((432192659813033311042455866958 * 10 ^ 70 +
        7415653043363602467629770238372012775613058661209511556978389445737155) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (21 - x)) = _
  rw [show 22 = 1 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_21_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_22_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (22 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (22 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_22 :
    recurrence4Scalar0Main.coeff 22 =
      -((152920852263140044771577423964457 * 10 ^ 70 +
        1931936293496822857845454100836589908097093236523273501205846392031837) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (22 - x)) = _
  rw [show 23 = 1 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_22_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_23_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (23 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (23 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_23 :
    recurrence4Scalar0Main.coeff 23 =
      ((37980669723644817018067669315916764 * 10 ^ 70 +
        2088948325684097043666037730239671540109853040885510848422909215955987) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (23 - x)) = _
  rw [show 24 = 1 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_23_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_24_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (24 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (24 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_24 :
    recurrence4Scalar0Main.coeff 24 =
      -((6746565495241057894772746972692351835 * 10 ^ 70 +
        8732095910376642899002848130688842782153376590925039663669682635082229) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (24 - x)) = _
  rw [show 25 = 1 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_24_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_25_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (25 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (25 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_25 :
    recurrence4Scalar0Main.coeff 25 =
      ((750799017527074496827323371376624157797 * 10 ^ 70 +
        3097675686361266735675345509632793497536820962903482570714037114434714) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (25 - x)) = _
  rw [show 26 = 1 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_25_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_26_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (26 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (26 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_26 :
    recurrence4Scalar0Main.coeff 26 =
      ((4880150155609270301059519071713886808452 * 10 ^ 70 +
        0125691451262290754662840812254697115483352580878373590896819390968890) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (26 - x)) = _
  rw [show 27 = 1 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_26_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_27_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (27 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (27 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_27 :
    recurrence4Scalar0Main.coeff 27 =
      -((29608732993395772998781027146953404813010802 * 10 ^ 70 +
        9179206765877105437214615072118481356704146180107681937250851822124588) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (27 - x)) = _
  rw [show 28 = 1 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_27_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_28_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (28 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (28 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_28 :
    recurrence4Scalar0Main.coeff 28 =
      ((10644299135896416966483880698092291590808377564 * 10 ^ 70 +
        2768460410438562829481227148389786883850435189692470678357797239963305) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (28 - x)) = _
  rw [show 29 = 1 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_28_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_29_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (29 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (29 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_29 :
    recurrence4Scalar0Main.coeff 29 =
      -((2944417813645439710016101515318161057063282060236 * 10 ^ 70 +
        9566506290898679110126409514063953017172131905304311426406021101036441) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (29 - x)) = _
  rw [show 30 = 1 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_29_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_30_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (30 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (30 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_30 :
    recurrence4Scalar0Main.coeff 30 =
      ((726433680677019007474786699021784903600137649610109 * 10 ^ 70 +
        5476153452303053210058950533562399071563303371557367430449972702354941) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (30 - x)) = _
  rw [show 31 = 1 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_30_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_31_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (31 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (31 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_31 :
    recurrence4Scalar0Main.coeff 31 =
      -((161094180153379009459285860325012739110765706152648508 * 10 ^ 70 +
        0673177975330332647116022315584679810008302580789184185570079279679430) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (31 - x)) = _
  rw [show 32 = 1 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_31_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_32_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (32 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (32 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_32 :
    recurrence4Scalar0Main.coeff 32 =
      ((31461505480468380588703616042770110794170779818650415165 * 10 ^ 70 +
        8477222015092223838178066170009061446585299520361241352149747478322993) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (32 - x)) = _
  rw [show 33 = 1 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_32_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_33_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (33 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (33 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_33 :
    recurrence4Scalar0Main.coeff 33 =
      -((5292315158893077766637780397373598426239016827359520746426 * 10 ^ 70 +
        3194858306837266829052217903907277120860806807262531218608297234744145) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (33 - x)) = _
  rw [show 34 = 1 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_33_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_34_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (34 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (34 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_34 :
    recurrence4Scalar0Main.coeff 34 =
      ((744959497450480346460923175037379080853277200944905299463491 * 10 ^ 70 +
        2007657678772025542242481222352349361374351626272291935042530703610836) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (34 - x)) = _
  rw [show 35 = 1 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_34_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_35_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (35 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (35 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_35 :
    recurrence4Scalar0Main.coeff 35 =
      -((82323163121902221450431236329429211015752142934123899459876970 * 10 ^ 70 +
        7150353176640810032463840734707177881681457968998957454375569081070985) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (35 - x)) = _
  rw [show 36 = 1 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_35_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_36_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (36 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (36 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_36 :
    recurrence4Scalar0Main.coeff 36 =
      ((5613871797102752308825429578020456534141809413823617164052842274 * 10 ^ 70 +
        9774380939141532748928151284654052689585950472192572010851712218341603) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (36 - x)) = _
  rw [show 37 = 1 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_36_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_37_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (37 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (37 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_37 :
    recurrence4Scalar0Main.coeff 37 =
      ((238619803034692156886361629261424020198214162606661855175517847711 * 10 ^ 70 +
        0037450821956624555668262061200074526039051287998449909592288035008310) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (37 - x)) = _
  rw [show 38 = 1 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_37_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_38_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (38 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (38 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_38 :
    recurrence4Scalar0Main.coeff 38 =
      -((166146954692616121166958399974456613145438759761993507768519836223704 * 10 ^ 70 +
        3064425809112317244783107287245201781127303448196661307213686326078153) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (38 - x)) = _
  rw [show 39 = 1 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_38_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_39_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (39 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (39 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_39 :
    recurrence4Scalar0Main.coeff 39 =
      (((3 * 10 ^ 70 +
        5804883542222935598680377358317936754311106201344480102084139628725904) * 10 ^ 70 +
        8715774518147574599463641261484433044633812783519529058003648499918297) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (39 - x)) = _
  rw [show 40 = 1 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_39_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_40_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (40 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (40 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_40 :
    recurrence4Scalar0Main.coeff 40 =
      -(((563 * 10 ^ 70 +
        5112893082092812657762473584894361360949556009477410171267700336626622) * 10 ^ 70 +
        0122022073544022475138699268294629285272854155740872664440545155345738) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (40 - x)) = _
  rw [show 41 = 1 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_40_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_41_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (41 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (41 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_41 :
    recurrence4Scalar0Main.coeff 41 =
      (((73202 * 10 ^ 70 +
        2392411996189186105978327058354143378144033243299921679983852550948775) * 10 ^ 70 +
        5880249804097136511113363381669276088780834094174439672798941392620572) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (41 - x)) = _
  rw [show 42 = 1 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_41_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_42_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (42 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (42 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_42 :
    recurrence4Scalar0Main.coeff 42 =
      -(((8162926 * 10 ^ 70 +
        3763286729128462906503499846339383789905517112711229763437573076235813) * 10 ^ 70 +
        1857431156920736464322054602280492201569454398543718017548359898914243) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (42 - x)) = _
  rw [show 43 = 1 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_42_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_43_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (43 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (43 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_43 :
    recurrence4Scalar0Main.coeff 43 =
      (((790665232 * 10 ^ 70 +
        1226829030584727532021570727186160726540133028700753432230491072983328) * 10 ^ 70 +
        7084598099228385644196110543333885288436773828883501214884572904156808) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (43 - x)) = _
  rw [show 44 = 1 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_43_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_44_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (44 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (44 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_44 :
    recurrence4Scalar0Main.coeff 44 =
      -(((66113733342 * 10 ^ 70 +
        7864975293031125318251126688252828663796521045420222394443742778321310) * 10 ^ 70 +
        0474350230792266375182622405005659122664973093291467374166289515224061) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (44 - x)) = _
  rw [show 45 = 1 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_44_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_45_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (45 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (45 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_45 :
    recurrence4Scalar0Main.coeff 45 =
      (((4622208948350 * 10 ^ 70 +
        2552454071847805368042743794520856149489013379352608262297186017576182) * 10 ^ 70 +
        6851067790360765820706696175016408013094805911218757000485005633648584) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (45 - x)) = _
  rw [show 46 = 1 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_45_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_46_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (46 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (46 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_46 :
    recurrence4Scalar0Main.coeff 46 =
      -(((242866248053061 * 10 ^ 70 +
        9263917323013991346276936893281717613342625220842684170163058230719232) * 10 ^ 70 +
        7928986657987217611180020614297779063378349964638597400808958308907497) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (46 - x)) = _
  rw [show 47 = 1 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_46_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_47_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (47 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (47 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_47 :
    recurrence4Scalar0Main.coeff 47 =
      (((4885222285950026 * 10 ^ 70 +
        4305355966306707236189225177332300706579995282459485637046866509466862) * 10 ^ 70 +
        5294618362500090311300131432579349411783622408433864250852285419692749) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (47 - x)) = _
  rw [show 48 = 1 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_47_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_48_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (48 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (48 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_48 :
    recurrence4Scalar0Main.coeff 48 =
      (((904134748637546109 * 10 ^ 70 +
        8724423152095221471362059998742517524950006764188920817341582003457002) * 10 ^ 70 +
        4946496205615505506159515825762809747681863069884340949803777648877917) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (48 - x)) = _
  rw [show 49 = 1 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_48_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_49_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (49 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (49 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_49 :
    recurrence4Scalar0Main.coeff 49 =
      -(((166352732302894062681 * 10 ^ 70 +
        2450756204382194790415768851986880260960585391122542568629631136329807) * 10 ^ 70 +
        1504035174951744143431706649616292078778316474341243153837935128877780) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (49 - x)) = _
  rw [show 50 = 1 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_49_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_50_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (50 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (50 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_50 :
    recurrence4Scalar0Main.coeff 50 =
      (((18750284808548437650862 * 10 ^ 70 +
        4706545744473642063953590348306789455481584053606814526935250225205145) * 10 ^ 70 +
        3022480671307540624367958692088419718858790888191903806441692635185835) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (50 - x)) = _
  rw [show 51 = 1 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_50_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (51 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_51 :
    recurrence4Scalar0Main.coeff 51 =
      -(((1714843142055422095754128 * 10 ^ 70 +
        8471719593185228072934545227307902706412588749491635562706859732530061) * 10 ^ 70 +
        3712130645010974944211662046402254478797172282298787016198959550648610) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (51 - x)) = _
  rw [show 52 = 1 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_51_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (52 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_52 :
    recurrence4Scalar0Main.coeff 52 =
      (((137003224860432118560368809 * 10 ^ 70 +
        1059396734570444135660271385542623731952353087211740522984369124505290) * 10 ^ 70 +
        6415811958606143361429699182157536404243870094264205631217103945156853) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (52 - x)) = _
  rw [show 53 = 1 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_52_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (53 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_53 :
    recurrence4Scalar0Main.coeff 53 =
      -(((9864817232344463691314259250 * 10 ^ 70 +
        4866173962945534268154448970433032123363341643175210298839393112791112) * 10 ^ 70 +
        9547645084374185279916901314773411432227478166926279955439138386305569) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (53 - x)) = _
  rw [show 54 = 1 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_53_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (54 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_54 :
    recurrence4Scalar0Main.coeff 54 =
      (((650850478613826738122574492781 * 10 ^ 70 +
        6032413960579336430838649023111922195447093259912295278879769883480171) * 10 ^ 70 +
        6414597837246651126184665703014768157752835832912326718957101840894873) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (54 - x)) = _
  rw [show 55 = 1 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_54_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (55 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_55 :
    recurrence4Scalar0Main.coeff 55 =
      -(((39743532990081620322742560844772 * 10 ^ 70 +
        8960694028400068658405142206977183221301747447082239053111291830261179) * 10 ^ 70 +
        1752775951949369532905194288793218912967131388475188341199153978944065) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (55 - x)) = _
  rw [show 56 = 1 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_55_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (56 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_56 :
    recurrence4Scalar0Main.coeff 56 =
      (((2261238616298951587380034059819980 * 10 ^ 70 +
        0917172989340420391215726821672887525644949268309360297884272015009843) * 10 ^ 70 +
        7981236543376457682883486996201837675634380694078857933441484951588475) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (56 - x)) = _
  rw [show 57 = 1 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_56_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (57 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_57 :
    recurrence4Scalar0Main.coeff 57 =
      -(((120443642102047265667411070890861914 * 10 ^ 70 +
        3211560815217186857745077910078857187259091779960138239077524475355341) * 10 ^ 70 +
        3293358073146131855460199725704501497401168907648353309744816343705790) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (57 - x)) = _
  rw [show 58 = 1 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_57_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (58 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_58 :
    recurrence4Scalar0Main.coeff 58 =
      (((6027224492981587844164716844754752295 * 10 ^ 70 +
        7815138379781720083395487765648723269476587490827636737799602197688168) * 10 ^ 70 +
        2121392230548149975803514540612849771421406918032469298581957364360547) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (58 - x)) = _
  rw [show 59 = 1 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_58_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (59 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_59 :
    recurrence4Scalar0Main.coeff 59 =
      -(((284141186754961223855294802473090070116 * 10 ^ 70 +
        1417899225762121375835392974951589587366208225530055306187306075894843) * 10 ^ 70 +
        1164138426507346170037029098281385553095629528507711204103781361415767) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (59 - x)) = _
  rw [show 60 = 1 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_59_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (60 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_60 :
    recurrence4Scalar0Main.coeff 60 =
      (((12646548559815782613733290954158917615785 * 10 ^ 70 +
        3345572480900053583542325782562479299410995181470229492391093967386058) * 10 ^ 70 +
        4892839627331028720789372446227973737284296106742131213770229878602188) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (60 - x)) = _
  rw [show 61 = 1 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_60_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (61 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_61 :
    recurrence4Scalar0Main.coeff 61 =
      -(((532329541776944431667941899046140334716061 * 10 ^ 70 +
        1306731379064982886367400853828073611728920371256142413804780402285090) * 10 ^ 70 +
        2142073541845842295149539388710927613038283767472151775614928445942146) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (61 - x)) = _
  rw [show 62 = 1 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_61_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (62 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_62 :
    recurrence4Scalar0Main.coeff 62 =
      (((21220700706030177187988286474989329227505923 * 10 ^ 70 +
        2459426406122172909296002820823512337061460960688507820221495805732905) * 10 ^ 70 +
        5296460475532266024535361959478230342511441243252458104660236614073309) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (62 - x)) = _
  rw [show 63 = 1 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_62_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (63 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_63 :
    recurrence4Scalar0Main.coeff 63 =
      -(((802014870796854413691842496334468472064027717 * 10 ^ 70 +
        5744620358618630744577931918074731919732810332388580745921448910511946) * 10 ^ 70 +
        9729988842642403321354496239392765311215972020761102425197951768328485) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (63 - x)) = _
  rw [show 64 = 1 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_63_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (64 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_64 :
    recurrence4Scalar0Main.coeff 64 =
      (((28761193084064785430205849469832329888636325590 * 10 ^ 70 +
        1735085898907264255587101056687696065911407241724488756575632436809708) * 10 ^ 70 +
        6325924169023846030842138918375646517682123520878900657555220855221173) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (64 - x)) = _
  rw [show 65 = 1 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_64_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (65 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_65 :
    recurrence4Scalar0Main.coeff 65 =
      -(((979219978789862349123148274008239391560981847628 * 10 ^ 70 +
        3007786475226600401387020965666320943007009067191861387091123236072856) * 10 ^ 70 +
        9428248051066959459337971544786845025669402155131437713126976138116497) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (65 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_65_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (66 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_66 :
    recurrence4Scalar0Main.coeff 66 =
      (((31661688196797157759012173957715653435648371748210 * 10 ^ 70 +
        1951484095791306118035780836485240176316538404435619654528637141277152) * 10 ^ 70 +
        8499451071627697174878457829435634180647066601664353418196111332905318) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (66 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_66_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (67 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_67 :
    recurrence4Scalar0Main.coeff 67 =
      -(((972234039338496207752920126547687185381924469510283 * 10 ^ 70 +
        5912867796348728245481444263146006319915424800350483999024914494196082) * 10 ^ 70 +
        4555865961693450576147533151360648585329156350472856796507230271986099) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (67 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_67_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (68 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_68 :
    recurrence4Scalar0Main.coeff 68 =
      (((28342549744724057746782798117003317982443470053790834 * 10 ^ 70 +
        0703846902775753127118454700288798764629770871347939110730040935877504) * 10 ^ 70 +
        1452246751435277680641521376743638420633752226198783223163034988857168) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (68 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_68_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (69 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_69 :
    recurrence4Scalar0Main.coeff 69 =
      -(((783773368751209670645858444706843211915978238047677636 * 10 ^ 70 +
        3815257970027817349209697729348883918680255695115514862989370994793970) * 10 ^ 70 +
        8547563629167209524071119112830185893893513798920370863366708968295652) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (69 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_69_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (70 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_70 :
    recurrence4Scalar0Main.coeff 70 =
      (((20531101789103635955989986675569407471496763450313862599 * 10 ^ 70 +
        1514282295581391465205083799224914351648022045422030920579219660244440) * 10 ^ 70 +
        8738722070574065800210163975393933134411559199219093296040350263114241) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (70 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_70_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (71 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_71 :
    recurrence4Scalar0Main.coeff 71 =
      -(((508287557958547631681549067519816528486109114700339935531 * 10 ^ 70 +
        5877257449162471380824525381611414083229486633985399991479532614300157) * 10 ^ 70 +
        7239375684009454285889586695578376607092863121637876818191053750339726) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (71 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_71_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (72 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_72 :
    recurrence4Scalar0Main.coeff 72 =
      (((11849599999252825040405057393493688687789622817273363420760 * 10 ^ 70 +
        7764539570806012579302609141738978820653187804786820120661078700267734) * 10 ^ 70 +
        0921492644377515262808424085675600780466829260139884924438783802588278) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (72 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_72_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (73 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_73 :
    recurrence4Scalar0Main.coeff 73 =
      -(((258616302502238967261252802077327435768927425651176589021086 * 10 ^ 70 +
        6730172196341489292755352171590575878996953256530822458125830797742326) * 10 ^ 70 +
        5121737757611749152334098980955078278219580205173049959199927448141786) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (73 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_73_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (74 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_74 :
    recurrence4Scalar0Main.coeff 74 =
      (((5232389897664891165950960020675287708893938942016565054363366 * 10 ^ 70 +
        4367384503436262581273226408911898135008951334952105527823940388020063) * 10 ^ 70 +
        9021536376396703398930814173145697076674886506175625115707391838618785) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (74 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_74_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (75 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_75 :
    recurrence4Scalar0Main.coeff 75 =
      -(((96399598945678987371911059422525609081551474077567856001065028 * 10 ^ 70 +
        6567348409568621887860282442313827517304801796908990417784775342232819) * 10 ^ 70 +
        1190558950918579986555243351939238015028791774239468703904907007560451) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (75 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_75_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (76 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_76 :
    recurrence4Scalar0Main.coeff 76 =
      (((1558138081871976646573905482970085090281628978758617198084762861 * 10 ^ 70 +
        1243630726056987654818302020088991458349871331791449002767492275295433) * 10 ^ 70 +
        1418419630590036458636224737254953041300654956346667786857021996484374) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (76 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_76_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (77 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_77 :
    recurrence4Scalar0Main.coeff 77 =
      -(((19993492829456198034981678640387431760177771952792271038305746292 * 10 ^ 70 +
        7700243797644992383495613927053475908655501806775935594435287400529199) * 10 ^ 70 +
        1104951264652049240021876036348428269230923795170040625718540686468471) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (77 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_77_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (78 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_78 :
    recurrence4Scalar0Main.coeff 78 =
      (((121076197523821109341311473829993456758762913575000422963141228273 * 10 ^ 70 +
        7538654785471253097804137984162458326510907352599358580638682723727911) * 10 ^ 70 +
        7719334787966988469874315744471405335064016172637336466181443157277182) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (78 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_78_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (79 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_79 :
    recurrence4Scalar0Main.coeff 79 =
      (((3640665295796527821224641803196295228258639398946479024117355717487 * 10 ^ 70 +
        1887350205692043347602193083644860019943790401960069562698388311899232) * 10 ^ 70 +
        8081969410725478205003544314396647846114696333408425921855031412227594) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (79 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_79_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (80 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_80 :
    recurrence4Scalar0Main.coeff 80 =
      -(((189023606216219996296087485573774270345923648930511695515749279686735 * 10 ^ 70 +
        2376719488175478449534714822080702698959958171752700799914909011960219) * 10 ^ 70 +
        7280775591124164611404250481767345837051340913973638602212817689480936) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (80 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_80_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (81 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_81 :
    recurrence4Scalar0Main.coeff 81 =
      (((5717165542713269845123885653633207701300223157250154255677568078207657 * 10 ^ 70 +
        2118735750920037257222587891928797188631180509744436303038711740354132) * 10 ^ 70 +
        1142674627758399985161117326784492318857806069797640094066910018372027) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (81 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_81_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (82 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_82 :
    recurrence4Scalar0Main.coeff 82 =
      -((((14 * 10 ^ 70 +
        0838144537466619346587787150037445396162957836526957751074501887270896) * 10 ^ 70 +
        7423976817671601761833758251098409041800763523993183070613303296949105) * 10 ^ 70 +
        4431279178362684034613769123628487158615829651434648878834694488207336) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (82 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_82_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (83 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_83 :
    recurrence4Scalar0Main.coeff 83 =
      ((((305 * 10 ^ 70 +
        2984574465798098005061242458535050690709780516711030733302233839394701) * 10 ^ 70 +
        9998945498889341371128824994851686437946643680332631347288681743621553) * 10 ^ 70 +
        9872355402240289302939117555761187843867945645287280414113341816401418) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (83 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_83_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (84 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_84 :
    recurrence4Scalar0Main.coeff 84 =
      -((((5988 * 10 ^ 70 +
        0701294016795557076486653889689770543740439850153036622483089820022783) * 10 ^ 70 +
        1013847791666504003261457494567098518097636289465461808502033382930753) * 10 ^ 70 +
        8185775910311807086488646399391002136890008263974943482072113386390347) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (84 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_84_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (85 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_85 :
    recurrence4Scalar0Main.coeff 85 =
      ((((107278 * 10 ^ 70 +
        6320895265178096721736315929675196011820896500579237619859430241210367) * 10 ^ 70 +
        0315418771343706158025374471609953070226635464974584538826373118802519) * 10 ^ 70 +
        8009572667979457993107978913954066422654135106728049967537180433188123) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (85 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (86 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_86 :
    recurrence4Scalar0Main.coeff 86 =
      -((((1752015 * 10 ^ 70 +
        7693440406506603686488141526046107321038737022186095730817919117750431) * 10 ^ 70 +
        0266437865337348171706679930533769340910837026222243522740961748875303) * 10 ^ 70 +
        4665187663353277149501919621763634156458626444652291230228812162109609) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (86 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (87 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_87 :
    recurrence4Scalar0Main.coeff 87 =
      ((((25690135 * 10 ^ 70 +
        4388571417425585195560015858968519671557076598903153902072778813673720) * 10 ^ 70 +
        1797681115700824469133625741087553973379297887064004748244384850415228) * 10 ^ 70 +
        0850054083812371056224819354797645561626254340510860677671631757214767) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (87 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (88 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_88 :
    recurrence4Scalar0Main.coeff 88 =
      -((((324260409 * 10 ^ 70 +
        5498719799827570840984695750211962828475057430706483828668578998222602) * 10 ^ 70 +
        8678339570695418168899585578352022036934345428666582568809916219321994) * 10 ^ 70 +
        1781434191854073891008876933157385035418199800873865666851307752012694) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (88 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (89 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_89 :
    recurrence4Scalar0Main.coeff 89 =
      ((((3079679891 * 10 ^ 70 +
        9849836506561313602516589766811332756353207179510098825942812014113552) * 10 ^ 70 +
        7547284713297819534218463713153559451449095828178236778697987016510870) * 10 ^ 70 +
        6094497740525415921628787775854490726883367743610557605236903370828362) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (89 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (90 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_90 :
    recurrence4Scalar0Main.coeff 90 =
      -((((6849096723 * 10 ^ 70 +
        8617875490052712808761430694307537653453669387629640155096402486008519) * 10 ^ 70 +
        2786640031175580061948935982581647547934823432194609381828528762095015) * 10 ^ 70 +
        8165207011349534579654213262764504243708003119049257473827979001016912) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (90 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (91 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_91 :
    recurrence4Scalar0Main.coeff 91 =
      -((((642101023234 * 10 ^ 70 +
        2323800625463645522169313218208061983381647062408553812537477422180078) * 10 ^ 70 +
        1846160276909449818409007234752864650127485115962118714072757697446491) * 10 ^ 70 +
        0331931257803259215359032896074823995370513157409143953283902810784448) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (91 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (92 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_92 :
    recurrence4Scalar0Main.coeff 92 =
      ((((22246146548718 * 10 ^ 70 +
        4575422451605088969722354379016473579848541404899738393965769173566987) * 10 ^ 70 +
        6366428315627278360867860703944632278444431842006465631953633514390165) * 10 ^ 70 +
        2648070212168889732822457886863023162887878955803084046382273220004725) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (92 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (93 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_93 :
    recurrence4Scalar0Main.coeff 93 =
      -((((527684291176305 * 10 ^ 70 +
        0335298406864992489037506917509449767189286803686629529144029952258180) * 10 ^ 70 +
        4345976047249713396373330470662320935342813581055391501448619088949015) * 10 ^ 70 +
        8187098462542525058547030047883772725262668356903511392687444046093447) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (93 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (94 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_94 :
    recurrence4Scalar0Main.coeff 94 =
      ((((10626389944767773 * 10 ^ 70 +
        2209096003110102267924304453512854475122973376224479819282865007931411) * 10 ^ 70 +
        0287978916018730741841020880562147705559592123295923142288990498735614) * 10 ^ 70 +
        3455393119536955510926832201777832212550350733243938341936875944929553) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (94 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (95 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_95 :
    recurrence4Scalar0Main.coeff 95 =
      -((((193378096232968347 * 10 ^ 70 +
        4617241749251885908474786521071839003438361567117087863247478604184421) * 10 ^ 70 +
        0148203595502747548505608082573627932893897802468788807581363203667704) * 10 ^ 70 +
        7454616621299393024033644581970419070452585643765710215895136683764333) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (95 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (96 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_96 :
    recurrence4Scalar0Main.coeff 96 =
      ((((3267846578554576414 * 10 ^ 70 +
        5345174029815583946889333610658405753420452425191863814322128607519600) * 10 ^ 70 +
        2975764278233740361486765297154834381871275673725723070589756636742090) * 10 ^ 70 +
        7208867887480501316427435188495326926187309183125392814739876924329468) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (96 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (97 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_97 :
    recurrence4Scalar0Main.coeff 97 =
      -((((52030134821240555786 * 10 ^ 70 +
        8506361499163761979596628598189027575095506863679711662902115596454830) * 10 ^ 70 +
        5501840100710366374614393471138737617204708829900640585046412090124658) * 10 ^ 70 +
        8520070237110914058091755286257881217234926181870542873250611201834295) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (97 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (98 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_98 :
    recurrence4Scalar0Main.coeff 98 =
      ((((787407029466912706785 * 10 ^ 70 +
        3697456334294324794440777315854331542921216662371525495842892635425817) * 10 ^ 70 +
        7442610933779003303162333553936994229582499009361330674246240650183514) * 10 ^ 70 +
        2752307039233217015641183025712784283985257854699873625275256978427347) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (98 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (99 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_99 :
    recurrence4Scalar0Main.coeff 99 =
      -((((11392210912737808016869 * 10 ^ 70 +
        8373138659306802752738918548056126290300329652853776626369847536131589) * 10 ^ 70 +
        1907177626263891113338956874275319467364796957582822565736886301235287) * 10 ^ 70 +
        2999318994205816103833857506505800273911436802037350242015001404440875) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (99 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (100 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_100 :
    recurrence4Scalar0Main.coeff 100 =
      ((((158215179608606498250322 * 10 ^ 70 +
        9887248735836737257409915558691457765772910129211911032206810236467383) * 10 ^ 70 +
        0526776988246295161826675924565673104477427477678675905200762140452705) * 10 ^ 70 +
        5152266999493287045946347773683554411869245759079679072997829583907668) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (100 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (101 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_101 :
    recurrence4Scalar0Main.coeff 101 =
      -((((2115559937381414365865889 * 10 ^ 70 +
        4887846885832792986784050164218577031959656643676469183557972975001135) * 10 ^ 70 +
        2104084946440503069058840593033147734501791597099744288342070706170927) * 10 ^ 70 +
        7797344772182184029683124862495768626914686355576493108254588460247801) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (101 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (102 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_102 :
    recurrence4Scalar0Main.coeff 102 =
      ((((27298792254493506209598691 * 10 ^ 70 +
        2383967247300580052758883187987196359431048789869033290194175070349003) * 10 ^ 70 +
        2159008947688610991639838004032987031164786369575527640929652640775041) * 10 ^ 70 +
        8436232577304695381058284369624138887024570290841866722115365285118633) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (102 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (103 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_103 :
    recurrence4Scalar0Main.coeff 103 =
      -((((340564793520984298364350553 * 10 ^ 70 +
        7146262466469102367108900671287781117979269384042349794736502846821829) * 10 ^ 70 +
        7621200379241888037799465863340578042126398574372781314765955235391280) * 10 ^ 70 +
        2984492826550102986747221902674222542401092105874250110052030966897121) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (103 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (104 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_104 :
    recurrence4Scalar0Main.coeff 104 =
      ((((4113815941821813194697714924 * 10 ^ 70 +
        1318556220053835324001280698566818696927190792684644322571369797566041) * 10 ^ 70 +
        0602043806082792085445613319367643622247277364965821434912555310047772) * 10 ^ 70 +
        5523404913424955161507187184964155718580465130910250562369890317590642) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (104 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (105 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_105 :
    recurrence4Scalar0Main.coeff 105 =
      -((((48175008292779303173316219754 * 10 ^ 70 +
        1748437547414548604200889540922144902773068213290147391328909145079080) * 10 ^ 70 +
        3560093996834082617042798943422563062602541125607876111143974276510127) * 10 ^ 70 +
        6846510113667766527786511816715199210237229315985068556241745936194166) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (105 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (106 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_106 :
    recurrence4Scalar0Main.coeff 106 =
      ((((547510808127156934680658636972 * 10 ^ 70 +
        8506557864451056623748517347089560420619325128778217424270834164901410) * 10 ^ 70 +
        4038360536568904496680113562995529337761360645847453346775612620063347) * 10 ^ 70 +
        8374210474846798186144947731691803392770157296425845876181252072283195) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (106 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (107 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_107 :
    recurrence4Scalar0Main.coeff 107 =
      -((((6044458017669642701055270918399 * 10 ^ 70 +
        0297324026913492323526781228912798301795878484088641854865186941154736) * 10 ^ 70 +
        9733143916927197936051872742933665706054249159669152036626658818263515) * 10 ^ 70 +
        6225627293287322815062616638880900508296451425869525336631802398692611) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (107 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (108 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_108 :
    recurrence4Scalar0Main.coeff 108 =
      ((((64873400686784454711463442464291 * 10 ^ 70 +
        2400003085338951633394440544448097108391730989711963283589429250698944) * 10 ^ 70 +
        2283061794608452288521309565491347749679061011195476145617968925127699) * 10 ^ 70 +
        0914858306467878175620311649875048147922834234744837934868808148695836) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (108 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (109 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_109 :
    recurrence4Scalar0Main.coeff 109 =
      -((((677379902554120506280460330170470 * 10 ^ 70 +
        9772619144763418588805042028071625361578800460313461374104020706486497) * 10 ^ 70 +
        0491545871678695677883660102537760828682279670761881582409260084170175) * 10 ^ 70 +
        0860708316655478720417912698498154381124544312809479729403974054657914) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (109 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (110 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_110 :
    recurrence4Scalar0Main.coeff 110 =
      ((((6885479727549983003564084836459653 * 10 ^ 70 +
        5937946825366033006580433126430847060130394795154262104396258908086327) * 10 ^ 70 +
        4852066660524336249373995533975086723611535324603325580821919726266342) * 10 ^ 70 +
        8931038169876847492619223563905288899655737250701473955978483965536106) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (110 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (111 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_111 :
    recurrence4Scalar0Main.coeff 111 =
      -((((68175142742470849405125796284522631 * 10 ^ 70 +
        8926396286191662296959556270695720533632729531436357491950530298342248) * 10 ^ 70 +
        8834633194854351515927868818246095842977027503337395024248470210902234) * 10 ^ 70 +
        9305914904573581160031220266131599585239389207041410954975614627886572) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (111 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (112 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_112 :
    recurrence4Scalar0Main.coeff 112 =
      ((((657869401583866899453173797485002321 * 10 ^ 70 +
        7210948258668213119494403888635019463153835512704205644195589568297289) * 10 ^ 70 +
        6806525141871504645203837216231431275383464584048834530928978337188558) * 10 ^ 70 +
        9885940264958393387741752822557376216534137808530373925938255341237907) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (112 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (113 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_113 :
    recurrence4Scalar0Main.coeff 113 =
      -((((6189968587639320393932323827006751223 * 10 ^ 70 +
        2511994312759236790584247557606832258263578040173091205068252495668321) * 10 ^ 70 +
        5082436047999858916204530436809571921320647134131530396242854110674877) * 10 ^ 70 +
        5837834197491576335997007686014726977769445202835567705532780961174579) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (113 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (114 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_114 :
    recurrence4Scalar0Main.coeff 114 =
      ((((56815901726409006963290099914943220485 * 10 ^ 70 +
        9647137522588220932732872111802143980560547820623770960863656613003600) * 10 ^ 70 +
        5979409037598285470299016364527270131543635629482211694699094133316298) * 10 ^ 70 +
        8641439964569015309514317023635251562163261179026391653489796510826765) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (114 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (115 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_115 :
    recurrence4Scalar0Main.coeff 115 =
      -((((508941704059742493745770824122505908043 * 10 ^ 70 +
        0311738904811409506863291756782949648203998523977495550869143280436355) * 10 ^ 70 +
        0669131958362470936316485250735045811654788031674618240472916705498166) * 10 ^ 70 +
        6610164970739325889844667405483825432097336686468495650591473182331419) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (115 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (116 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_116 :
    recurrence4Scalar0Main.coeff 116 =
      ((((4450973407753940663868948768362312815464 * 10 ^ 70 +
        7542146663089180725943249645962377720969221443682268114816278545603250) * 10 ^ 70 +
        2581599592168395180623093037978517550298416092436796557808412351084534) * 10 ^ 70 +
        8527037302103201238038863695696505698270438093532607006810971055220943) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (116 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (117 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_117 :
    recurrence4Scalar0Main.coeff 117 =
      -((((38018287747449534422394290520103321314226 * 10 ^ 70 +
        0515493030005598748072770282631790532845887545800619703487447845183305) * 10 ^ 70 +
        8031738282614078803353611849322782288238326466054995528145566437673761) * 10 ^ 70 +
        7071718840233657921622900942971357650954393085548454097805731148952330) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (117 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (118 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_118 :
    recurrence4Scalar0Main.coeff 118 =
      ((((317273132083460058385472343968138793883005 * 10 ^ 70 +
        7637287210542911087003434630993152316192434402999520860495317944702798) * 10 ^ 70 +
        6856269581385413180976714572047983461899455413462233085019312389550175) * 10 ^ 70 +
        4056873077349418375453955799622887015632384746395598804573250197883610) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (118 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (119 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_119 :
    recurrence4Scalar0Main.coeff 119 =
      -((((2587746038252377126672703695194495198649411 * 10 ^ 70 +
        1364283457632932226888596295684920185850939202244492643488432315969259) * 10 ^ 70 +
        0860995114603581704434185455943183272075852870204579876715979304638583) * 10 ^ 70 +
        5248382940910567750432075179485817024850660869280900536421752658265994) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (119 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (120 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_120 :
    recurrence4Scalar0Main.coeff 120 =
      ((((20634536780271312817705738437997014773560255 * 10 ^ 70 +
        2821840941740987285183862454098110049269603118245565832987317932801390) * 10 ^ 70 +
        8338947341511413127156986475599019962611185506625531664705931040894299) * 10 ^ 70 +
        7079949631257518690365835679819669255150775556221164943377666376839432) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (120 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (121 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_121 :
    recurrence4Scalar0Main.coeff 121 =
      -((((160909989021293386562695498058648056598143221 * 10 ^ 70 +
        2735503493692315059121615025746629652638806011364617785216536666052878) * 10 ^ 70 +
        2961746233582196486572406129816982832605105828152725430843715941179399) * 10 ^ 70 +
        5350157472971612611831732350875695404028441568583445653538175325380989) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (121 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (122 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_122 :
    recurrence4Scalar0Main.coeff 122 =
      ((((1227470310279126843416676510267184398788849278 * 10 ^ 70 +
        6565609389457781267166083843865066781799710564398764891283659400631954) * 10 ^ 70 +
        7360142404545188073062302042350926461339684594757839697822861371112283) * 10 ^ 70 +
        9671954197338166507560817194582938717995576857454713102861445069531690) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (122 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (123 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_123 :
    recurrence4Scalar0Main.coeff 123 =
      -((((9162156995312255327445665935112370091058166618 * 10 ^ 70 +
        1121592568125789042546860380988724063282379027522066742725517384216589) * 10 ^ 70 +
        8250459795383160262319890505940354363310551848376997220627693382790280) * 10 ^ 70 +
        0113391240352303571592868849497037371554366628602687712892996517105506) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (123 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (124 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_124 :
    recurrence4Scalar0Main.coeff 124 =
      ((((66935609485437236116710585005211001115518401743 * 10 ^ 70 +
        1116628956039630024281206319769897340338709217728662123547040047562204) * 10 ^ 70 +
        1416142250676221861120263429399976776232157210791197236924231891145498) * 10 ^ 70 +
        7047404505856309851565533476977313655854935676681302391140807705584328) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (124 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (125 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_125 :
    recurrence4Scalar0Main.coeff 125 =
      -((((478739073854523519363741810492664993016746558430 * 10 ^ 70 +
        6922217164008445388942537319782496469342552055834536298335980153857463) * 10 ^ 70 +
        2321100505580686580460601602257550338963804516315836193883701917120617) * 10 ^ 70 +
        1519570451875009733115540631143923670414708288596097337361034223493123) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (125 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (126 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_126 :
    recurrence4Scalar0Main.coeff 126 =
      ((((3352955698660662172910000865881729705691059840088 * 10 ^ 70 +
        6405586656396223573973095605859744159015763662202759307312761920301581) * 10 ^ 70 +
        9287563340172519267156439492738710820258773736464443769893192469792002) * 10 ^ 70 +
        8683166349629871016152600974724211505437972257811467852821931325909561) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (126 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (127 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_127 :
    recurrence4Scalar0Main.coeff 127 =
      -((((23000919573433758841812864837629367905288444770368 * 10 ^ 70 +
        6888867660015634507735514727596103174233502601472268113245228969990024) * 10 ^ 70 +
        4952340335020384341060086319476985925621937535159287433346423425262704) * 10 ^ 70 +
        6540600413495330757241499323853392926928733759471753426659698311068952) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (127 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (128 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_128 :
    recurrence4Scalar0Main.coeff 128 =
      ((((154578284303360972052489793869737892988287531894135 * 10 ^ 70 +
        4723537621317307339219640321240143044038003372944127977704103603161850) * 10 ^ 70 +
        5109172544518896255431396875694600351029728090331723071438814546170589) * 10 ^ 70 +
        3486497004626623979355064201432072143431941104076865478686229813334577) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (128 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (129 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_129 :
    recurrence4Scalar0Main.coeff 129 =
      -((((1017962208889608527549540522764657383520173124892507 * 10 ^ 70 +
        9957234857836477424687415949953975910603439233112047865695666400148977) * 10 ^ 70 +
        8589953609535945528562870692510448773605355542866116062786392983459300) * 10 ^ 70 +
        9421795465010280482730045337274394746018383074517812516872301215832158) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (129 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (130 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_130 :
    recurrence4Scalar0Main.coeff 130 =
      ((((6570303853474652163986843701081779478846691092113147 * 10 ^ 70 +
        0774088311303279549846208870295714880522053377394381430851298164712238) * 10 ^ 70 +
        1823583353217784544108236022269708390384864067580401200063153476298497) * 10 ^ 70 +
        1349680997693613894042595602619816177088442984222942944312223560713298) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (130 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (131 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_131 :
    recurrence4Scalar0Main.coeff 131 =
      -((((41571677808660979972905431835836798567801478598587579 * 10 ^ 70 +
        0231349860753617394973534580095576046255617447227849265341426345324059) * 10 ^ 70 +
        6614276302689417890139258872670229277317981145619903611180016281887975) * 10 ^ 70 +
        5240059432461264855698338172398925115505164164904502989567166026690268) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (131 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (132 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_132 :
    recurrence4Scalar0Main.coeff 132 =
      ((((257900822724604245006333622742879541431429835078386371 * 10 ^ 70 +
        0886917085494918621142028403722256888360777571723483545193196334700749) * 10 ^ 70 +
        6075883491871489840896649810387309838962294158399954313311674629612834) * 10 ^ 70 +
        6433757253710972466933343633575010076728839457089195391663243004453642) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (132 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (133 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_133 :
    recurrence4Scalar0Main.coeff 133 =
      -((((1569036386805732574944103217166790713390745248482788373 * 10 ^ 70 +
        0680656250485785290451615118389264716366405608572109607845813603938641) * 10 ^ 70 +
        2679656244073062526256380146883869342962221133021770692237293486929220) * 10 ^ 70 +
        2330902888922877102075608704842062504569800030679540350731236760039433) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (133 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (134 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_134 :
    recurrence4Scalar0Main.coeff 134 =
      ((((9363060906658648295056749219533432174290566987995282537 * 10 ^ 70 +
        8180467851811615269200363767412310675703562665008012520577003139289359) * 10 ^ 70 +
        5999120827646605417579797124146634483174334036312724190298378512670923) * 10 ^ 70 +
        6830385551793108417270533191228624458817173081454552455005213257119346) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (134 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (135 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_135 :
    recurrence4Scalar0Main.coeff 135 =
      -((((54813077013396195942008797225147712579288391551848291152 * 10 ^ 70 +
        8556055382774017223256010969612024569120383553475115057199594680908304) * 10 ^ 70 +
        6764553541640800933228787788989358407785119236288149225638911435244736) * 10 ^ 70 +
        7655544278664390401835006993824047163019658783371824058950305874057802) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (135 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (136 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_136 :
    recurrence4Scalar0Main.coeff 136 =
      ((((314852111050451851041288382043211104414820764013870259418 * 10 ^ 70 +
        3172080865927869206192157548592808753614608310204222727419255926817276) * 10 ^ 70 +
        7253863430969536221356515508522430317185560711084328626643084912975466) * 10 ^ 70 +
        1792978705668442998468753728662207507483459593714881853663104129232363) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (136 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (137 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_137 :
    recurrence4Scalar0Main.coeff 137 =
      -((((1774832870898751178215504000821005850180789178885493076929 * 10 ^ 70 +
        4613077117187437493693215697876926817672503884381507257744037518613750) * 10 ^ 70 +
        5847195296779594160856578805556818556398762203186208697005045646243829) * 10 ^ 70 +
        1651456148581021903099297943919528384529100083572251610483353100971599) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (137 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (138 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_138 :
    recurrence4Scalar0Main.coeff 138 =
      ((((9819896630583578637069129508800370062764332173824960080480 * 10 ^ 70 +
        1179694725703392604078751556334235270474015411820885805837420084074867) * 10 ^ 70 +
        3861972829329402909358476208517070872993330681653947255480614969602177) * 10 ^ 70 +
        2829050897188215048797749217411527471284875789365732012454898010158155) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (138 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (139 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_139 :
    recurrence4Scalar0Main.coeff 139 =
      -((((53336322223547533106794403850746906602449651259348235146029 * 10 ^ 70 +
        1529745124831636433095703132629431098904858554389576118338827669244258) * 10 ^ 70 +
        7959142610756461207804956980270442858426270234976412340231777157841324) * 10 ^ 70 +
        3877897725395094799713774292952692557909458203887686589490918006443334) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (139 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (140 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_140 :
    recurrence4Scalar0Main.coeff 140 =
      ((((284427784681169867494926874120980745165724799597265241881388 * 10 ^ 70 +
        1685863996690571574915966852522169054562035340600462229305618158283126) * 10 ^ 70 +
        1864748489271356252598326130214316482313479505709972507303019583279520) * 10 ^ 70 +
        4778695468658272578644853611232258505862232920651178885161298605543850) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (140 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (141 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_141 :
    recurrence4Scalar0Main.coeff 141 =
      -((((1489422687195997424009409474090383381013815706250306444891325 * 10 ^ 70 +
        8340062848859028899575495806784001839495312304319767408958126466673938) * 10 ^ 70 +
        9338223746758706058476622642843651775901624162479174005160926684421539) * 10 ^ 70 +
        5022197647143685318046644803743581986348843932532062210550315068855796) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (141 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (142 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_142 :
    recurrence4Scalar0Main.coeff 142 =
      ((((7659902613887767146396138655096209676962724117470083757019216 * 10 ^ 70 +
        6636087029906198476887236191508081776962276471500387431529034266307471) * 10 ^ 70 +
        3686811172095162233810866214380505576723889098215680999552732737294477) * 10 ^ 70 +
        4529229744646153033216678383485236193620458224764881680853170566065630) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (142 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (143 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_143 :
    recurrence4Scalar0Main.coeff 143 =
      -((((38694428100341364581132723221678609407164283378094852944151515 * 10 ^ 70 +
        6750030356102137443035725246820371263720964956249176510057118961036403) * 10 ^ 70 +
        1689629072565158371189024485570161981225593607157723090191587297186127) * 10 ^ 70 +
        9965089678869358579745411358157764734093144315895264914118295287484560) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (143 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (144 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_144 :
    recurrence4Scalar0Main.coeff 144 =
      ((((192022606781095257019322593806804769019442498838756663596191283 * 10 ^ 70 +
        4562731815902399414059707644637909643701041724922167163413147379851719) * 10 ^ 70 +
        6357843137173682424607024307799148419783984229947917998652887140956231) * 10 ^ 70 +
        0398573580522051656238197692765575787580173498999291529683454615691859) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (144 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (145 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_145 :
    recurrence4Scalar0Main.coeff 145 =
      -((((936250832392269050691260395457946025787496036677917544574305611 * 10 ^ 70 +
        7756911509724449342464077779658713687551183099587123474928228918300557) * 10 ^ 70 +
        4113755866245278480357065797999839269075310269891801898186528151771306) * 10 ^ 70 +
        9300431385787490199650812323314505396636910656061006246306875755998582) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (145 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (146 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_146 :
    recurrence4Scalar0Main.coeff 146 =
      ((((4485631294158060185411533622556540701129264790638992225439976779 * 10 ^ 70 +
        4511045654266343971230828422146257186500314675614056533504767530468486) * 10 ^ 70 +
        3820888526889718582282798452127964230083412743957644767753238844204623) * 10 ^ 70 +
        1990513756239053533762182273187834966236365524697886533640727541256289) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (146 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (147 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_147 :
    recurrence4Scalar0Main.coeff 147 =
      -((((21120317633952658623267128191980875018011652328893745458156118900 * 10 ^ 70 +
        1839155753262915805715248802770621534015511107918174371478981265722935) * 10 ^ 70 +
        3361990199168310041451634743656812847871475832081584125496571152381431) * 10 ^ 70 +
        8847347815752156793465929559726109572903862086672950321813108398287425) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (147 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (148 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_148 :
    recurrence4Scalar0Main.coeff 148 =
      ((((97740676319435621541429471993521993738367321088116116489021914220 * 10 ^ 70 +
        9348693332089915655320260626097939678472357322085530205194449575591795) * 10 ^ 70 +
        9076660825949483536665029507033809942941113933039487154330820867184696) * 10 ^ 70 +
        8497768648054743862764527783345851822994223875540325878509161749988704) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (148 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (149 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_149 :
    recurrence4Scalar0Main.coeff 149 =
      -((((444630547835142644474004331547550368553819641217632842141011539315 * 10 ^ 70 +
        4402741340933484876208055699057847654082494519386085322690497117036343) * 10 ^ 70 +
        4995898293981016001646666244344996474785867943164496978232943806818502) * 10 ^ 70 +
        6117272247743623228678865580240347029983202814403676369345364509377548) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (149 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (150 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_150 :
    recurrence4Scalar0Main.coeff 150 =
      ((((1988483244281888577399321862409137508239795969650592037909688683920 * 10 ^ 70 +
        0376031619236640959133092179819972697210530158710746693838193328647923) * 10 ^ 70 +
        5463083722406228397601825363375080819343018407557668956655361303965871) * 10 ^ 70 +
        1589257887153187110631629315176407183631513113650959789596136234581108) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (150 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (151 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_151 :
    recurrence4Scalar0Main.coeff 151 =
      -((((8743624390345727672018950956318906460240553135477921083688287801995 * 10 ^ 70 +
        6816118381986574242031000761942952985984963634431387139180571641034955) * 10 ^ 70 +
        5750909706818423256700617324050288467337375537669191481809156893256106) * 10 ^ 70 +
        7245558708332140564275231749055225049553394323817708535513178032563270) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (151 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (152 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_152 :
    recurrence4Scalar0Main.coeff 152 =
      ((((37805489193205786835350759011554562668397953254944196753441392840704 * 10 ^ 70 +
        1335097371288162240636025692530235384620639936468937529483403002888643) * 10 ^ 70 +
        3840909026603547919995788851876067276117219846111088025890387375307990) * 10 ^ 70 +
        4770133101813372291996429870607441288568326022987409114946753925223337) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (152 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (153 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_153 :
    recurrence4Scalar0Main.coeff 153 =
      -((((160752461197347484172338800319453778403969152609936193462981090049456 * 10 ^ 70 +
        8023038385572916814412794460869833957347186534177671030872842827886378) * 10 ^ 70 +
        2214190843783715507384121876010733057342024638377742138499308169044351) * 10 ^ 70 +
        1868609115038590173191082196012019222469325983129789127402884385301321) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (153 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (154 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_154 :
    recurrence4Scalar0Main.coeff 154 =
      ((((672270594487392492283077119572277213600766877257453186326500512032511 * 10 ^ 70 +
        4309458530241645593651926314126856860466178438979993850010826683164464) * 10 ^ 70 +
        1281245854895091407035306931786285790997192691379081551454532762107973) * 10 ^ 70 +
        5333439875948836112550584715975304632494321853394222696798887211104455) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (154 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (155 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_155 :
    recurrence4Scalar0Main.coeff 155 =
      -((((2765396403344830624479953682675119649014223824620168094320907010065136 * 10 ^ 70 +
        5994687737813153715885970885928491580050374472395158582814081093795547) * 10 ^ 70 +
        3307801526494365496136488461501222389991408892688961796254843410089924) * 10 ^ 70 +
        4872389310468113675170821462394980423853403812196118095836208580873202) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (155 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (156 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_156 :
    recurrence4Scalar0Main.coeff 156 =
      (((((1 * 10 ^ 70 +
        1190238376600526291935807579677344253051911924736063083373434072326601) * 10 ^ 70 +
        6039032082540987445535720789239498121099061964078253963268105843914028) * 10 ^ 70 +
        5543224636162168930016720644116100044479435042631954020664513311002308) * 10 ^ 70 +
        3857981649186573754563406256104924306598630122948634800248700319599283) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (156 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (157 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_157 :
    recurrence4Scalar0Main.coeff 157 =
      -(((((4 * 10 ^ 70 +
        4548249722536241003954479941719888354106318985447548239750547457270059) * 10 ^ 70 +
        8790413711147610071928319033768980376133679545738515328145856793597376) * 10 ^ 70 +
        7505821024902332453461066965487338095629532068015975951197992554306302) * 10 ^ 70 +
        8577484506773176393530731713953418391189853274820699677577298999597708) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (157 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (158 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_158 :
    recurrence4Scalar0Main.coeff 158 =
      (((((17 * 10 ^ 70 +
        4490130349898643384757434960958165226057363465747662079649691443819218) * 10 ^ 70 +
        3808503190080835086752804384981299184605619740326647138078969501753676) * 10 ^ 70 +
        5112328456894221824416459922027982622391959437766728567710404636828838) * 10 ^ 70 +
        7376963741627409212651732658166264000508900625205209692117135395894425) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (158 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (159 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_159 :
    recurrence4Scalar0Main.coeff 159 =
      -(((((67 * 10 ^ 70 +
        2509519172873118782995897020867201800954425593299754166603174400656438) * 10 ^ 70 +
        5972833434841808214831984742435106109823766505432092224485978727263252) * 10 ^ 70 +
        5167441959772241569541724386830280326597655591988630084131246780798735) * 10 ^ 70 +
        5007488775414707490314774769439160076425578115675801007384764144783129) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (159 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (160 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_160 :
    recurrence4Scalar0Main.coeff 160 =
      (((((255 * 10 ^ 70 +
        0648977883067557412234764190854417909815812637408064625922992653930848) * 10 ^ 70 +
        8805571273096841659146301911080552774204311084731312569336590366105393) * 10 ^ 70 +
        5172971624316189559862018260151222872418598016670119446230916218600978) * 10 ^ 70 +
        6995164678405419856759783205392231732052018749032534281253562960052430) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (160 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (161 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_161 :
    recurrence4Scalar0Main.coeff 161 =
      -(((((952 * 10 ^ 70 +
        0591274296994711327336746158926198738139770226359635231070443402448438) * 10 ^ 70 +
        9314232713876071309432250663793197727465835007970379000064093929792424) * 10 ^ 70 +
        8508999086695682263079512629391861816023118162414926732647221894460439) * 10 ^ 70 +
        4370303467028671409868850086855697555170586647881377930812464433996310) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (161 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (162 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_162 :
    recurrence4Scalar0Main.coeff 162 =
      (((((3497 * 10 ^ 70 +
        6258668124513937570641168788868608237209332418825887296798196133668163) * 10 ^ 70 +
        6492634005989380558261412115957818801994164231029914303644463205710214) * 10 ^ 70 +
        4294307347989660810238367063620810509376191982014829809943656402209393) * 10 ^ 70 +
        1034712779181249622526170465512430720256065430280506940535212564958245) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (162 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (163 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_163 :
    recurrence4Scalar0Main.coeff 163 =
      -(((((12647 * 10 ^ 70 +
        7481662841833526262558255832137828728521615967061992685417311989205971) * 10 ^ 70 +
        7396644738623992966792013116982260055749052850706237288650639173709409) * 10 ^ 70 +
        0199462393519374542418758192663385176409168203291397252675036452692232) * 10 ^ 70 +
        3006748389555462612993472257717268391174669539433443527674732199619934) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (163 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (164 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_164 :
    recurrence4Scalar0Main.coeff 164 =
      (((((45021 * 10 ^ 70 +
        1642494632517913178134885316805546543892925726835572130546278480176703) * 10 ^ 70 +
        4632894298725626074169680437724715225728893476677275293738733092212856) * 10 ^ 70 +
        2217527271888192511240117492083855857362907019773647853483018140068042) * 10 ^ 70 +
        0277727385993517113653297110963359644921713134266167239402191922675820) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (164 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (165 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_165 :
    recurrence4Scalar0Main.coeff 165 =
      -(((((157766 * 10 ^ 70 +
        9919879162658493380709601373570057997537751799819792025493308333714423) * 10 ^ 70 +
        8293234553835675134842999473928323468037726807897232366460708410203211) * 10 ^ 70 +
        0676811802690408673813119801038759330129870861341699401917680323498144) * 10 ^ 70 +
        3025360813420406010759357288754057463917882570417006666926556647826959) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (165 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (166 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_166 :
    recurrence4Scalar0Main.coeff 166 =
      (((((544305 * 10 ^ 70 +
        5808472011808337915818480959892662472841258010867493628010021959918761) * 10 ^ 70 +
        3817756649193890126281708650377491952581443828599565413624095321560467) * 10 ^ 70 +
        1023955475027804132482570100962292643919219843708391216238520559710236) * 10 ^ 70 +
        4933887253643818271819789706004345359535170577786036636702461509494217) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (166 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (167 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_167 :
    recurrence4Scalar0Main.coeff 167 =
      -(((((1848957 * 10 ^ 70 +
        9078181284952301054407459113024337374403760014849092599022168617520061) * 10 ^ 70 +
        4423013250119686582927394751951767132168225616570158993632114154674977) * 10 ^ 70 +
        1499870853405767120172786240704044445429085565446542685544251306433606) * 10 ^ 70 +
        8294960600569852947051211196149207844391492631182116128801161634938182) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (167 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (168 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_168 :
    recurrence4Scalar0Main.coeff 168 =
      (((((6184410 * 10 ^ 70 +
        7026679744029776106610798978009118355784515070661299356380623651808861) * 10 ^ 70 +
        3313205665078717386174939531143390237376020775632080205339386608210586) * 10 ^ 70 +
        2796571845961263237605615420259025263877554015561844808800226206801932) * 10 ^ 70 +
        6536638186184974219295460963753362918814032768917621294857793826715471) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (168 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (169 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_169 :
    recurrence4Scalar0Main.coeff 169 =
      -(((((20369729 * 10 ^ 70 +
        2922098714622181893852965518650700969412824159859825080315325585377047) * 10 ^ 70 +
        0675130842525170722529125473805426945712557062393593797270521354965262) * 10 ^ 70 +
        1245393721057202982130343731056197347134051079200024229527502883031682) * 10 ^ 70 +
        4972604993672740956046639178881452502058084769864569383936678935111874) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (169 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (170 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_170 :
    recurrence4Scalar0Main.coeff 170 =
      (((((66071706 * 10 ^ 70 +
        9647620620351341759831067420911257845276877952256808350238597973534377) * 10 ^ 70 +
        8408324809250504318557732930001766837919646063316965608522371883517290) * 10 ^ 70 +
        8445942033386519383331498759974315065392022729274812786929726666711050) * 10 ^ 70 +
        3523427624671983815597768723504618766270406161092644635229127495521677) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (170 - x)) = _
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
  rw [recurrence4Scalar0Main_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
