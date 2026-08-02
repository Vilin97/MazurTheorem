/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

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
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117

attribute [local simp]
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_13
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_14
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_15
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_16
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_17
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_22

attribute [local simp]
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80

attribute [local simp]
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar2First_coeff_0_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (0 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (0 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_0 :
    recurrence4Scalar2First.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (0 - x)) = _
  rw [show 1 = 1 +
    0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_0_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_1_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (1 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (1 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_1 :
    recurrence4Scalar2First.coeff 1 =
      (-4478585163154794200093651455596016765017858048 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (1 - x)) = _
  rw [show 2 = 1 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_1_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_2_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (2 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (2 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_2 :
    recurrence4Scalar2First.coeff 2 =
      (26930821020513676202167999028265183488289416543232 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (2 - x)) = _
  rw [show 3 = 1 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_2_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_3_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (3 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (3 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_3 :
    recurrence4Scalar2First.coeff 3 =
      (-60537483962024339189216517869488293995417400461486592 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (3 - x)) = _
  rw [show 4 = 1 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_3_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_4_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (4 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (4 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_4 :
    recurrence4Scalar2First.coeff 4 =
      (45344773146786063916402308011398880709253200494285345280 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (4 - x)) = _
  rw [show 5 = 1 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_4_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_5_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (5 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (5 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_5 :
    recurrence4Scalar2First.coeff 5 =
      (58827588115646807780566651106555902852566093494674698122032 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (5 - x)) = _
  rw [show 6 = 1 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_5_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_6_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (6 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (6 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_6 :
    recurrence4Scalar2First.coeff 6 =
      (-168419459268969594906586497535741075898426227198070632123956200 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (6 - x)) = _
  rw [show 7 = 1 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_6_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_7_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (7 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (7 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_7 :
    recurrence4Scalar2First.coeff 7 =
      (170798540160019085925271793170513679335573070010390213175796117336 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (7 - x)) = _
  rw [show 8 = 1 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_7_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_8_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (8 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (8 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_8 :
    recurrence4Scalar2First.coeff 8 =
      (-88613814129859775596556440053216104877274564991670273733510432590884 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (8 - x)) = _
  rw [show 9 = 1 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_8_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_9_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (9 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (9 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_9 :
    recurrence4Scalar2First.coeff 9 =
      ((2 * 10 ^ 70 +
        2197902270774629782629746149751946765359719793984068103784360621949864) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (9 - x)) = _
  rw [show 10 = 1 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_9_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_10_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (10 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (10 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_10 :
    recurrence4Scalar2First.coeff 10 =
      -((191 * 10 ^ 70 +
        4730666793398846485585189004306448134202250450516612101520680770663760) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (10 - x)) = _
  rw [show 11 = 1 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_10_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_11_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (11 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (11 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_11 :
    recurrence4Scalar2First.coeff 11 =
      ((58203 * 10 ^ 70 +
        8729818254351199303456645106378513537890789297296632310506929289797708) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (11 - x)) = _
  rw [show 12 = 1 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_11_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_12_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (12 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (12 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_12 :
    recurrence4Scalar2First.coeff 12 =
      -((61887210 * 10 ^ 70 +
        5858818984124381163768695670766883429385988878824215301890639874781340) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (12 - x)) = _
  rw [show 13 = 1 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_12_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_13_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (13 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (13 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_13 :
    recurrence4Scalar2First.coeff 13 =
      ((15926107419 * 10 ^ 70 +
        6129725699561108403785526177959178017228555283708238048481940445258400) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (13 - x)) = _
  rw [show 14 = 1 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_13_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_14_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (14 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (14 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_14 :
    recurrence4Scalar2First.coeff 14 =
      -((3752911519780 * 10 ^ 70 +
        1482795568368662308898011144585992306493816296200800694768335784469262) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (14 - x)) = _
  rw [show 15 = 1 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_14_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_15_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (15 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (15 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_15 :
    recurrence4Scalar2First.coeff 15 =
      ((9975982715564966 * 10 ^ 70 +
        8471743437389032751889676335359485784544858278811770079690584736338142) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (15 - x)) = _
  rw [show 16 = 1 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_15_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_16_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (16 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (16 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_16 :
    recurrence4Scalar2First.coeff 16 =
      -((9794654786324610378 * 10 ^ 70 +
        4261802795128624963456996086132463128039142050185115771912466144792680) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (16 - x)) = _
  rw [show 17 = 1 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_16_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_17_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (17 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (17 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_17 :
    recurrence4Scalar2First.coeff 17 =
      ((4629480631418272854493 * 10 ^ 70 +
        6383297964105696224855317445392735955805367703306990380142219265054884) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (17 - x)) = _
  rw [show 18 = 1 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_17_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_18_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (18 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (18 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_18 :
    recurrence4Scalar2First.coeff 18 =
      -((917981163334058445488403 * 10 ^ 70 +
        0749565633929741975987096560601582196692634524236201552663679509706845) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (18 - x)) = _
  rw [show 19 = 1 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_18_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_19_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (19 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (19 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_19 :
    recurrence4Scalar2First.coeff 19 =
      -((246511251437454678024846003 * 10 ^ 70 +
        4059812271182549405936611934566606187822925796755862376633856554505771) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (19 - x)) = _
  rw [show 20 = 1 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_19_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_20_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (20 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (20 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_20 :
    recurrence4Scalar2First.coeff 20 =
      ((265665324932310552040065787035 * 10 ^ 70 +
        2807058050182328521021660709281258364656291998128919833066253160439059) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (20 - x)) = _
  rw [show 21 = 1 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_20_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_21_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (21 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (21 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_21 :
    recurrence4Scalar2First.coeff 21 =
      -((111229781878794774010969828879737 * 10 ^ 70 +
        4985714598505628705002712882342438576265601024291806113166173847445295) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (21 - x)) = _
  rw [show 22 = 1 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_21_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_22_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (22 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (22 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_22 :
    recurrence4Scalar2First.coeff 22 =
      ((30302458927473172850141526325596461 * 10 ^ 70 +
        9764748995072444781107528717377706502962506328131715317204566605693807) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (22 - x)) = _
  rw [show 23 = 1 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_22_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_23_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (23 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (23 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_23 :
    recurrence4Scalar2First.coeff 23 =
      -((5826418333706457367261473042901998305 * 10 ^ 70 +
        6382496226664340740377836082412473829628454299490057236481457344724538) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (23 - x)) = _
  rw [show 24 = 1 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_23_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_24_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (24 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (24 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_24 :
    recurrence4Scalar2First.coeff 24 =
      ((817745936670760360649400287908521654936 * 10 ^ 70 +
        3567068633004814752793934445915552440142375877378816718801695747317140) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (24 - x)) = _
  rw [show 25 = 1 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_24_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_25_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (25 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (25 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_25 :
    recurrence4Scalar2First.coeff 25 =
      -((112621853985428674618538126610592137237418 * 10 ^ 70 +
        8847119683711328220362236916359138604240195519212483752845609015937635) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (25 - x)) = _
  rw [show 26 = 1 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_25_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_26_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (26 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (26 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_26 :
    recurrence4Scalar2First.coeff 26 =
      ((33786567579532122210595669873551197032125815 * 10 ^ 70 +
        2231953986039610948795978291396566793120089686245281314610668238700449) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (26 - x)) = _
  rw [show 27 = 1 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_26_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_27_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (27 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (27 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_27 :
    recurrence4Scalar2First.coeff 27 =
      -((14467625342537742175796517399980975003422549018 * 10 ^ 70 +
        6545565494037990081670829728281750965293262922338552392959048061263492) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (27 - x)) = _
  rw [show 28 = 1 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_27_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_28_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (28 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (28 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_28 :
    recurrence4Scalar2First.coeff 28 =
      ((5083343627702361234738210308202340122469403602402 * 10 ^ 70 +
        6888360194839916981845843616232161849028179662235327755250446973403521) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (28 - x)) = _
  rw [show 29 = 1 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_28_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_29_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (29 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (29 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_29 :
    recurrence4Scalar2First.coeff 29 =
      -((1413486306316786245742475931692056269785274448041271 * 10 ^ 70 +
        4445507301222969536641484262189818495204842184673758846012889224572139) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (29 - x)) = _
  rw [show 30 = 1 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_29_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_30_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (30 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (30 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_30 :
    recurrence4Scalar2First.coeff 30 =
      ((322747808690968091697078353495493468746492771572467833 * 10 ^ 70 +
        2118588115180150189955120078122880471643811341469569877768007562530477) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (30 - x)) = _
  rw [show 31 = 1 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_30_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_31_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (31 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (31 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_31 :
    recurrence4Scalar2First.coeff 31 =
      -((62069047950206724668311559873550087106746944842746788034 * 10 ^ 70 +
        0403700138073149475554555033160758357157320747935156086890493409268615) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (31 - x)) = _
  rw [show 32 = 1 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_31_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_32_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (32 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (32 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_32 :
    recurrence4Scalar2First.coeff 32 =
      ((10142994358592368643935661186907293555053995267550348270875 * 10 ^ 70 +
        0439275285935232100351803507565792617089942385400320443012762837527405) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (32 - x)) = _
  rw [show 33 = 1 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_32_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_33_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (33 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (33 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_33 :
    recurrence4Scalar2First.coeff 33 =
      -((1395501471472422315880908058860825366129089475380035215255680 * 10 ^ 70 +
        5598448856484721858390328985665403565488593057225728705589832235616994) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (33 - x)) = _
  rw [show 34 = 1 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_33_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_34_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (34 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (34 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_34 :
    recurrence4Scalar2First.coeff 34 =
      ((155217288417022324076654730462600468835838788574902370781005971 * 10 ^ 70 +
        3631726442652647059178537494720966652075834075107268784494724833966916) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (34 - x)) = _
  rw [show 35 = 1 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_34_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_35_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (35 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (35 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_35 :
    recurrence4Scalar2First.coeff 35 =
      -((12106422790070300049517527185399990556538351741831458589112780718 * 10 ^ 70 +
        8616576918607185796171368510053742294348843111430153355175685135267465) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (35 - x)) = _
  rw [show 36 = 1 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_35_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_36_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (36 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (36 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_36 :
    recurrence4Scalar2First.coeff 36 =
      ((151272691364337929251563141143482743007187032537611364240942359831 * 10 ^ 70 +
        5652041336150790712636522262842281213590788001461644262815613435632210) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (36 - x)) = _
  rw [show 37 = 1 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_36_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_37_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (37 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (37 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_37 :
    recurrence4Scalar2First.coeff 37 =
      ((163893910867054262260415492076033131664616181893902031793510911582153 * 10 ^ 70 +
        2319755055817375556317288425808643592728507912081663150207681185861176) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (37 - x)) = _
  rw [show 38 = 1 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_37_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_38_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (38 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (38 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_38 :
    recurrence4Scalar2First.coeff 38 =
      -(((3 * 10 ^ 70 +
        8607300626520326015041025841927311674893693081287204452055900910130478) * 10 ^ 70 +
        6125524966805737546707374759327773022660646534853535657109763750461257) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (38 - x)) = _
  rw [show 39 = 1 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_38_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_39_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (39 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (39 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_39 :
    recurrence4Scalar2First.coeff 39 =
      (((593 * 10 ^ 70 +
        0521234461240098784373861374030543822818271522732498892370429113838198) * 10 ^ 70 +
        3370203123385275762743537540162315223573170073279906582143359207914440) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (39 - x)) = _
  rw [show 40 = 1 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_39_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_40_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (40 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (40 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_40 :
    recurrence4Scalar2First.coeff 40 =
      -(((71665 * 10 ^ 70 +
        6642702561924097795235269001317041208310558545775640371540063572561104) * 10 ^ 70 +
        6813343343534162895762142830475243599720342386934456038721082800520500) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (40 - x)) = _
  rw [show 41 = 1 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_40_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_41_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (41 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (41 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_41 :
    recurrence4Scalar2First.coeff 41 =
      (((7062103 * 10 ^ 70 +
        1393266340853460422087467773472313000181241093761575781598180502303420) * 10 ^ 70 +
        8082626467624792202626990668713283682898753219459160782942066303665732) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (41 - x)) = _
  rw [show 42 = 1 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_41_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_42_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (42 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (42 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_42 :
    recurrence4Scalar2First.coeff 42 =
      -(((550994181 * 10 ^ 70 +
        6010274525046551347268941678800977311312133440455077966196019944546070) * 10 ^ 70 +
        9609513929598321204800328659592569084639892232637570688339360335787695) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (42 - x)) = _
  rw [show 43 = 1 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_42_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_43_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (43 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (43 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_43 :
    recurrence4Scalar2First.coeff 43 =
      (((28596860894 * 10 ^ 70 +
        0053114725694848964870396263104107007710736898057890990069983371700520) * 10 ^ 70 +
        5821234580264853586360597814628326483090420736614407961051650364961281) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (43 - x)) = _
  rw [show 44 = 1 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_43_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_44_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (44 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (44 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_44 :
    recurrence4Scalar2First.coeff 44 =
      (((220692487678 * 10 ^ 70 +
        3022411957302412907758617856105230926144720982470693517035398931846448) * 10 ^ 70 +
        8425403219767062409893852941451937985602866035440799668901241845460045) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (44 - x)) = _
  rw [show 45 = 1 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_44_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_45_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (45 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (45 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_45 :
    recurrence4Scalar2First.coeff 45 =
      -(((300269344380338 * 10 ^ 70 +
        0644746677824139980744126585086428924840118328612868033975483389803965) * 10 ^ 70 +
        3831149306541835830987067462550543883294041116326918399018290219613783) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (45 - x)) = _
  rw [show 46 = 1 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_45_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_46_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (46 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (46 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_46 :
    recurrence4Scalar2First.coeff 46 =
      (((49457659447827314 * 10 ^ 70 +
        1656573034966052278458595664183919394962831187392553435555672757049984) * 10 ^ 70 +
        5537863291993887754584315955455243308079158250603299383494361222647624) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (46 - x)) = _
  rw [show 47 = 1 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_46_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_47_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (47 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (47 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_47 :
    recurrence4Scalar2First.coeff 47 =
      -(((5831870899690734757 * 10 ^ 70 +
        9264645656856561104020215423412478063186410498738709554843953099350852) * 10 ^ 70 +
        5212729060237072456488393225872562783398395012585859838034659292159591) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (47 - x)) = _
  rw [show 48 = 1 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_47_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_48_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (48 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (48 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_48 :
    recurrence4Scalar2First.coeff 48 =
      (((575533450170690840722 * 10 ^ 70 +
        9818647223272149229522183890530877749064996426342761755854797909588377) * 10 ^ 70 +
        5042171987155069941263361830291012925885567608862270227728409208618083) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (48 - x)) = _
  rw [show 49 = 1 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_48_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_49_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (49 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (49 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_49 :
    recurrence4Scalar2First.coeff 49 =
      -(((50091110474216138502719 * 10 ^ 70 +
        1456026317595632490953649949875786443214407778815392021381230177793996) * 10 ^ 70 +
        9082297980418718761900012016325316147737462490873217375526146675678786) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (49 - x)) = _
  rw [show 50 = 1 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_49_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_50_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (50 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (50 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_50 :
    recurrence4Scalar2First.coeff 50 =
      (((3941117128749189144322141 * 10 ^ 70 +
        6499344951990071166036851081156905768003018523154366577355579440441361) * 10 ^ 70 +
        5996217865936248340170311998796695735404352135366579054658772663669943) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (50 - x)) = _
  rw [show 51 = 1 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_50_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (51 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_51 :
    recurrence4Scalar2First.coeff 51 =
      -(((284276692043181283346322362 * 10 ^ 70 +
        6970124051064813388102649141029264949894216035689052247820383281192845) * 10 ^ 70 +
        6496425982683476767616288857512452103785321374150845375957474263026112) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (51 - x)) = _
  rw [show 52 = 1 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_51_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (52 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_52 :
    recurrence4Scalar2First.coeff 52 =
      (((18967636205399420665509333108 * 10 ^ 70 +
        4073393477341791061611548423550310887885407743745006965665334051062034) * 10 ^ 70 +
        6087150381369266741680599847731419564848490705032950566210850548159502) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (52 - x)) = _
  rw [show 53 = 1 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_52_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (53 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_53 :
    recurrence4Scalar2First.coeff 53 =
      -(((1177939857635656934866474054765 * 10 ^ 70 +
        1414657380198663634455256818053292384663427512946951235659908186404935) * 10 ^ 70 +
        7843554119056088354346834304621719256404954081682997410319834224117601) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (53 - x)) = _
  rw [show 54 = 1 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_53_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (54 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_54 :
    recurrence4Scalar2First.coeff 54 =
      (((68397774465674959877576645378900 * 10 ^ 70 +
        2465098043747384116642334264764083246009355649425212270419741856819263) * 10 ^ 70 +
        6550991011452562572677794243794115093510075896303674689598553771793065) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (54 - x)) = _
  rw [show 55 = 1 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_54_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (55 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_55 :
    recurrence4Scalar2First.coeff 55 =
      -(((3726309046477413028410729533047701 * 10 ^ 70 +
        2694422052273393463229454345988381293783250805011273159629182886526703) * 10 ^ 70 +
        3829671735572336438004791473575998021256356428005045657895518084850932) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (55 - x)) = _
  rw [show 56 = 1 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_55_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (56 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_56 :
    recurrence4Scalar2First.coeff 56 =
      (((190996950256374678704372733927969749 * 10 ^ 70 +
        7263921998428729561170342944334031578157109395499495755352501763983441) * 10 ^ 70 +
        2261321034703510362834152798845378771825515911315316749818651638200585) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (56 - x)) = _
  rw [show 57 = 1 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_56_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (57 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_57 :
    recurrence4Scalar2First.coeff 57 =
      -(((9230993608755835650674336658040949375 * 10 ^ 70 +
        1713916578545881502529162287911908032531658242734572844410229158353938) * 10 ^ 70 +
        3444461823321299176354519517509599297680286254048745355324972289054909) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (57 - x)) = _
  rw [show 58 = 1 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_57_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (58 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_58 :
    recurrence4Scalar2First.coeff 58 =
      (((421439089723292953597642159852761720382 * 10 ^ 70 +
        6489223824172041904483359824884731049375821536563496583672066974027661) * 10 ^ 70 +
        4901435098131351261239035152753494018509628864241777398853158843045071) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (58 - x)) = _
  rw [show 59 = 1 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_58_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (59 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_59 :
    recurrence4Scalar2First.coeff 59 =
      -(((18202733858100599637431053158560692080509 * 10 ^ 70 +
        0150517672514375633274610038373077201329668059149661424774527655596253) * 10 ^ 70 +
        6071413179465262246176193794645610318704668478497124837960813897989070) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (59 - x)) = _
  rw [show 60 = 1 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_59_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (60 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_60 :
    recurrence4Scalar2First.coeff 60 =
      (((744712150087788399952458167204864528759463 * 10 ^ 70 +
        3449771417287204963442455904949553180591219490026119126224079684497472) * 10 ^ 70 +
        6405549365455737670241208482896632301748685487418931323891011827981402) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (60 - x)) = _
  rw [show 61 = 1 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_60_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (61 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_61 :
    recurrence4Scalar2First.coeff 61 =
      -(((28888278974305752875770806428212773801827630 * 10 ^ 70 +
        1473731837011187534389631194709181316150052731650965782223800318302971) * 10 ^ 70 +
        1344878954403683041714344469125458617412542021734509260080529168142068) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (61 - x)) = _
  rw [show 62 = 1 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_61_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (62 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_62 :
    recurrence4Scalar2First.coeff 62 =
      (((1063337051891257868116392246800276365600821276 * 10 ^ 70 +
        9738604974485768964444636245886435683795072152874817899852707499927204) * 10 ^ 70 +
        7682745001876329876934343412591277476260181678476209849235482258856480) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (62 - x)) = _
  rw [show 63 = 1 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_62_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (63 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_63 :
    recurrence4Scalar2First.coeff 63 =
      -(((37159900058414243115683402258817848503739700667 * 10 ^ 70 +
        1748280759911816855563298554616239160800123346296066668785121790607583) * 10 ^ 70 +
        7705590042129868915673744038318478818910597971203840579897059145388591) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (63 - x)) = _
  rw [show 64 = 1 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_63_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (64 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_64 :
    recurrence4Scalar2First.coeff 64 =
      (((1233299561814208629985835918077475091784555876092 * 10 ^ 70 +
        9502933992782982675374362567787022395055478337754408678686924719764097) * 10 ^ 70 +
        8730389143898297312998118519669335748022679235515510020329914728165631) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (64 - x)) = _
  rw [show 65 = 1 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_64_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (65 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_65 :
    recurrence4Scalar2First.coeff 65 =
      -(((38875331571707598739104492646816845768231983632084 * 10 ^ 70 +
        5850759771969309879401854482466226428334783598250379128866738822575159) * 10 ^ 70 +
        0411673443243375035772132805659259865781369735251411746550354627012894) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (65 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_65_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (66 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_66 :
    recurrence4Scalar2First.coeff 66 =
      (((1163521701454956177351801806732299331163733049787933 * 10 ^ 70 +
        3082195699248696007283902672502326955605423264220926803523061689995347) * 10 ^ 70 +
        1668600485697298852233720371904477153993196548209249794837352911184263) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (66 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_66_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (67 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_67 :
    recurrence4Scalar2First.coeff 67 =
      -(((33042944778058708146155761787525516863081200795457833 * 10 ^ 70 +
        8970398308784610428892954197464106866480141954275778366036854097757432) * 10 ^ 70 +
        6412735881917907975230793202667409546951978901929480855837704641867736) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (67 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_67_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (68 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_68 :
    recurrence4Scalar2First.coeff 68 =
      (((889329294568563889236792537009958464164201537136531226 * 10 ^ 70 +
        9545109920066391379190186956916211710969392822964133634395373692574234) * 10 ^ 70 +
        4117281984010521222186392408295202241420795553619791870153332114557465) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (68 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_68_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (69 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_69 :
    recurrence4Scalar2First.coeff 69 =
      -(((22639758785593991448026292981625583845938433221983090581 * 10 ^ 70 +
        8763821847683839968433606631738984663457186106283136313795499500893615) * 10 ^ 70 +
        4014508886915818306418649696140266862916998321768470862136710824122991) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (69 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_69_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (70 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_70 :
    recurrence4Scalar2First.coeff 70 =
      (((543446948095094110205603721599711801828994263409928063539 * 10 ^ 70 +
        4786933512742306851110524328609169296681535172561799039402853764351061) * 10 ^ 70 +
        7613917212891633798814350042115554351090896597426247125405220200889884) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (70 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_70_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (71 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_71 :
    recurrence4Scalar2First.coeff 71 =
      -(((12239852688464006012804400376312207781079524840430017839900 * 10 ^ 70 +
        2411412086908766789272020451125088417393710033471153782310968086356252) * 10 ^ 70 +
        7789231248113783547614541648205935432023359684341282053275816673796644) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (71 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_71_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (72 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_72 :
    recurrence4Scalar2First.coeff 72 =
      (((256571441114951213068949222989713422664675858678164036899041 * 10 ^ 70 +
        9998609530791965056051681765407401555060601670615773420031205629793605) * 10 ^ 70 +
        5258728782036683908101305004496136928522188038030105531368733597845305) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (72 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_72_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (73 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_73 :
    recurrence4Scalar2First.coeff 73 =
      -(((4934853305384518853569652585757152724189970171146272780152222 * 10 ^ 70 +
        1576127121255145376082949637873600446086426286826138671034891835795953) * 10 ^ 70 +
        9290888588024949544106749845171361699606504027120703948261656339589606) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (73 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_73_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (74 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_74 :
    recurrence4Scalar2First.coeff 74 =
      (((84692222225171974084582088356542527563790887216565690938220853 * 10 ^ 70 +
        9883020362525945381637669889000610677225996937111748900922825676560854) * 10 ^ 70 +
        8507767454921109522833378642430224345305721656956497872899540939338934) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (74 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_74_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (75 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_75 :
    recurrence4Scalar2First.coeff 75 =
      -(((1213085990140362813340959637725861265420696114179814124039290645 * 10 ^ 70 +
        6290977866412024675057029778796480749750962126091900791615092802659277) * 10 ^ 70 +
        0976675159620385682608441959315375822376571808853131475622856385320123) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (75 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_75_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (76 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_76 :
    recurrence4Scalar2First.coeff 76 =
      (((11341585506321966061087592217647844171388546103657452341777386014 * 10 ^ 70 +
        6691005237488392830363371117182726091239814551441821205839402680106108) * 10 ^ 70 +
        8508020373128430178831287943356556203168724472990349271112635096138896) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (76 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_76_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (77 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_77 :
    recurrence4Scalar2First.coeff 77 =
      (((70627686042813309296036128577478657702206047440083686902394498206 * 10 ^ 70 +
        7586224520704712018529947770324281365013464900737464782898942883738142) * 10 ^ 70 +
        7806801212672024725480330989047762261832808739041699880011404546684257) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (77 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_77_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (78 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_78 :
    recurrence4Scalar2First.coeff 78 =
      -(((7426965143966340271903605090385440064179773412163345804309319237199 * 10 ^ 70 +
        1625629930037819598770890898476694161358242403495208844097835175890550) * 10 ^ 70 +
        7206831287190769839771857745969139542382435438929445791450644700752214) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (78 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_78_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (79 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_79 :
    recurrence4Scalar2First.coeff 79 =
      (((254901613128399835313944612615168227357735641083678194506889531822399 * 10 ^ 70 +
        6470776876151910510385079206178142467781903665374863137977541302102822) * 10 ^ 70 +
        0579381939060602958406833424433257486392955423632961487886435858434231) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (79 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_79_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (80 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_80 :
    recurrence4Scalar2First.coeff 80 =
      -(((6682032314807883436664827986298510924153638934731100837162745262958419 * 10 ^ 70 +
        0329046568340264936337623437565512794492751699938828232096478727463901) * 10 ^ 70 +
        3150508068030863884041157534835786416539106293352712455635623061476706) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (80 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_80_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (81 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_81 :
    recurrence4Scalar2First.coeff 81 =
      ((((15 * 10 ^ 70 +
        0954763950007491031680715168792879708525236546679143000479731159112256) * 10 ^ 70 +
        6756973046992019728628151746757781024192581332548325840747285649954786) * 10 ^ 70 +
        7170559979736733333372512816995048041851207337663905219330839179880490) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (81 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_81_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (82 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_82 :
    recurrence4Scalar2First.coeff 82 =
      -((((305 * 10 ^ 70 +
        5579088689530356838864305616395977607777075826302993741295629666503400) * 10 ^ 70 +
        7645875598616257678766893188492872686263439705973924622252733817876656) * 10 ^ 70 +
        5461609595002573986012758905948499744050478460499286769581258989376956) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (82 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_82_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (83 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_83 :
    recurrence4Scalar2First.coeff 83 =
      ((((5616 * 10 ^ 70 +
        4890548677659051507383925808185022343761638136895564574721988994767921) * 10 ^ 70 +
        8387409873103077606547871487479562354440998269201014225180850836002089) * 10 ^ 70 +
        2367535900222690799945267768723606970757003436473624858444084955497236) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (83 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_83_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (84 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_84 :
    recurrence4Scalar2First.coeff 84 =
      -((((93691 * 10 ^ 70 +
        0139033089046993438814706021554573088928768475962380066812109484393032) * 10 ^ 70 +
        2126214459435113116747101260857092244481969801325878368062427432590658) * 10 ^ 70 +
        6545496666015221409895451370790470263045266909738378822764805445860805) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (84 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_84_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (85 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_85 :
    recurrence4Scalar2First.coeff 85 =
      ((((1396657 * 10 ^ 70 +
        8908670127185420100726168026091576207244494644219714422235345777407242) * 10 ^ 70 +
        4636649058094290830409738518843165043419450783391306875398573968400279) * 10 ^ 70 +
        9780309824110470195347232311907425023669132884185336320452401789437470) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (85 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (86 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_86 :
    recurrence4Scalar2First.coeff 86 =
      -((((17782627 * 10 ^ 70 +
        3382094662238924851480899405407165550283143324452478197730367683935470) * 10 ^ 70 +
        3946442094362617326575896847010686849511711696310618212843534588015632) * 10 ^ 70 +
        0064317820769830138954666989972172015864715761731131399356988373476091) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (86 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (87 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_87 :
    recurrence4Scalar2First.coeff 87 =
      ((((166261003 * 10 ^ 70 +
        3152771871936109046424736698903726149823117108298110447868465558848743) * 10 ^ 70 +
        8891771506717936137739347476563152697486250038315584976024291673757060) * 10 ^ 70 +
        9630767096820872611327817010873301542367082210160293121946818964199064) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (87 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (88 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_88 :
    recurrence4Scalar2First.coeff 88 =
      -((((177984509 * 10 ^ 70 +
        7316654714756783718923603943114240587347391012190317016424356352358965) * 10 ^ 70 +
        9257349474857118596473836267893852700120287452238539232816853811239849) * 10 ^ 70 +
        6328275619327931647013094435297395409322003961751629077249320464253096) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (88 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (89 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_89 :
    recurrence4Scalar2First.coeff 89 =
      -((((42696901957 * 10 ^ 70 +
        0092561282586221850921808904056147629194992945004711943744862050165947) * 10 ^ 70 +
        9807328656052640706214888674074531878984246032933279062246671613331748) * 10 ^ 70 +
        3487082185622755002727776206404709221070293193225270534340124603196615) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (89 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (90 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_90 :
    recurrence4Scalar2First.coeff 90 =
      ((((1432883111751 * 10 ^ 70 +
        7046499338513372139304312293312885106111474338699435428539203233121119) * 10 ^ 70 +
        0540793940155033981920596808785691026245708194286560459010921885744253) * 10 ^ 70 +
        2936747631137457207365583088603080272953801208831038889587103726702865) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (90 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (91 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_91 :
    recurrence4Scalar2First.coeff 91 =
      -((((34058263442227 * 10 ^ 70 +
        2442319297421609201541791197855565198918072831192715199816688091968064) * 10 ^ 70 +
        8925227247002350920956471176328875462366956845564729350109178150884702) * 10 ^ 70 +
        8943854081572142770446548091457756540982241027198122316773374617133551) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (91 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (92 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_92 :
    recurrence4Scalar2First.coeff 92 =
      ((((692364215552344 * 10 ^ 70 +
        4663439447120087172224153412346580008090331644897209408463187111130442) * 10 ^ 70 +
        3480942685451550023157167726789252169666216595228219037580376867957656) * 10 ^ 70 +
        1535361938428254010866393597427828027912677790748372573882736172794340) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (92 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (93 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_93 :
    recurrence4Scalar2First.coeff 93 =
      -((((12752108709087567 * 10 ^ 70 +
        0029924144488550675263861940792389275024936593441107503306106513607870) * 10 ^ 70 +
        9338989753505540146672497575637146216986153594012147928212209985870610) * 10 ^ 70 +
        2554784607767811324895061678158025584860233152040809093076554604802707) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (93 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (94 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_94 :
    recurrence4Scalar2First.coeff 94 =
      ((((218337659877707388 * 10 ^ 70 +
        2594379115995791963221084809791325332245709010152008593499451492149032) * 10 ^ 70 +
        8628516169299768162361047805319740803088912117324795573066984429653680) * 10 ^ 70 +
        2689071888863733293990509636688869737091475568149037153257175567776022) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (94 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (95 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_95 :
    recurrence4Scalar2First.coeff 95 =
      -((((3523793462810947163 * 10 ^ 70 +
        8515440373184650373154414294205662557867215125093142736635227141207696) * 10 ^ 70 +
        1195186931590605532709628491476472345712562337257173258388200778609493) * 10 ^ 70 +
        4066387653235773906876370235173226290010757170472122539176378150892955) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (95 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (96 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_96 :
    recurrence4Scalar2First.coeff 96 =
      ((((54064294951039715430 * 10 ^ 70 +
        3858470490135770202746758026055153690669954443600433692493359697848531) * 10 ^ 70 +
        0089552157605084062577520552493786030613084257134016863794670266316742) * 10 ^ 70 +
        7679874030129888630490127864926916073369932196310540180240003434941124) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (96 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (97 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_97 :
    recurrence4Scalar2First.coeff 97 =
      -((((793002079636751589880 * 10 ^ 70 +
        6226446904921482154246441899495286479106337874660871925804306854040425) * 10 ^ 70 +
        7141171002155770739689637384211797635117412991256930406664520075406350) * 10 ^ 70 +
        6854889498314410385649581734132301162371098115047284827221918243304771) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (97 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (98 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_98 :
    recurrence4Scalar2First.coeff 98 =
      ((((11164273970878402524102 * 10 ^ 70 +
        1921769159879135742846409374729525683742156495400060057683438851734969) * 10 ^ 70 +
        2561095813780822410357362660601712033658358592030541906691878646357771) * 10 ^ 70 +
        4439725743766677657019645824216376072632135681155024722224716085194001) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (98 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (99 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_99 :
    recurrence4Scalar2First.coeff 99 =
      -((((151308054254171207330272 * 10 ^ 70 +
        5743014546228431946532467207034704007057827875259380366797099863814550) * 10 ^ 70 +
        6222135319923453222336748945017186473850027991187954048371597693852024) * 10 ^ 70 +
        7101066678318082924919656850522718922017864669743348273972754936198731) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (99 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (100 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_100 :
    recurrence4Scalar2First.coeff 100 =
      ((((1978604970356656715082848 * 10 ^ 70 +
        3814168001645782444988866185798336529651899364130275214700515883102186) * 10 ^ 70 +
        0101137424090048117889448761201428823905439464520090965152272486801686) * 10 ^ 70 +
        2588730837042123496508862624335158424317299514475709808418130028328877) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (100 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (101 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_101 :
    recurrence4Scalar2First.coeff 101 =
      -((((25009811111052228783191030 * 10 ^ 70 +
        0028480890408609195817497510150233314474522960262145579887866761961108) * 10 ^ 70 +
        4960206990619198657657612444406061679585120009362620964827769355197630) * 10 ^ 70 +
        8443036182621360320675184678113760270605250627886643035781687735949362) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (101 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (102 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_102 :
    recurrence4Scalar2First.coeff 102 =
      ((((306028081568229815756907603 * 10 ^ 70 +
        5657248494790005871967944382883896211961067226350030295108821261338590) * 10 ^ 70 +
        8079565969275609274871480803748483851671261019816031423120819839583660) * 10 ^ 70 +
        9004033063424695728942866484412847651617948786605707214564154180416974) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (102 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (103 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_103 :
    recurrence4Scalar2First.coeff 103 =
      -((((3629539404924567344489184055 * 10 ^ 70 +
        8974521800616857378585176412793624010361239371606687169333584689607225) * 10 ^ 70 +
        3906163819205710540671904691603011696877615522248755571552522050759146) * 10 ^ 70 +
        3161698367540579725860692798226409921511581985999324554321750398064423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (103 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (104 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_104 :
    recurrence4Scalar2First.coeff 104 =
      ((((41767776708383139998818475053 * 10 ^ 70 +
        9471375059285673927374330589794691751186595392193242032021216327376997) * 10 ^ 70 +
        1967797138278335725673561970800682404762561888296784206781395713092387) * 10 ^ 70 +
        6191272195407570574926585048567572263466336673162025703040063648669727) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (104 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (105 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_105 :
    recurrence4Scalar2First.coeff 105 =
      -((((466798692824878348366852732033 * 10 ^ 70 +
        6360348727229808144705470410196859144928546506756649157885865909579006) * 10 ^ 70 +
        9094853635803137563062610068197486971237055401367023429327029452417969) * 10 ^ 70 +
        9936426270323296108281877275411803372402697034190152834866642648974282) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (105 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (106 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_106 :
    recurrence4Scalar2First.coeff 106 =
      ((((5070687082214435352188156503249 * 10 ^ 70 +
        5116425822926958983275431222810887065996559177550649614254978192236133) * 10 ^ 70 +
        5615615100078493727473127382787633821964418522677998260927838848536187) * 10 ^ 70 +
        2617860655406078224230199240956421701699128968195799016559651454059012) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (106 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (107 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_107 :
    recurrence4Scalar2First.coeff 107 =
      -((((53575303667442805796331375514617 * 10 ^ 70 +
        9865485424475993500360564104988513540312380913612598852742288873282571) * 10 ^ 70 +
        4773545145308252854790677592241194606318811338116492340745250098783153) * 10 ^ 70 +
        0553841898319413381590593361974504544587162747397013742140604765797690) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (107 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (108 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_108 :
    recurrence4Scalar2First.coeff 108 =
      ((((550938790015510281724155928536395 * 10 ^ 70 +
        6379231919475036893729747999612005204493127984574936085613518170982824) * 10 ^ 70 +
        9710720105353791826562678013526679947321981994871406439367227305142875) * 10 ^ 70 +
        8146735515933922090601447427016086922078783545014097616805816688073747) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (108 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (109 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_109 :
    recurrence4Scalar2First.coeff 109 =
      -((((5517434129952467743848996869119072 * 10 ^ 70 +
        6986813225781040218815809940773831709098750799109388254217294830070963) * 10 ^ 70 +
        0535002345244826402998495229610255098842530682132452643234168150058877) * 10 ^ 70 +
        1699075320530413516098114882903946904960411464961719505396523684908328) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (109 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (110 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_110 :
    recurrence4Scalar2First.coeff 110 =
      ((((53839192640011075703156528932112171 * 10 ^ 70 +
        1300280763332949319277807017101971818867630810235477645244526616807159) * 10 ^ 70 +
        6535362418241488410629751154042531081843233509682426846114158594989247) * 10 ^ 70 +
        8936625251888109251006176113341983284641941962348302963591650382211301) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (110 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (111 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_111 :
    recurrence4Scalar2First.coeff 111 =
      -((((512155208759918027906941103513909716 * 10 ^ 70 +
        6454465553577528908526734040525881320027010638336460470882251275269379) * 10 ^ 70 +
        3177581982057558163997789924931038458929425313426456824675970646110204) * 10 ^ 70 +
        2482824558546644326344460274256900576309925091388348242133481105764277) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (111 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (112 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_112 :
    recurrence4Scalar2First.coeff 112 =
      ((((4751652961854533575847637468301158515 * 10 ^ 70 +
        4501466192172408468620688165712376849501938260079374608010753169902702) * 10 ^ 70 +
        6747172158203600053861699421895654123411051647496834110675545980228640) * 10 ^ 70 +
        7547922677970313959416000351058155257564505867225974876251933956538763) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (112 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (113 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_113 :
    recurrence4Scalar2First.coeff 113 =
      -((((43014288004510307670418219616728530443 * 10 ^ 70 +
        8606276728599619522540940243448843979908544957176296208048110506205922) * 10 ^ 70 +
        3185998111579768139768572400922895920118645911601804368755079049885662) * 10 ^ 70 +
        8654810483318236092009901810341687346221600818235845892949677630625182) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (113 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (114 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_114 :
    recurrence4Scalar2First.coeff 114 =
      ((((380083228766319827272342637618852446349 * 10 ^ 70 +
        7957298824505523798519969014035016835306620868680226217147203569474556) * 10 ^ 70 +
        4440864405504117200759706746172918833609068018688088639075937935170440) * 10 ^ 70 +
        9557695961958347299102558910751121873472346013654059084044230005555294) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (114 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (115 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_115 :
    recurrence4Scalar2First.coeff 115 =
      -((((3279482372270865503740212175211301606536 * 10 ^ 70 +
        6823401925598304644335716898629413646561331150801781675745039157540927) * 10 ^ 70 +
        0027385259463964976659736175260340516460529750072829839934451802169482) * 10 ^ 70 +
        7515485291531929275594691830472308501888759903320781185817975283227207) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (115 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (116 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_116 :
    recurrence4Scalar2First.coeff 116 =
      ((((27640509303993290184067007620558686727634 * 10 ^ 70 +
        6002831394901258825309478708006179017632084825161044121037214561259719) * 10 ^ 70 +
        4252180409485042606450455121651338717330068967800440454283934715620242) * 10 ^ 70 +
        2499775454375745495658316505128555954885022130720100685257662645362300) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (116 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (117 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_117 :
    recurrence4Scalar2First.coeff 117 =
      -((((227638798662496372143824359626763728730367 * 10 ^ 70 +
        4223287312499776397837419784200683932280678417584586522976604296586912) * 10 ^ 70 +
        7276203685413630562746141776355988644177881847662330870344130355857436) * 10 ^ 70 +
        1246576338056323358504955843261671600376520188789341387604681074257527) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (117 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (118 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_118 :
    recurrence4Scalar2First.coeff 118 =
      ((((1832500366179318300894875569787411690800673 * 10 ^ 70 +
        0656618228847497190475259836876301391893904728052728849956784631199168) * 10 ^ 70 +
        5179594927571751124049740272992257864861271690562299377461982929396778) * 10 ^ 70 +
        7481386604935521915189942023474567538290047936379490207743432902904665) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (118 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (119 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_119 :
    recurrence4Scalar2First.coeff 119 =
      -((((14423505644739122673251302835568060959482968 * 10 ^ 70 +
        2192623148635371372784625229273836037287306292823716924139054392424493) * 10 ^ 70 +
        4368719574329232693698468927330509579617032410187981696171761537267577) * 10 ^ 70 +
        2201844691037362372600496949423968856117885389698958461087270561333056) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (119 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (120 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_120 :
    recurrence4Scalar2First.coeff 120 =
      ((((111032980958396456718229287344956724038802617 * 10 ^ 70 +
        4536964986726047158054179813773534499727342612080614986739350442997932) * 10 ^ 70 +
        5644081409639561767583683743863623379406385702088471809796037373537988) * 10 ^ 70 +
        2247799284370231683115967481118763367804711068469714993402754368672520) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (120 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (121 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_121 :
    recurrence4Scalar2First.coeff 121 =
      -((((836194973345270414596752357437001786473306752 * 10 ^ 70 +
        5742718769263194876626164117936885316541365717244021173075036027400310) * 10 ^ 70 +
        4082203680384724872901475884635853422005049350459211364196490994903847) * 10 ^ 70 +
        7102586033154938012887580537661278663302075754752346709855875308376583) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (121 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (122 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_122 :
    recurrence4Scalar2First.coeff 122 =
      ((((6162436300665298414933358003318706547799071911 * 10 ^ 70 +
        0958915335221186282981270647007241621436021906913997715104407043059085) * 10 ^ 70 +
        6715941884270263927272804575350000986951936596293311746955570654146164) * 10 ^ 70 +
        7596491814881642844144086273556135565548114961292862653207578448558930) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (122 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (123 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_123 :
    recurrence4Scalar2First.coeff 123 =
      -((((44452583723260221616531704658261803350476805995 * 10 ^ 70 +
        6312084708390738860497410515832823514880839013777815236193685142073180) * 10 ^ 70 +
        9417743259962563962974055656938793108559045754976474722481058230283693) * 10 ^ 70 +
        4341736800113611833633508903134172361569775458693570325179636836709526) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (123 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (124 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_124 :
    recurrence4Scalar2First.coeff 124 =
      ((((313940476497281691617482364392623943830638781683 * 10 ^ 70 +
        7876925828739994806013583604438750558061142719600913964252772610095356) * 10 ^ 70 +
        3356382867540870497669522043641068344106508281391744983758480915579173) * 10 ^ 70 +
        5787876913321114998273886227330324252355540552867785668029903404144362) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (124 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (125 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_125 :
    recurrence4Scalar2First.coeff 125 =
      -((((2171228104549292761457640894452265310819507532537 * 10 ^ 70 +
        8298725122642024022172816262521075293963522935937172314479629044028307) * 10 ^ 70 +
        9705891930972056078021510641743272189341548678071504453759517802874989) * 10 ^ 70 +
        5038863787171140624065700833663033062362026161781364970280736733815562) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (125 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (126 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_126 :
    recurrence4Scalar2First.coeff 126 =
      ((((14708548593952892688182925718433744392328080377304 * 10 ^ 70 +
        8380171270853059882544667009197285407197800971952386585550740935164793) * 10 ^ 70 +
        0633011169954210512926774486926619311593451873901871833338875271333553) * 10 ^ 70 +
        4623610952744324467739170592950502266132910396686618181640253212224192) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (126 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (127 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_127 :
    recurrence4Scalar2First.coeff 127 =
      -((((97619223485029929144740021790225189675296752263142 * 10 ^ 70 +
        1841446227946086234546296025715877917047969936571122297459328300088248) * 10 ^ 70 +
        0220739026259856018930579989196142059625898594329760396533217998970784) * 10 ^ 70 +
        7885729085437381765326813996005555496003583389418329988285202716125649) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (127 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (128 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_128 :
    recurrence4Scalar2First.coeff 128 =
      ((((634883033694283842744973292531394938054807029222850 * 10 ^ 70 +
        4964855201696430211823243280347740443019519271170580982578740970293013) * 10 ^ 70 +
        0863505840861485352504259608200133316111233624386603533257324140800133) * 10 ^ 70 +
        8418016911015437071772754897171099767481038874674680401365311606511960) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (128 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (129 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_129 :
    recurrence4Scalar2First.coeff 129 =
      -((((4047003310093983672198701491894589628715421853284332 * 10 ^ 70 +
        0188206742192678479119755150956844415120525338356987687978941316360225) * 10 ^ 70 +
        0139829979381376187559357222238239480818443653012405770096874144718959) * 10 ^ 70 +
        5174661622291250387268070909832835105316209590345460952495231555415682) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (129 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (130 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_130 :
    recurrence4Scalar2First.coeff 130 =
      ((((25289520559213851905682441535049970912584801560364978 * 10 ^ 70 +
        1972131869418955341368714177087158706133126039801970574387444230441752) * 10 ^ 70 +
        7276151006559253998684080495550065464133826057374368519827539505253727) * 10 ^ 70 +
        7758488534966238526541329495457550675498086482476700165502496455021148) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (130 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (131 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_131 :
    recurrence4Scalar2First.coeff 131 =
      -((((154952228859783351879638014195994713256399153526952415 * 10 ^ 70 +
        4731894644611948038431658108202174650296533244947269889151161985301128) * 10 ^ 70 +
        9208963794609308104215473683925468257118576507176022130589930315450046) * 10 ^ 70 +
        3875005583284796125950427242035735821257431841326828318590674026917375) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (131 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (132 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_132 :
    recurrence4Scalar2First.coeff 132 =
      ((((931077120897260846760369980279347068685350624354172526 * 10 ^ 70 +
        2846443707838045269225266384458180639937023981235616673940599613871363) * 10 ^ 70 +
        1728936072130642332394193820449401999871828794073603913944001927981523) * 10 ^ 70 +
        6883815667361098006609472407045865209214118023459571623631492384269024) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (132 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (133 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_133 :
    recurrence4Scalar2First.coeff 133 =
      -((((5487594463700305956490617437546322021709208934805893394 * 10 ^ 70 +
        1574945112663054724364136989651274226477704484918188532283261061082692) * 10 ^ 70 +
        1079216917411747016369990829510240795588150723634299048263523356228330) * 10 ^ 70 +
        8002481367685814488295967792267615993116577133896759200348832273921117) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (133 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (134 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_134 :
    recurrence4Scalar2First.coeff 134 =
      ((((31729444393711154060335902250989777163795506580744006932 * 10 ^ 70 +
        8789745041461197944927477647304204811962087156596944138286289673662909) * 10 ^ 70 +
        7262921013253163253407819825859768878556803235969372530647890654675817) * 10 ^ 70 +
        0413510834644384320450876390966784362102682308125478715063478903900280) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (134 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (135 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_135 :
    recurrence4Scalar2First.coeff 135 =
      -((((180011544192083890856624659995347251574532967512848386265 * 10 ^ 70 +
        3431824470914981603605145987148838377644871815097350586675220048781099) * 10 ^ 70 +
        7043327682544307377854478258931887718082673080832233784121077701426938) * 10 ^ 70 +
        4927014149520823771181033860629934288689280844482664366058576040874083) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (135 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (136 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_136 :
    recurrence4Scalar2First.coeff 136 =
      ((((1002228748330007235886381119128549344503174451882293596986 * 10 ^ 70 +
        1781157804698553471892814544257276487289092422749573536965906358421583) * 10 ^ 70 +
        5138657786674785282854536506702685459910898840526950421368788617607739) * 10 ^ 70 +
        6690404415925987496546977619265437708853606906742804623694546449620730) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (136 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (137 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_137 :
    recurrence4Scalar2First.coeff 137 =
      -((((5476852908987378148662580912658001297812529235053988949859 * 10 ^ 70 +
        7939355404293759555348538896981105136740804733147039565238874682278611) * 10 ^ 70 +
        4161489851166606561920114908446662963543910364103351157258755437516854) * 10 ^ 70 +
        1278759846489516820094451008092647186952272438841964405901141191845018) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (137 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (138 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_138 :
    recurrence4Scalar2First.coeff 138 =
      ((((29380565805858881903260830581584462513145094313736850295126 * 10 ^ 70 +
        3758508761050444788056910741089775443341099927735775806965841492434755) * 10 ^ 70 +
        4216962494851861820083761514705062804046647104127002840943295531398730) * 10 ^ 70 +
        5894243587083591608972071167241172309949260072101477829334086538886843) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (138 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (139 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_139 :
    recurrence4Scalar2First.coeff 139 =
      -((((154745960008811971184850981776125429688811549819227934318774 * 10 ^ 70 +
        2431944973469564452463242385877330879572895706120345897083325795326655) * 10 ^ 70 +
        8374051304667599235357971092579035431440570532111743253171363068297521) * 10 ^ 70 +
        7131323694536410990461072329292061387678182873292802152997317776610780) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (139 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (140 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_140 :
    recurrence4Scalar2First.coeff 140 =
      ((((800335291703524337270644256600183919153212001938722028571333 * 10 ^ 70 +
        2280690219675111077699487342490365441531340784200688565829759749628838) * 10 ^ 70 +
        9831502117930350759202597326261760862859893358942635772787034307937230) * 10 ^ 70 +
        7496364424641887611823538844948322538361078108471835787919725169512302) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (140 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (141 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_141 :
    recurrence4Scalar2First.coeff 141 =
      -((((4065179535766720550622721822734078195225240907255434289450499 * 10 ^ 70 +
        7327846069929714903218342772292597700338877861420857803357328909034321) * 10 ^ 70 +
        1487621640497160444388942289799058648089890397262254686790855607952064) * 10 ^ 70 +
        6267366125680878178826173002371838967416544286545885253427187055721043) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (141 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (142 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_142 :
    recurrence4Scalar2First.coeff 142 =
      ((((20281614912343762060350662769181219574269230401286300485844365 * 10 ^ 70 +
        3131251865406317611461254295500473526178068294768297575531107252747278) * 10 ^ 70 +
        4194620810398510934704859819737419871397489254364211618954639420327826) * 10 ^ 70 +
        2187049389445259364908868690390263684749461873531989316388413729677877) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (142 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (143 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_143 :
    recurrence4Scalar2First.coeff 143 =
      -((((99402807570212626575370619430044987669369779475402788395860961 * 10 ^ 70 +
        5157594635120212788860820102475707499292450140014704954209763069364763) * 10 ^ 70 +
        7093198577729290726512307029498686640881704348473228432232736513493823) * 10 ^ 70 +
        1382555421339408985603251978259982856536696753857218895944094566230769) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (143 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (144 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_144 :
    recurrence4Scalar2First.coeff 144 =
      ((((478657391794455437085720954120945205981823008579079881210100442 * 10 ^ 70 +
        8899970425427723852816494345126866562136323068118027212701457132160645) * 10 ^ 70 +
        3658897014837890724545418294381636624255309807606031976961302539058777) * 10 ^ 70 +
        3088641613339754698579358394622600240431151926744611649756134197752305) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (144 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (145 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_145 :
    recurrence4Scalar2First.coeff 145 =
      -((((2264832201462555152110211081582827500386084369857531286895159091 * 10 ^ 70 +
        5376379660254241699443120352858581514888085239714653912042008820068707) * 10 ^ 70 +
        2339354875771638049990170041607287415292086374731616357932850819625324) * 10 ^ 70 +
        8214622349203494638263284021720308511425710920111703744829600722104882) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (145 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (146 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_146 :
    recurrence4Scalar2First.coeff 146 =
      ((((10531399354504203319202116218534021209728659131486883391275625056 * 10 ^ 70 +
        5876131367179353019718819201243092270755922927950029671584923521963761) * 10 ^ 70 +
        9678238719255338040708691441217667565110629828949118867535129538300657) * 10 ^ 70 +
        2151742358009415772239488223456163198157646896985225380797564862819266) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (146 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (147 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_147 :
    recurrence4Scalar2First.coeff 147 =
      -((((48131247651155045773012313399937320940597665023323872368310639032 * 10 ^ 70 +
        8740493475061944518688304183575967728897320041971670292442702717504147) * 10 ^ 70 +
        8472460711378288049392899154291090601000113641519728965415877969326737) * 10 ^ 70 +
        9521820095400098371513243643307303179404085659977363293320317535531796) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (147 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (148 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_148 :
    recurrence4Scalar2First.coeff 148 =
      ((((216227007012734650162536268463803302100986157852094626882741255464 * 10 ^ 70 +
        2792898957056807273675000693536971197428932609329228876539831817026231) * 10 ^ 70 +
        4016529445866094619260105047258370425936663340001335974332963179124245) * 10 ^ 70 +
        7486409533233085220591710791057702311682980139532183897422348397190694) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (148 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (149 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_149 :
    recurrence4Scalar2First.coeff 149 =
      -((((954957317060552086028017964034540157093661255466558147487954716657 * 10 ^ 70 +
        1398134139029240096683460323066625779036047892413164582975907339662702) * 10 ^ 70 +
        3585696964987479529201253927185516064258333820241187742691252320899433) * 10 ^ 70 +
        9017183429102095270289543895855349420442808819535133818583939733867350) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (149 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (150 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_150 :
    recurrence4Scalar2First.coeff 150 =
      ((((4146649154259387421540851083906629545611884523484038086141355165734 * 10 ^ 70 +
        5502093027156925249005805560584512925291717845117647462889867369826255) * 10 ^ 70 +
        0010051135889964862405471587663314398160632807988225743644627617116320) * 10 ^ 70 +
        0048980499450348128970988669131063874652723461070710152274500087867423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (150 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (151 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_151 :
    recurrence4Scalar2First.coeff 151 =
      -((((17705032990267336746824923810006323018691640958673383023330754456779 * 10 ^ 70 +
        6540005836472031547928415829022918156974559221822795502767226243548794) * 10 ^ 70 +
        7501829310729069594860231553713429365854786863153747494608791322665201) * 10 ^ 70 +
        7363587085608982450652563870243516182691078365286143305470108798528552) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (151 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (152 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_152 :
    recurrence4Scalar2First.coeff 152 =
      ((((74340908478625699504379446910320593358486053230790520712313931612675 * 10 ^ 70 +
        4964151685751705274697732189142259362181429670897074096722155988577668) * 10 ^ 70 +
        6935955345676248558283244137574935314444414555736768906273852284070017) * 10 ^ 70 +
        7895571007031016052848632634818676996527834667876824120163130322455818) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (152 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (153 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_153 :
    recurrence4Scalar2First.coeff 153 =
      -((((306997613202565783579107356091263989512946323302195733320993186550060 * 10 ^ 70 +
        3043979126663146248063890552791211743159987375444269606931713137092989) * 10 ^ 70 +
        1057079896296276500342052424615828991358658123509296144156961808365346) * 10 ^ 70 +
        2904488261338181274359345337125477872383871311809088131893263423046295) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (153 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (154 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_154 :
    recurrence4Scalar2First.coeff 154 =
      ((((1246985183026721541918874282389713707488161750632476708647849746626016 * 10 ^ 70 +
        2474332267131400380479647472066484815371415074504368538233515002367940) * 10 ^ 70 +
        2506207412737678141480689167036865057837862416065696680770570151103420) * 10 ^ 70 +
        6245156650281203292933971246751982305313740702628704814739253607662152) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (154 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (155 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_155 :
    recurrence4Scalar2First.coeff 155 =
      -((((4982516400249822411939906348293609830007470129577830800984867865666726 * 10 ^ 70 +
        2270600711004488145708153135770840130391685179382025922417763701000451) * 10 ^ 70 +
        4075319454100652063733472960672368108407675086560380556755755155928949) * 10 ^ 70 +
        8739409887924417722227487497396036780637745347136999229174849727661452) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (155 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (156 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_156 :
    recurrence4Scalar2First.coeff 156 =
      (((((1 * 10 ^ 70 +
        9585659180697986698464935028558997928739341676122464195302062405073455) * 10 ^ 70 +
        0523497892762364070885386378261778909039344653527657097301816136135623) * 10 ^ 70 +
        6735735600212725120376084551588755861257768369686868805399982521201113) * 10 ^ 70 +
        7443610060549382379743633051479398100646910284050243566341263165013876) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (156 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (157 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_157 :
    recurrence4Scalar2First.coeff 157 =
      -(((((7 * 10 ^ 70 +
        5747695416222010917966834515496075331629943329153327153326858121924403) * 10 ^ 70 +
        6283090730679536312379328202901599996850755465261831007115778762130798) * 10 ^ 70 +
        0554138124942248620335226279639830337763515302957066233647038839360587) * 10 ^ 70 +
        0121593401775430145780980751948866191301649529172194364808365006772433) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (157 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (158 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_158 :
    recurrence4Scalar2First.coeff 158 =
      (((((28 * 10 ^ 70 +
        8257835855162873403576699626767489829624793963711278790965780171901728) * 10 ^ 70 +
        5018519543838774035846867642058257695782449141533850480154092156558147) * 10 ^ 70 +
        6035785975590620901844905669431696543075454449684075993765829481229897) * 10 ^ 70 +
        3270728186209123104102328194236184221643251416281859691822952653174870) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (158 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (159 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_159 :
    recurrence4Scalar2First.coeff 159 =
      -(((((107 * 10 ^ 70 +
        9470878451638148365580250861970468726797501756935642310966856470770803) * 10 ^ 70 +
        7831681582040418343821307993392325039336970259753688083983167997660414) * 10 ^ 70 +
        9779861915009868955236071478776233399841051206037411278361428654949440) * 10 ^ 70 +
        9096144851345720223609109322906099307537721850777042524548559912693787) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (159 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (160 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_160 :
    recurrence4Scalar2First.coeff 160 =
      (((((397 * 10 ^ 70 +
        8281177927295801055425563689587959255899986307745727414817065448050015) * 10 ^ 70 +
        8727716434429854002097946793145395948000618948128249986041773655126431) * 10 ^ 70 +
        2207851772261117537202097936076093589001686744809964481776219768565719) * 10 ^ 70 +
        2180461267504590215906939299447282914862987805056044101701448909623697) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (160 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (161 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_161 :
    recurrence4Scalar2First.coeff 161 =
      -(((((1443 * 10 ^ 70 +
        0134635539137491055454102465884851170297373044794049113797826035473777) * 10 ^ 70 +
        6927580810577956344353352118647621464280389749324350469270952788203294) * 10 ^ 70 +
        5246840971751434673309266305553826626136589593163008498704335489527596) * 10 ^ 70 +
        6819272259287132624998937811203701933427047437464179796398103903041379) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (161 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (162 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_162 :
    recurrence4Scalar2First.coeff 162 =
      (((((5151 * 10 ^ 70 +
        9342294604044035799888419592860247511097459238547312945477989385139162) * 10 ^ 70 +
        4468338754837650206289201360497120537374474713196134463807315916510091) * 10 ^ 70 +
        1703695953116785098813640542552052327172651153238204230788911476310885) * 10 ^ 70 +
        6401423590827722961021030516735052490106445301439039127890839817203175) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (162 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (163 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_163 :
    recurrence4Scalar2First.coeff 163 =
      -(((((18106 * 10 ^ 70 +
        2686886842230521461831948386470578567664848550544334794227217375898904) * 10 ^ 70 +
        1406451358882189096465888782922149288021497251681951936270252425479450) * 10 ^ 70 +
        5373650121956286272356066185693957083578814462174190751338169909582069) * 10 ^ 70 +
        3541763064638239414809431548281436187795697050559109576048659054736787) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (163 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (164 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_164 :
    recurrence4Scalar2First.coeff 164 =
      (((((62643 * 10 ^ 70 +
        9467455537495201072063165255954398158567685653183290970551881404006870) * 10 ^ 70 +
        6164839325880133862341663298609116887065191345214923695202956209232681) * 10 ^ 70 +
        5463297981523869130273974193212195262049197323464450256204455046866152) * 10 ^ 70 +
        0652884387774462420588598997316858449396607839838924935543722270688972) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (164 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (165 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_165 :
    recurrence4Scalar2First.coeff 165 =
      -(((((213379 * 10 ^ 70 +
        4697875622817213079455875836230566249721150350743170899100329599887857) * 10 ^ 70 +
        7310624135640886640309724728746327818522341910504023265604606568926847) * 10 ^ 70 +
        1505391191393127901225088219018624594477197654411537716308742917082443) * 10 ^ 70 +
        2936935225096956329312020634358518059043865786524176603739869274161424) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (165 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (166 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_166 :
    recurrence4Scalar2First.coeff 166 =
      (((((715616 * 10 ^ 70 +
        7582755540689082420339242413167911986388647916066631015681170011488384) * 10 ^ 70 +
        7093685895563513124852776393605820143476414774046407727158523644683717) * 10 ^ 70 +
        7910265068350385539490469267321960041656401320363880385776216377365111) * 10 ^ 70 +
        9434294108600596354587485854895290410864781287914590517854732154537071) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (166 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (167 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_167 :
    recurrence4Scalar2First.coeff 167 =
      -(((((2363158 * 10 ^ 70 +
        4249501193626123291519358709433106406500376571254393187408125771584521) * 10 ^ 70 +
        4810010811358234059667237889773069594003803033082554268357289887777540) * 10 ^ 70 +
        9288562587272146936936696053343649778692647401729833741506408832278386) * 10 ^ 70 +
        7848419964419122202011115467393190370401686842779443603307212329549969) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (167 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (168 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_168 :
    recurrence4Scalar2First.coeff 168 =
      (((((7684558 * 10 ^ 70 +
        1630199865498522550864673098485247738269740851331145061608613588273539) * 10 ^ 70 +
        8288118749805618646200742805067366396213061327133199797378565394012005) * 10 ^ 70 +
        8266418162092923103188118197618002594189902432084453038207607815236155) * 10 ^ 70 +
        4978396115661421550766011551373894830242439733246703779550649762031361) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (168 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (169 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_169 :
    recurrence4Scalar2First.coeff 169 =
      -(((((24608612 * 10 ^ 70 +
        6204056318763424557022648447242611406723534389239986259718609275482932) * 10 ^ 70 +
        1840784688829562103040948823214801868481626042365998454174620223242809) * 10 ^ 70 +
        1152791120066236253907704220132541730363245204038815075705673460850169) * 10 ^ 70 +
        1394045440374798236856129144884762899454933607076956386513451376981874) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (169 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (170 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_170 :
    recurrence4Scalar2First.coeff 170 =
      (((((77611332 * 10 ^ 70 +
        7339032365695888581503346677456928228628410468568237115580230810823091) * 10 ^ 70 +
        5777429130272270265249930096095915303559510754809512149759817326425607) * 10 ^ 70 +
        1791194431820914256571696602618269946096659304847276836644591226487453) * 10 ^ 70 +
        1123427408891979116992579862953658020484911394586749364391750786975136) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (170 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
