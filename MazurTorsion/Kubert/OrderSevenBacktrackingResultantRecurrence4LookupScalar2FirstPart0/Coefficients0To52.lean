/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
