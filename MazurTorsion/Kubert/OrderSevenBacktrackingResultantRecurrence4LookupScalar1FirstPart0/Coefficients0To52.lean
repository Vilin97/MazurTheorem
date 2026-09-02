/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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

private theorem recurrence4Scalar1First_coeff_0_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (0 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (0 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_0 :
    recurrence4Scalar1First.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (0 - x)) = _
  rw [show 1 = 1 +
    0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_0_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_1_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (1 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (1 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_1 :
    recurrence4Scalar1First.coeff 1 =
      (-83921241414679494612514457632606701454786560 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (1 - x)) = _
  rw [show 2 = 1 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_1_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_2_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (2 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (2 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_2 :
    recurrence4Scalar1First.coeff 2 =
      (755720455248389530300398836042458145231921405952 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (2 - x)) = _
  rw [show 3 = 1 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_2_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_3_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (3 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (3 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_3 :
    recurrence4Scalar1First.coeff 3 =
      (-2508464416318493024073950905368412761160370779436544 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (3 - x)) = _
  rw [show 4 = 1 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_3_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_4_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (4 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (4 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_4 :
    recurrence4Scalar1First.coeff 4 =
      (3424997062089538418437735461688297806132496909889284992 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (4 - x)) = _
  rw [show 5 = 1 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_4_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_5_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (5 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (5 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_5 :
    recurrence4Scalar1First.coeff 5 =
      (189654811169388450017263673475555333579509073549440171424 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (5 - x)) = _
  rw [show 6 = 1 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_5_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_6_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (6 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (6 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_6 :
    recurrence4Scalar1First.coeff 6 =
      (-6963871838947980811918702695455460414417060948566410552958736 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (6 - x)) = _
  rw [show 7 = 1 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_6_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_7_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (7 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (7 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_7 :
    recurrence4Scalar1First.coeff 7 =
      (9922442307317059931713646142343991127570937169188664901567055464 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (7 - x)) = _
  rw [show 8 = 1 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_7_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_8_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (8 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (8 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_8 :
    recurrence4Scalar1First.coeff 8 =
      (-6832908761679528931317110691808838093746078136846256309090786638020 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (8 - x)) = _
  rw [show 9 = 1 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_8_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_9_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (9 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (9 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_9 :
    recurrence4Scalar1First.coeff 9 =
      (2689346335338665652936184569676131828434689251833930198673951075042976 : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (9 - x)) = _
  rw [show 10 = 1 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_9_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_10_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (10 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (10 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_10 :
    recurrence4Scalar1First.coeff 10 =
      -((77 * 10 ^ 70 +
        6336955848046617127294957053702182462942399775518340533578607562730994) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (10 - x)) = _
  rw [show 11 = 1 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_10_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_11_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (11 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (11 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_11 :
    recurrence4Scalar1First.coeff 11 =
      ((27797 * 10 ^ 70 +
        5985320553296031520745717776465414902701064559782133748746554838747962) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (11 - x)) = _
  rw [show 12 = 1 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_11_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_12_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (12 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (12 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_12 :
    recurrence4Scalar1First.coeff 12 =
      -((9725821 * 10 ^ 70 +
        5539380773441982446850712128148393798192609483087260935038556552150718) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (12 - x)) = _
  rw [show 13 = 1 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_12_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_13_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (13 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (13 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_13 :
    recurrence4Scalar1First.coeff 13 =
      ((353062902 * 10 ^ 70 +
        0076236152189380126829840713492955948701938056745809673303046821531582) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (13 - x)) = _
  rw [show 14 = 1 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_13_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_14_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (14 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (14 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_14 :
    recurrence4Scalar1First.coeff 14 =
      ((1603452813540 * 10 ^ 70 +
        6230545848618260432873123213282622122936586163621328167563595607261726) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (14 - x)) = _
  rw [show 15 = 1 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_14_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_15_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (15 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (15 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_15 :
    recurrence4Scalar1First.coeff 15 =
      -((717384148963929 * 10 ^ 70 +
        9364752718098076276267621099517988531640045055330221266251448300743563) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (15 - x)) = _
  rw [show 16 = 1 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_15_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_16_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (16 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (16 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_16 :
    recurrence4Scalar1First.coeff 16 =
      ((52131950749769755 * 10 ^ 70 +
        7584798262323255329500894668067865214233114290503470698058301919407237) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (16 - x)) = _
  rw [show 17 = 1 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_16_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_17_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (17 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (17 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_17 :
    recurrence4Scalar1First.coeff 17 =
      ((63585837482009695225 * 10 ^ 70 +
        8558234069105983583072186085184337876100239887011799799506899236343550) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (17 - x)) = _
  rw [show 18 = 1 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_17_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_18_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (18 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (18 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_18 :
    recurrence4Scalar1First.coeff 18 =
      -((19742197688587044657839 * 10 ^ 70 +
        1721587418981396353110430102936583986388250230924185356498402144158136) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (18 - x)) = _
  rw [show 19 = 1 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_18_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_19_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (19 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (19 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_19 :
    recurrence4Scalar1First.coeff 19 =
      -((6051894335397930196383994 * 10 ^ 70 +
        4854978597051294571115594350404180625293578834960586273191257513074912) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (19 - x)) = _
  rw [show 20 = 1 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_19_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_20_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (20 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (20 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_20 :
    recurrence4Scalar1First.coeff 20 =
      ((7213705877891596789105406644 * 10 ^ 70 +
        6529832007836710392806813928213296519954661726436543680841055850749201) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (20 - x)) = _
  rw [show 21 = 1 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_20_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_21_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (21 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (21 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_21 :
    recurrence4Scalar1First.coeff 21 =
      -((3219888279753296615070556680317 * 10 ^ 70 +
        3645226301976690379580885455361202312374224135116032529884358012071039) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (21 - x)) = _
  rw [show 22 = 1 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_21_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_22_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (22 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (22 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_22 :
    recurrence4Scalar1First.coeff 22 =
      ((926603025311867555557812463585745 * 10 ^ 70 +
        5093961152667778440015685693165882992704792120628746494183596245801160) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (22 - x)) = _
  rw [show 23 = 1 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_22_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_23_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (23 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (23 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_23 :
    recurrence4Scalar1First.coeff 23 =
      -((187958511267445165566769524244690134 * 10 ^ 70 +
        2839118109268216877968636322648178323958510949786474606270817782287972) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (23 - x)) = _
  rw [show 24 = 1 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_23_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_24_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (24 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (24 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_24 :
    recurrence4Scalar1First.coeff 24 =
      ((27492306543626947925427366255336411023 * 10 ^ 70 +
        9819772633147297966568249188210234112917970670765072612313934724848501) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (24 - x)) = _
  rw [show 25 = 1 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_24_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_25_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (25 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (25 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_25 :
    recurrence4Scalar1First.coeff 25 =
      -((3513391992147239777574098148479189620394 * 10 ^ 70 +
        2438578302748512700314573653331777947693830410494263261836795897761252) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (25 - x)) = _
  rw [show 26 = 1 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_25_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_26_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (26 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (26 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_26 :
    recurrence4Scalar1First.coeff 26 =
      ((883593466274621906223991240474939195322811 * 10 ^ 70 +
        2979477366505944778796837206384992313310904773746868929598971625170777) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (26 - x)) = _
  rw [show 27 = 1 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_26_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_27_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (27 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (27 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_27 :
    recurrence4Scalar1First.coeff 27 =
      -((380759931322769073506716772799837645351611894 * 10 ^ 70 +
        9903684559221094601472307572175434102056956263078299730145445540615256) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (27 - x)) = _
  rw [show 28 = 1 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_27_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_28_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (28 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (28 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_28 :
    recurrence4Scalar1First.coeff 28 =
      ((139627377733442140055518080487177164640351996229 * 10 ^ 70 +
        9824391009255331385274501117512715137748807087214892056214907027336833) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (28 - x)) = _
  rw [show 29 = 1 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_28_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_29_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (29 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (29 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_29 :
    recurrence4Scalar1First.coeff 29 =
      -((39978470924065643159788147417204321639671645649885 * 10 ^ 70 +
        6060785012050057452236029518852100774920074968876466888980566831831228) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (29 - x)) = _
  rw [show 30 = 1 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_29_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_30_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (30 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (30 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_30 :
    recurrence4Scalar1First.coeff 30 =
      ((9256498927054789728253207085285046450191331942059768 * 10 ^ 70 +
        9735171751416986732254298286499663374523574209517856727007883079045492) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (30 - x)) = _
  rw [show 31 = 1 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_30_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_31_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (31 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (31 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_31 :
    recurrence4Scalar1First.coeff 31 =
      -((1776797298843391320071269212361220577628006248376043057 * 10 ^ 70 +
        9371767638628893951162275816099467007288780382373438652199851888494166) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (31 - x)) = _
  rw [show 32 = 1 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_31_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_32_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (32 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (32 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_32 :
    recurrence4Scalar1First.coeff 32 =
      ((283588104105129461584239237915212938158729572616447337138 * 10 ^ 70 +
        0578204505524571956201002469562474858841529542361337497422346010856972) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (32 - x)) = _
  rw [show 33 = 1 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_32_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_33_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (33 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (33 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_33 :
    recurrence4Scalar1First.coeff 33 =
      -((36563129477597504979308197256453649768229099512925330395603 * 10 ^ 70 +
        3445184381066090714883591663668421677015026972139855376053865817547689) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (33 - x)) = _
  rw [show 34 = 1 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_33_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_34_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (34 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (34 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_34 :
    recurrence4Scalar1First.coeff 34 =
      ((3393882822862044158084888531429122557165448440002545621621947 * 10 ^ 70 +
        4621643938903998598016817786146381434595232544299949501827418686825264) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (34 - x)) = _
  rw [show 35 = 1 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_34_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_35_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (35 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (35 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_35 :
    recurrence4Scalar1First.coeff 35 =
      -((96531038551013832337936885725066696653787653431617769038871537 * 10 ^ 70 +
        1055759586254850502154494723419476593694836191439916836525894675602317) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (35 - x)) = _
  rw [show 36 = 1 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_35_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_36_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (36 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (36 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_36 :
    recurrence4Scalar1First.coeff 36 =
      -((44921612191205236074785122347627333162078288520165368837895593044 * 10 ^ 70 +
        6875190665343400302193142303407100514595700223539742500324174392655905) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (36 - x)) = _
  rw [show 37 = 1 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_36_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_37_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (37 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (37 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_37 :
    recurrence4Scalar1First.coeff 37 =
      ((12978218690712376958243994931405388990713525129009997646997322678016 * 10 ^ 70 +
        2784020825953993047052299435959681756690789856129317366861523734589873) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (37 - x)) = _
  rw [show 38 = 1 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_37_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_38_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (38 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (38 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_38 :
    recurrence4Scalar1First.coeff 38 =
      -((2313821426928161184079895165510769951549585776745582846237475403346386 * 10 ^ 70 +
        1975132711406834225283144894100151376739705165973214716565547164049215) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (38 - x)) = _
  rw [show 39 = 1 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_38_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_39_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (39 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (39 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_39 :
    recurrence4Scalar1First.coeff 39 =
      (((32 * 10 ^ 70 +
        3154083162212312378743651880180144864105519392415955283924982140941044) * 10 ^ 70 +
        2191846507825750381202769345252697431981276365779174782763175695149281) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (39 - x)) = _
  rw [show 40 = 1 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_39_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_40_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (40 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (40 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_40 :
    recurrence4Scalar1First.coeff 40 =
      -(((3731 * 10 ^ 70 +
        9189787995306366058346841370063922005990945651330034788587791583030146) * 10 ^ 70 +
        0832436736076175184838346656764681230339301750814148235581619786867747) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (40 - x)) = _
  rw [show 41 = 1 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_40_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_41_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (41 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (41 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_41 :
    recurrence4Scalar1First.coeff 41 =
      (((356663 * 10 ^ 70 +
        2260483735476973677205405529007650817663506157074346616211499831153738) * 10 ^ 70 +
        7624120897073303043248562335944416527691486784529420992805633259639163) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (41 - x)) = _
  rw [show 42 = 1 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_41_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_42_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (42 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (42 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_42 :
    recurrence4Scalar1First.coeff 42 =
      -(((26708646 * 10 ^ 70 +
        1086968061873001995224178025163072419814850209314357564168687144913385) * 10 ^ 70 +
        5391781045053867942542225337136488885538657672826688451341969374035833) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (42 - x)) = _
  rw [show 43 = 1 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_42_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_43_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (43 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (43 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_43 :
    recurrence4Scalar1First.coeff 43 =
      (((1204924481 * 10 ^ 70 +
        0305548294369999339443823625601415132090183827672410965276332801451647) * 10 ^ 70 +
        5790350657807317003422162156243367463448188383912027420984376006129816) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (43 - x)) = _
  rw [show 44 = 1 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_43_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_44_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (44 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (44 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_44 :
    recurrence4Scalar1First.coeff 44 =
      (((49909625388 * 10 ^ 70 +
        3799573598782121146432047298319326536051504737352400023968994729540953) * 10 ^ 70 +
        1423197148762288516435533648129831071805816944529437363394118291286180) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (44 - x)) = _
  rw [show 45 = 1 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_44_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_45_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (45 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (45 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_45 :
    recurrence4Scalar1First.coeff 45 =
      -(((20588932483548 * 10 ^ 70 +
        1853308524052892953863798550589143191698831931513235710293177411688967) * 10 ^ 70 +
        1061891013551821084134311156551470686426039448544277662436181356221986) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (45 - x)) = _
  rw [show 46 = 1 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_45_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_46_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (46 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (46 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_46 :
    recurrence4Scalar1First.coeff 46 =
      (((3172112892382242 * 10 ^ 70 +
        7343993203384050189635113397663276728568196811771076394144515688655306) * 10 ^ 70 +
        7999495565033059612986965280503456511391531897348007682360195567509907) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (46 - x)) = _
  rw [show 47 = 1 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_46_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_47_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (47 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (47 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_47 :
    recurrence4Scalar1First.coeff 47 =
      -(((369834223728667023 * 10 ^ 70 +
        8775766011742240086152563742286334642487576379872860320720442866835627) * 10 ^ 70 +
        1761832294818280888183988160340107417277052360503656188216270827058362) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (47 - x)) = _
  rw [show 48 = 1 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_47_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_48_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (48 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (48 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_48 :
    recurrence4Scalar1First.coeff 48 =
      (((36680935416985922145 * 10 ^ 70 +
        6510690872046055282659704279882971826077428650094457620801454926196171) * 10 ^ 70 +
        5398699618039725847768877021599273215820533267310059635700014252392359) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (48 - x)) = _
  rw [show 49 = 1 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_48_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_49_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (49 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (49 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_49 :
    recurrence4Scalar1First.coeff 49 =
      -(((3231809418021637281009 * 10 ^ 70 +
        0619340699783661693318298608193429781728799434811047134154570146502189) * 10 ^ 70 +
        6789697528241911910660117611012042070009445578831857244571133679225577) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (49 - x)) = _
  rw [show 50 = 1 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_49_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_50_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (50 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (50 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_50 :
    recurrence4Scalar1First.coeff 50 =
      (((258421781475828468777311 * 10 ^ 70 +
        5569453907538964153169983550869058830440569426198032495428626862084350) * 10 ^ 70 +
        0926860138134331219018650197049724866310942049761418246713289240004048) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (50 - x)) = _
  rw [show 51 = 1 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_50_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (51 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_51 :
    recurrence4Scalar1First.coeff 51 =
      -(((18989908323419432140985753 * 10 ^ 70 +
        4204703094139043737495161032447179122859190946268079548621064542130104) * 10 ^ 70 +
        3617033803550526575243104207583138383760963565994808468623088628180309) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (51 - x)) = _
  rw [show 52 = 1 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_51_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (52 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_52 :
    recurrence4Scalar1First.coeff 52 =
      (((1292882527048244485569181565 * 10 ^ 70 +
        5942591536279853443815513600728542685590242299893261730838561900153208) * 10 ^ 70 +
        2751473030152928900735733798580044171079225888403260487493221417448689) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (52 - x)) = _
  rw [show 53 = 1 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_52_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
