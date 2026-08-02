/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (53 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_53 :
    recurrence4Scalar1First.coeff 53 =
      -(((82019141965530252337079200218 * 10 ^ 70 +
        5753444227494031017111681302380043194229702198460006282250709148283791) * 10 ^ 70 +
        4345830362753023998651626828719651596329213114302698972352572287396025) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (53 - x)) = _
  rw [show 54 = 1 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_53_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (54 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_54 :
    recurrence4Scalar1First.coeff 54 =
      (((4868870066082564554392103579642 * 10 ^ 70 +
        9162161440338152094522344051744403453564966713881245863012481367406602) * 10 ^ 70 +
        1292055748265672132565891662679388473534564399393298928039508536464211) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (54 - x)) = _
  rw [show 55 = 1 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_54_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (55 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_55 :
    recurrence4Scalar1First.coeff 55 =
      -(((271341950433496254794130346203458 * 10 ^ 70 +
        5677688511974497476455181941978192113164453158197463040030938165120678) * 10 ^ 70 +
        4576783361835287118906803381207365453799220716670483399985456410980810) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (55 - x)) = _
  rw [show 56 = 1 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_55_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (56 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_56 :
    recurrence4Scalar1First.coeff 56 =
      (((14233488044171350023814728976878643 * 10 ^ 70 +
        3932491679962014964975610296938004135354273374106320527002001787959091) * 10 ^ 70 +
        7342964032881466353550401566903551136852204011190788703785934980651134) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (56 - x)) = _
  rw [show 57 = 1 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_56_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (57 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_57 :
    recurrence4Scalar1First.coeff 57 =
      -(((704255848120719549708245280547943750 * 10 ^ 70 +
        7041031012077407673946760159672095561417091411243372351959552646954346) * 10 ^ 70 +
        0561966629959602075202792687438719504231902495973900673532174785414870) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (57 - x)) = _
  rw [show 58 = 1 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_57_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (58 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_58 :
    recurrence4Scalar1First.coeff 58 =
      (((32925479330612476101073421170774030236 * 10 ^ 70 +
        5020967402673335194498762621305257769385738833296139759214987498276272) * 10 ^ 70 +
        1638627658550976516439560709959422008560780550528331549141293320714491) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (58 - x)) = _
  rw [show 59 = 1 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_58_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (59 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_59 :
    recurrence4Scalar1First.coeff 59 =
      -(((1456614432830485358782441899432279337348 * 10 ^ 70 +
        3360809267704365334310411509295666726751420288586656221164571676271613) * 10 ^ 70 +
        1324994388864495467707623327556524338843319216216951238927318390519633) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (59 - x)) = _
  rw [show 60 = 1 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_59_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (60 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_60 :
    recurrence4Scalar1First.coeff 60 =
      (((61050205869046819859047887849406315164484 * 10 ^ 70 +
        7498812713158769739848621018882042185919530568397569119895511155808567) * 10 ^ 70 +
        9162159225106763301219944124326301964303317874827823320086405891196568) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (60 - x)) = _
  rw [show 61 = 1 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_60_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (61 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_61 :
    recurrence4Scalar1First.coeff 61 =
      -(((2426508688202274818026059573091301398600015 * 10 ^ 70 +
        1567242512764432790059256273438705530395574046080082139981915732019362) * 10 ^ 70 +
        5828631463177495873237636268902304415704000645425119405386366197952914) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (61 - x)) = _
  rw [show 62 = 1 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_61_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (62 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_62 :
    recurrence4Scalar1First.coeff 62 =
      (((91529237251496654126943374124820992132874857 * 10 ^ 70 +
        7010171532639625675554798975693588753244107531248267680923282001996705) * 10 ^ 70 +
        5233585213593121590103369321155191497616084501934964384552760114729032) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (62 - x)) = _
  rw [show 63 = 1 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_62_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (63 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_63 :
    recurrence4Scalar1First.coeff 63 =
      -(((3278396551477928720836907218867715763287572991 * 10 ^ 70 +
        0776794920319790851997196007216484515816833509624712601950099980011254) * 10 ^ 70 +
        7168474721853157871497246434786423452163613752547826917189555383732967) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (63 - x)) = _
  rw [show 64 = 1 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_63_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (64 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_64 :
    recurrence4Scalar1First.coeff 64 =
      (((111540154170718967800665690541947778793160038702 * 10 ^ 70 +
        1917426567976168371465865699205880143720368609085535788920064000034720) * 10 ^ 70 +
        3565605183055618338254680279540389317037520586436416509349891898568230) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (64 - x)) = _
  rw [show 65 = 1 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_64_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (65 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_65 :
    recurrence4Scalar1First.coeff 65 =
      -(((3605005618467234877644250807567220978294089312871 * 10 ^ 70 +
        6499543053694892530625056107797581313051444221779099038869207535643767) * 10 ^ 70 +
        9411003363972129171559485300193940734620679687785277569171095402358920) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (65 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_65_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (66 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_66 :
    recurrence4Scalar1First.coeff 66 =
      (((110660967987557837438809334228734541660778285570615 * 10 ^ 70 +
        1158275652533295817210687479942692983728368778494389725034979414048137) * 10 ^ 70 +
        6694017654068481931908374708845725193240103971017801509103118799658689) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (66 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_66_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (67 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_67 :
    recurrence4Scalar1First.coeff 67 =
      -(((3224369931398306705944713985408918363329849009894133 * 10 ^ 70 +
        9072017318429225628044319047621431709602835434869696883150642630385876) * 10 ^ 70 +
        7472684654821779743730829314966792857516515188288200104270009075890040) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (67 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_67_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (68 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_68 :
    recurrence4Scalar1First.coeff 68 =
      (((89082429182050306748296524541788698739119817480271722 * 10 ^ 70 +
        3307339534139813578038728301596602568606875055617968220417462858360816) * 10 ^ 70 +
        1362486343890168293995595018417163893378386989053437553145421727289666) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (68 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_68_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (69 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_69 :
    recurrence4Scalar1First.coeff 69 =
      -(((2329554432896641711060551989601623916776396898381091680 * 10 ^ 70 +
        5310673359770287722920422588873487796073550080318954460608068363194077) * 10 ^ 70 +
        3577870352162845989141093169054947486143296026069804235923212389530593) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (69 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_69_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (70 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_70 :
    recurrence4Scalar1First.coeff 70 =
      (((57502024660798516002129440787141311519269309587797442773 * 10 ^ 70 +
        6141717202966483294358794273201621857200051759213076951248690814210294) * 10 ^ 70 +
        6474073891880680052786469205531353779185200436377813834263620257900561) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (70 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_70_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (71 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_71 :
    recurrence4Scalar1First.coeff 71 =
      -(((1333901674616572059670629319725539649087891714650949473739 * 10 ^ 70 +
        5346737852704682770818553862186970983202974675433980433111222866569817) * 10 ^ 70 +
        9135166525292526378639756575388068864138835677809853741389437230517452) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (71 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_71_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (72 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_72 :
    recurrence4Scalar1First.coeff 72 =
      (((28874536473770671042695480000878099721495943971220184944511 * 10 ^ 70 +
        4808094647679856865025953055208342376733584733032756952923793038264065) * 10 ^ 70 +
        6656721380978574271669002686750898443543718736167497275915914107367072) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (72 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_72_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (73 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_73 :
    recurrence4Scalar1First.coeff 73 =
      -(((576190874957171326273903367649222229966767901582971153884594 * 10 ^ 70 +
        1264598887673668146952055306070965636678625399276696708604748991155116) * 10 ^ 70 +
        6624024758941406032702610091251236238655616910009208190089133993213620) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (73 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_73_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (74 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_74 :
    recurrence4Scalar1First.coeff 74 =
      (((10357508882927470977247841124849604465279752497587798823475242 * 10 ^ 70 +
        2027384729122622932011388181803780708583422222086625246961522957994262) * 10 ^ 70 +
        8338564773227293637514548613308997240897696681432812926232149829024672) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (74 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_74_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (75 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_75 :
    recurrence4Scalar1First.coeff 75 =
      -(((159257960827717462658343525173839207081539728885448297279818507 * 10 ^ 70 +
        5043183306405330621841796762738884804007117288309801772935610531078741) * 10 ^ 70 +
        9917818009450464337115503999975545362916123141783800371086789056245809) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (75 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_75_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (76 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_76 :
    recurrence4Scalar1First.coeff 76 =
      (((1779915042477942228792857699116574637963372292785382448093133524 * 10 ^ 70 +
        4114845108751269126923818150459752161650965242113448630098592565397752) * 10 ^ 70 +
        4160696949493216977818047648150669600923219725994855939459016238772539) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (76 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_76_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (77 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_77 :
    recurrence4Scalar1First.coeff 77 =
      -(((1091717266450193088764746347576566771089642439066674177780406435 * 10 ^ 70 +
        1602780169457588579296295384595879337459495102612372614536954519732544) * 10 ^ 70 +
        2458627630091074421607088842817290330506570339831691104803604651448513) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (77 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_77_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (78 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_78 :
    recurrence4Scalar1First.coeff 78 =
      -(((718097993411383408076529138587034401309812312588817136766696019005 * 10 ^ 70 +
        0745953497047374325523586909831265527004071996870832342536024995772246) * 10 ^ 70 +
        8048845968142624047390151179130675377378635826781815573012300978112326) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (78 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_78_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (79 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_79 :
    recurrence4Scalar1First.coeff 79 =
      (((28307662131817233077434265928159122809816591364332028157327625903350 * 10 ^ 70 +
        3613099142754596630845867003416674419717912365311073062829319147805257) * 10 ^ 70 +
        2936905001160446505121834241890485787530812507695613552908788926534821) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (79 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_79_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (80 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_80 :
    recurrence4Scalar1First.coeff 80 =
      -(((792244276221691704011136233598895152142202015337608286032042984192610 * 10 ^ 70 +
        8264793282424978065635393458867923300575975526558879754019575650415434) * 10 ^ 70 +
        4741121721653767709769643323138385503289183356605141711923771609694727) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (80 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_80_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (81 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_81 :
    recurrence4Scalar1First.coeff 81 =
      ((((1 * 10 ^ 70 +
        8756485919943475432923783454651594021004946319654329759405825169376928) * 10 ^ 70 +
        4204044520621267592099833555738226093908482866685123352904985736281406) * 10 ^ 70 +
        9646531324106638837896943682840559193910673008671013425916347189850337) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (81 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_81_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (82 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_82 :
    recurrence4Scalar1First.coeff 82 =
      -((((39 * 10 ^ 70 +
        5348761784272809510934614836343154065521074234327588538668103550793670) * 10 ^ 70 +
        9920228337091365632280302235839291631519102084206237691298876614221559) * 10 ^ 70 +
        4163118910592510025777158501591042405651739076090301235012818574917899) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (82 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_82_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (83 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_83 :
    recurrence4Scalar1First.coeff 83 =
      ((((755 * 10 ^ 70 +
        7053976512561438402727051841832177039518220531238694683344348618801121) * 10 ^ 70 +
        0417862515513639828437941825100236233138787087541666943003332568409442) * 10 ^ 70 +
        6029957507697886001897642093467837245907402751845163907687852232758367) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (83 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_83_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (84 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_84 :
    recurrence4Scalar1First.coeff 84 =
      -((((13141 * 10 ^ 70 +
        8883040949561792561410122192321304144373770572914867085884655850283803) * 10 ^ 70 +
        3935341962535493194201831989720370824704561510969759092272522233047448) * 10 ^ 70 +
        8017486660673226427570654005530084027749822723662559749014440314944283) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (84 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_84_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (85 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_85 :
    recurrence4Scalar1First.coeff 85 =
      ((((205867 * 10 ^ 70 +
        3912425966333428342699637827579647137710311843233849616495055394770681) * 10 ^ 70 +
        6571951093039971073196544073629724162022492401545168166485045691745709) * 10 ^ 70 +
        6424824545145421518951115839182930437069178919921251530350254305954234) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (85 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (86 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_86 :
    recurrence4Scalar1First.coeff 86 =
      -((((2814108 * 10 ^ 70 +
        0666252309643372228020190314238471821050964992253935112155419894561197) * 10 ^ 70 +
        6256166508018472087915931190926983392434212655076820797820338924157084) * 10 ^ 70 +
        2504163396426857350551693669690835385721047163382482640133985088659350) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (86 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (87 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_87 :
    recurrence4Scalar1First.coeff 87 =
      ((((30516902 * 10 ^ 70 +
        8479523951159509493073493537953267186007059674501269796072098156404275) * 10 ^ 70 +
        8922961987602531449906608629075328629564718372794068332765247729356928) * 10 ^ 70 +
        0598861953270171572707514432100364819579837429777386165318651759964713) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (87 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (88 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_88 :
    recurrence4Scalar1First.coeff 88 =
      -((((158013209 * 10 ^ 70 +
        4834636415599654238798368367798037141361446622147746329033645866454328) * 10 ^ 70 +
        2567495165262071374689864121033280564286810243010203127719886041588494) * 10 ^ 70 +
        4760143333400843929456734496227657514784715761329454554038135559504690) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (88 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (89 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_89 :
    recurrence4Scalar1First.coeff 89 =
      -((((3905340792 * 10 ^ 70 +
        1107451539323184468152618376264330130039481816954779028066534971394253) * 10 ^ 70 +
        5982769410388421724623054064250432472295497363567762431756884953708905) * 10 ^ 70 +
        7349123246730419117141176786184305789190011101015182519210980090757177) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (89 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (90 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_90 :
    recurrence4Scalar1First.coeff 90 =
      ((((174173574157 * 10 ^ 70 +
        7340211047549187189004366108599300666756665780580072747624381524303056) * 10 ^ 70 +
        5834504675295748168244927221587658904116509594470943695902493407791817) * 10 ^ 70 +
        3628372507257366154678270276877857789194367078136028059562227849723120) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (90 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (91 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_91 :
    recurrence4Scalar1First.coeff 91 =
      -((((4537350519159 * 10 ^ 70 +
        6507789569261842268531577390959851146454821528913465365659063259272297) * 10 ^ 70 +
        7248503848920863063619762528067331823769310379869790019296612855440794) * 10 ^ 70 +
        3165577597992377841148885275704131385081815447270249106883970151918168) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (91 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (92 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_92 :
    recurrence4Scalar1First.coeff 92 =
      ((((97296829658765 * 10 ^ 70 +
        6389598356142480048509029672242416762466748558472745443682686441095928) * 10 ^ 70 +
        3457546374661647548175556118810275809822264207625827206930552227516035) * 10 ^ 70 +
        0689837908975757826342084101668593401566733028613988310834339477996064) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (92 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (93 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_93 :
    recurrence4Scalar1First.coeff 93 =
      -((((1863537184086566 * 10 ^ 70 +
        2839666133780505989661094269695182505469786204946860584205683074103194) * 10 ^ 70 +
        5400801058200702284100993265003561739991802078902483185764260672758120) * 10 ^ 70 +
        1124366373936120581370192551141735061017537038514292505642647174450073) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (93 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (94 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_94 :
    recurrence4Scalar1First.coeff 94 =
      ((((32950586362758966 * 10 ^ 70 +
        4946670358841852839500793586448888311105472392676456343535852508004319) * 10 ^ 70 +
        2890233176193247856178590074518922912029528962239036345151318689215133) * 10 ^ 70 +
        5293918115739390608937367914577743199941072588074512486497667108662829) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (94 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (95 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_95 :
    recurrence4Scalar1First.coeff 95 =
      -((((547028759822439168 * 10 ^ 70 +
        8431470849708890984391214131027939541063891974046216249351292407564531) * 10 ^ 70 +
        3508889013039188984172449663509002516224039053260149296453688919083944) * 10 ^ 70 +
        0016051116159033015648965197315468591174342494600117008780848234956711) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (95 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (96 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_96 :
    recurrence4Scalar1First.coeff 96 =
      ((((8611823282704705050 * 10 ^ 70 +
        1869499277446785642165410405942539370959356494421118714678131643652534) * 10 ^ 70 +
        9499754229203941109810571003001490354313413985000764004239179803453118) * 10 ^ 70 +
        2718130002077592607980158210788138172671807911813274288256618994268629) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (96 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (97 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_97 :
    recurrence4Scalar1First.coeff 97 =
      -((((129392609310479171255 * 10 ^ 70 +
        5397891265511915293218200672376495475581431235959383523580902625903332) * 10 ^ 70 +
        1084328841548516342918549791064357767747418659332969479277536182131522) * 10 ^ 70 +
        3312260529996916898195707416175557544536219036200809355056910966614480) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (97 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (98 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_98 :
    recurrence4Scalar1First.coeff 98 =
      ((((1863750949562697238326 * 10 ^ 70 +
        9747946708394149619297007467656441252156373517013749352762782922709870) * 10 ^ 70 +
        5902414752728270576256174036001109242028098295229599297300503011924818) * 10 ^ 70 +
        7809998613803063478836194445083635722024117796793826896425507191626350) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (98 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (99 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_99 :
    recurrence4Scalar1First.coeff 99 =
      -((((25819274771531981660998 * 10 ^ 70 +
        5917577828013675450950733545342609951309378896453798145414294975140105) * 10 ^ 70 +
        1870010111710032578482085480158938246116384370410470609547354672996298) * 10 ^ 70 +
        1444786738847538675338876256286880963892657205577614287090928563146216) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (99 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (100 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_100 :
    recurrence4Scalar1First.coeff 100 =
      ((((344869907367034617635578 * 10 ^ 70 +
        0794008286255646590837432012008624275682360657444202551996750961551310) * 10 ^ 70 +
        5878378917576422300375574886438566326898637061287265268502166229878281) * 10 ^ 70 +
        6001147161366260064947118649554541356349504917124788946893426345548540) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (100 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (101 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_101 :
    recurrence4Scalar1First.coeff 101 =
      -((((4450114320154813275349324 * 10 ^ 70 +
        0195669553807137564629899664354405261609474980131023428012283476309517) * 10 ^ 70 +
        4874070745918843363824091664276375937586093829560843256418003592564892) * 10 ^ 70 +
        8156535801311350594009935570615894878381560384274807219833222784541812) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (101 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (102 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_102 :
    recurrence4Scalar1First.coeff 102 =
      ((((55562359351580482281880358 * 10 ^ 70 +
        2538014636209657951000381002725515753619902001055571113224286315705805) * 10 ^ 70 +
        2858442022717081708296300584242132706143643781067250601082739293804711) * 10 ^ 70 +
        4509183624576928239657013578072719876108940030513348557983065102860976) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (102 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (103 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_103 :
    recurrence4Scalar1First.coeff 103 =
      -((((672134381912668617900538843 * 10 ^ 70 +
        0877304522789447356766380393278902812176992419505475807635592667919772) * 10 ^ 70 +
        1577562451702101406886794862725478407701704212784187951785979337497399) * 10 ^ 70 +
        3313265495835860426212121850729639435885077361305561431205249024798872) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (103 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (104 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_104 :
    recurrence4Scalar1First.coeff 104 =
      ((((7886465543777286245390717622 * 10 ^ 70 +
        2456002336363050199692812675592266012952144072909754082128850191275009) * 10 ^ 70 +
        2270509039693993167071110772197164972417109449818706313580295235496514) * 10 ^ 70 +
        9299217849829733138053626109090174715741436907484957394238021504843635) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (104 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (105 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_105 :
    recurrence4Scalar1First.coeff 105 =
      -((((89841630451946888951333371658 * 10 ^ 70 +
        4632901658323283634877259100320916471438352338423969207746508952055600) * 10 ^ 70 +
        6233928022217904867290348081736879627914022725323678402585463097686101) * 10 ^ 70 +
        4625503721983433654297629528752907963532313177215244803366476754744013) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (105 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (106 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_106 :
    recurrence4Scalar1First.coeff 106 =
      ((((994506197374288656392520707558 * 10 ^ 70 +
        7816206403701599124118784411233787101160139802020018421660213919896224) * 10 ^ 70 +
        2707374974177589115545809175288750796016840309230944355521512971089649) * 10 ^ 70 +
        8362673410474489539240256877985051256009096257570079153124642377671622) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (106 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (107 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_107 :
    recurrence4Scalar1First.coeff 107 =
      -((((10705232218363285836132549097511 * 10 ^ 70 +
        8625767559104082193605946571655382823042624136657748619278871143012649) * 10 ^ 70 +
        9878258535573054833395458700418793899073926348284794064150228647391229) * 10 ^ 70 +
        4133550346819777209649147129390487651592434685649786211658533222276538) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (107 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (108 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_108 :
    recurrence4Scalar1First.coeff 108 =
      ((((112133085308131377798562473227151 * 10 ^ 70 +
        3202989519828741253340526893194970062009114733615819958082813413592054) * 10 ^ 70 +
        9473991767699910839592006985168736523316437140041243921453484488315071) * 10 ^ 70 +
        4043116353868747911590962734285492139361964917538430414383275370750839) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (108 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (109 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_109 :
    recurrence4Scalar1First.coeff 109 =
      -((((1143623794498633207427570047928014 * 10 ^ 70 +
        3367412819250727513578298835033260609314611178203536968346734262830215) * 10 ^ 70 +
        8353905257789950456386770773076644892229890356097849862767415150014236) * 10 ^ 70 +
        9944519637419500825932263089306876112839351160845931756826193220748244) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (109 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (110 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_110 :
    recurrence4Scalar1First.coeff 110 =
      ((((11362762349448780000661267038844991 * 10 ^ 70 +
        4792842592110432622476892760244347528935561940016727163975991217478591) * 10 ^ 70 +
        5157735328563493097030971764405309002473111119412255242581635874728616) * 10 ^ 70 +
        6493916021165774606009556112981040823100514012095990756162382598353445) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (110 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (111 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_111 :
    recurrence4Scalar1First.coeff 111 =
      -((((110041417431940752062548289781863081 * 10 ^ 70 +
        4376000872706055480594082439054610886935238489441791069722199777796866) * 10 ^ 70 +
        5343598599847382854445237329861073952564498350724393389933142327534977) * 10 ^ 70 +
        4055736621520895260207776871949691592949879553460630481654028767985504) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (111 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (112 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_112 :
    recurrence4Scalar1First.coeff 112 =
      ((((1039210649645158129342724207349436539 * 10 ^ 70 +
        0675327868202785716494982007433380980451961409183442015315332590512932) * 10 ^ 70 +
        8410666444730780784417850403763074289503083395362251101487444642996238) * 10 ^ 70 +
        1626090808410985954525747049790809848235587120806469157941142155708212) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (112 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (113 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_113 :
    recurrence4Scalar1First.coeff 113 =
      -((((9574488718705527583313003381759024036 * 10 ^ 70 +
        1772958540739158462755651300559094633886838413075368224598504786646622) * 10 ^ 70 +
        1497011261300464983482117231622744639645836953241979654910474651493168) * 10 ^ 70 +
        2396489504339665486511867998104218436295055093619296511986658626545990) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (113 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (114 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_114 :
    recurrence4Scalar1First.coeff 114 =
      ((((86093283663389167705052223604753506184 * 10 ^ 70 +
        8180885802184394612034695813511938174858377792235030297057198167769520) * 10 ^ 70 +
        4518379302800767477064797494496855205833547550523031149640535973567839) * 10 ^ 70 +
        6997042187857693164593384707393299683341731609257640608580616273980491) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (114 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (115 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_115 :
    recurrence4Scalar1First.coeff 115 =
      -((((755841812347524707791789486722902811970 * 10 ^ 70 +
        2313932438509953532844888391372960877874710293175429849784863740809772) * 10 ^ 70 +
        0915353159351981642811527577001579500794480670548975856859704317686149) * 10 ^ 70 +
        4914495223397829897298181578209773152483308189376005639138422448451909) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (115 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (116 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_116 :
    recurrence4Scalar1First.coeff 116 =
      ((((6481227434593589119034719502682847909510 * 10 ^ 70 +
        4190647407638107449324980367684880443377461679285607425429804477330933) * 10 ^ 70 +
        0259652434009283856510273918342020348525241521362293656855557488618958) * 10 ^ 70 +
        2979480794080300456935905366160820853248844432424332572138158778741604) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (116 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (117 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_117 :
    recurrence4Scalar1First.coeff 117 =
      -((((54299595374493603404768267819279033465989 * 10 ^ 70 +
        3230496376719790082153287443354291932313758855379417561708032391945486) * 10 ^ 70 +
        8531464538595565136065800200267074662098517908961256295887692327128733) * 10 ^ 70 +
        0377011971778623409064642096054011535832646149811985968071677496380558) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (117 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (118 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_118 :
    recurrence4Scalar1First.coeff 118 =
      ((((444620620084843664776221108172005724405082 * 10 ^ 70 +
        8891454405036674598346279745783508469083894974768476001067936062251653) * 10 ^ 70 +
        7832113437750631484078318759002347654835773919168879769250164872848843) * 10 ^ 70 +
        0154147844976888223327024133017614215254460747077888212816998854685836) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (118 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (119 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_119 :
    recurrence4Scalar1First.coeff 119 =
      -((((3559345492510574305286155949738986283724689 * 10 ^ 70 +
        9785494557175688727278993183876967963344696183494558916196708934712648) * 10 ^ 70 +
        1163761808941880101073586215435746770088080629025020526059991948036457) * 10 ^ 70 +
        4082066528598026375730309504365925879036753566350026614731215740385847) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (119 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (120 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_120 :
    recurrence4Scalar1First.coeff 120 =
      ((((27865440205704561106671880266331660639554772 * 10 ^ 70 +
        3370511549709318033879969437674430247075440119027214779172696340675301) * 10 ^ 70 +
        8538493560286128522263932192332117504351507795193925774101386184303700) * 10 ^ 70 +
        6540199861227365696349849809594480748733562300841438849519104075365286) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (120 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (121 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_121 :
    recurrence4Scalar1First.coeff 121 =
      -((((213402220541188117021738720135525701376873725 * 10 ^ 70 +
        3195002614652583217529796957152862825341957819925995159147940993581465) * 10 ^ 70 +
        9754067148978080052320022623599994773302676758662991679665391065920397) * 10 ^ 70 +
        7909592110648289365572465099386808273197753284917671703868291957370010) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (121 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (122 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_122 :
    recurrence4Scalar1First.coeff 122 =
      ((((1599138621320932665533618517659131533598494749 * 10 ^ 70 +
        6276688145478707450576452086793565157400462475715390701402257346158440) * 10 ^ 70 +
        6921519567692069082208509110279211037215290325221969024481233369427278) * 10 ^ 70 +
        3423562218076665826054109831297944864614337820009383766261963752961575) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (122 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (123 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_123 :
    recurrence4Scalar1First.coeff 123 =
      -((((11728422131036760979055434019656060727493132337 * 10 ^ 70 +
        0470482778370215623755898193819705412405547660447826332533773833588494) * 10 ^ 70 +
        3577929683691389020639754272791636446899086803605102959409259802621883) * 10 ^ 70 +
        8283396622928748186713530478663327909930426768976907568544028058063915) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (123 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (124 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_124 :
    recurrence4Scalar1First.coeff 124 =
      ((((84210671164746861265692740138135081968916477335 * 10 ^ 70 +
        2038565427723129686147254829558356990051920622350411158009119599806344) * 10 ^ 70 +
        2704253658127996664923560705002250786786275042087866997190005101967209) * 10 ^ 70 +
        9049763819429630316188662541471719419388167743219832899208870904589209) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (124 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (125 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_125 :
    recurrence4Scalar1First.coeff 125 =
      -((((592069149871077944726042632882237271680532215611 * 10 ^ 70 +
        5697571668130487289124798704004279377765866039811229677356417735088668) * 10 ^ 70 +
        6624257869832752439393002219426321899172575745321120870312603898032679) * 10 ^ 70 +
        7325733928855340777780862866801782317841002213222847096216657453796735) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (125 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (126 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_126 :
    recurrence4Scalar1First.coeff 126 =
      ((((4077138039877318614774858929442855274114289010636 * 10 ^ 70 +
        9718672019072308557317509350229596194323265004046584895073211883669071) * 10 ^ 70 +
        8906846516690705970076365052177092677752493778499722308551753430085110) * 10 ^ 70 +
        9676536369136901693238776336583707195978410903749102007315675204216506) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (126 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (127 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_127 :
    recurrence4Scalar1First.coeff 127 =
      -((((27505051128543725880570684193317394368527297314575 * 10 ^ 70 +
        7010588356332171293268131107097890348586999730659431598969974914430492) * 10 ^ 70 +
        2130206575819946838446021090654780816686097411062302719401433458584568) * 10 ^ 70 +
        0722008889885019228153669022391828554406003504039330097823385944597382) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (127 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (128 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_128 :
    recurrence4Scalar1First.coeff 128 =
      ((((181817891527707098846432927691679648742411161127561 * 10 ^ 70 +
        0029818053124029450692731603179398356827722166665610541112978881760194) * 10 ^ 70 +
        2139722958714758538170551189437974402861624600937779973028449112622041) * 10 ^ 70 +
        8511961783480584082066244781556191138022185463367688450476713542552153) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (128 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (129 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_129 :
    recurrence4Scalar1First.coeff 129 =
      -((((1177925542687752629402567305462750200947795891047821 * 10 ^ 70 +
        1550680416783910814452048135909343571423744451712222404712517176715697) * 10 ^ 70 +
        6367483892531759165016255622720108975358372338928388052301641180812010) * 10 ^ 70 +
        7055250316185455831326001214005585974284275273621352130796666688467012) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (129 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (130 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_130 :
    recurrence4Scalar1First.coeff 130 =
      ((((7480715227982912333719891211069455695838505808963028 * 10 ^ 70 +
        9163878707298754905672243553952187119293033074093084028702086529155996) * 10 ^ 70 +
        2920425523276744790772567705595064612781484976303936027831875647351060) * 10 ^ 70 +
        2249201593555804363365951338966943896782642929609103862748307959232454) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (130 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (131 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_131 :
    recurrence4Scalar1First.coeff 131 =
      -((((46579699521249231083764034393895772957866822295494769 * 10 ^ 70 +
        6509125954134831907212605642652025904713790486741891535779820667333563) * 10 ^ 70 +
        4073819818130922616688527742222992741781148732648648123299995553794215) * 10 ^ 70 +
        7527987310568998061508299575575319285949389185071472437031433513516242) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (131 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (132 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_132 :
    recurrence4Scalar1First.coeff 132 =
      ((((284419976367939857043706345313491960229599930684122044 * 10 ^ 70 +
        0751894841951167893560682077874698988400576464749874688706436638426257) * 10 ^ 70 +
        8389959985342835655867144978053235442315516382964209748357798627281869) * 10 ^ 70 +
        2275616440559155122826178227221724196749557435359823398362550847874295) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (132 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (133 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_133 :
    recurrence4Scalar1First.coeff 133 =
      -((((1703383477936989462958709295834383069095002002388675762 * 10 ^ 70 +
        4929341397790767443629927551123715716187507602226353516083920759756228) * 10 ^ 70 +
        6170876363453909977863215906213802524284807090564730332684739338438148) * 10 ^ 70 +
        1911929158115984378746262509942981048639020474621594686297597903770815) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (133 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (134 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_134 :
    recurrence4Scalar1First.coeff 134 =
      ((((10007609814354419190568853620788779728902495442073110801 * 10 ^ 70 +
        4899511491715272833159046193543833898987372562409231746474545371022627) * 10 ^ 70 +
        4700753356086079180068952633024543761474862251474027064462942108476553) * 10 ^ 70 +
        8903789905950511096561777405507316168987231858261305917949879595978255) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (134 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (135 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_135 :
    recurrence4Scalar1First.coeff 135 =
      -((((57688373631331675802272961329344138188138146323062393168 * 10 ^ 70 +
        2427213202614100786826521684869297056500593045711023215651876350601032) * 10 ^ 70 +
        8736250824155577877579237399418164760780339657639336980819071792411736) * 10 ^ 70 +
        5295300498600935297021682407752596935593989294473790894964626007149803) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (135 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (136 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_136 :
    recurrence4Scalar1First.coeff 136 =
      ((((326331081614476619983418811630711980643716409969637560065 * 10 ^ 70 +
        2957638663164903254818260761944343492408530911067451224235126622692107) * 10 ^ 70 +
        3247295407049621090743268703477359231982380067339999003738962719188380) * 10 ^ 70 +
        2591825587334240664602318295496310172517530028197398320762715592841215) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (136 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (137 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_137 :
    recurrence4Scalar1First.coeff 137 =
      -((((1811802804099962655069747366982639532658928086978106346978 * 10 ^ 70 +
        4755005367071994146614965298205051248225107777539824177695702722759647) * 10 ^ 70 +
        3274076434145088210112208306416733883668438872047456015636748958754914) * 10 ^ 70 +
        2575785435428715224389999522900116354208694840715803221482210533965686) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (137 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (138 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_138 :
    recurrence4Scalar1First.coeff 138 =
      ((((9874471946000233980709942952109336434878424644672089327598 * 10 ^ 70 +
        9253131836639057029471609154019430066229182328434038108913229646205365) * 10 ^ 70 +
        0279285171749563050668526585734511335663914379458680796042943273635344) * 10 ^ 70 +
        7292798746595280611940282488467746810273357439398757669753116904778742) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (138 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (139 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_139 :
    recurrence4Scalar1First.coeff 139 =
      -((((52836433757357793537788085392867175765072269355978637349932 * 10 ^ 70 +
        1323973489620273511374309800632074907152028295516394889262678397928008) * 10 ^ 70 +
        3176436841206711261368024421817085961812603482536743027682255537932511) * 10 ^ 70 +
        2671622814217157356898705029256224665549471992706408445568209946321872) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (139 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (140 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_140 :
    recurrence4Scalar1First.coeff 140 =
      ((((277609370975637940516984627007792492356029634652774648005430 * 10 ^ 70 +
        8303218029754268361781859829399742684687064506944602187258451164337510) * 10 ^ 70 +
        8542990035202191261765068615963955492975904764910490917355865096136721) * 10 ^ 70 +
        5431660246942779463033052987082819083387577059607664255730699895175229) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (140 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (141 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_141 :
    recurrence4Scalar1First.coeff 141 =
      -((((1432446186892163545980920052379456927679613935063600143634138 * 10 ^ 70 +
        6492359074364340641531199732006450905261693228192632099319680891801097) * 10 ^ 70 +
        2647469866980646646340803727013918121546990124289676053413210795262799) * 10 ^ 70 +
        2211218082646058201054587734759237093160240581418007540127722490728093) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (141 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (142 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_142 :
    recurrence4Scalar1First.coeff 142 =
      ((((7259837759778302680043559288763521635577585060824416996163736 * 10 ^ 70 +
        9687372479484295114842605230000159321239602740371870582672147125522860) * 10 ^ 70 +
        2820450664043908468529081604734844312570040969900271433345239754405715) * 10 ^ 70 +
        8790197874602568292972162081105521989042665766028891431351845959786305) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (142 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (143 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_143 :
    recurrence4Scalar1First.coeff 143 =
      -((((36144239877334468848595920293454821188808132049143533107020163 * 10 ^ 70 +
        5015205203537719734976667695508387517917751173720188067403066667871706) * 10 ^ 70 +
        6602265514666462608822415588826889367582380372119189119982362958557638) * 10 ^ 70 +
        1133976293060081628845188060574209521512617463407492533429161698530490) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (143 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (144 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_144 :
    recurrence4Scalar1First.coeff 144 =
      ((((176795995796967319558097450036283058861719131596435137889356686 * 10 ^ 70 +
        8008301066080474389210422937808397664028209705885263754910553292145125) * 10 ^ 70 +
        5059523416206518242503238697510749103656124666746229244267072791984707) * 10 ^ 70 +
        4257128264299692511527936444903607430465597556102465199097981352853238) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (144 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (145 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_145 :
    recurrence4Scalar1First.coeff 145 =
      -((((849733839298766695255422624512645996109006411426551364351227898 * 10 ^ 70 +
        4584932709322077269442922802933050193584649163818412206624184934397230) * 10 ^ 70 +
        3821661168314631393824483827378599700681812909070802237407178262584768) * 10 ^ 70 +
        6208331994334690496482414109055471990546081141997621858076914261300931) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (145 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (146 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_146 :
    recurrence4Scalar1First.coeff 146 =
      ((((4013516653152477121319941197478318760979907591057222145138788025 * 10 ^ 70 +
        2066379588788019656215853053812889786769391718076155201308204682341696) * 10 ^ 70 +
        8645448786827374854538943170583552739212449649823493945378604519635589) * 10 ^ 70 +
        9032285498634739126448848872134624326651218607200413469163625871714192) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (146 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (147 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_147 :
    recurrence4Scalar1First.coeff 147 =
      -((((18631676631160124036951687531340473344828177205321941318045714295 * 10 ^ 70 +
        0083523021328962529740708597788796126612339782255561466201609613858540) * 10 ^ 70 +
        2362746593890759245473662171130431075670643728914571102575887712696866) * 10 ^ 70 +
        6586469262908327754039064841029189378893840850192827331298225023488038) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (147 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (148 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_148 :
    recurrence4Scalar1First.coeff 148 =
      ((((85018835231421096668023663214355540159379215080747709424352796371 * 10 ^ 70 +
        9294150747168670440853409924324259525539878190209045525569032678001926) * 10 ^ 70 +
        8736484880374007365132425108800409128419062978531538490357891745572615) * 10 ^ 70 +
        7072996809694191710029966594200975479923456300332180006417265805058642) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (148 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (149 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_149 :
    recurrence4Scalar1First.coeff 149 =
      -((((381386191267867426044511262734948937255217743589106560279042281310 * 10 ^ 70 +
        8143375200993869627616146014360499414163639290426239236181942100752038) * 10 ^ 70 +
        7218267389117742173147063789565129363777682355093407644892312983125705) * 10 ^ 70 +
        2266089036210426158208968212113416188729349808565046842088159758340558) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (149 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (150 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_150 :
    recurrence4Scalar1First.coeff 150 =
      ((((1682094157639884494037225621442543750660210597397170048629383867274 * 10 ^ 70 +
        8671979419876510281468226484251697014614717323835257896402446049082841) * 10 ^ 70 +
        1260859465230893401112165492334905202673380491890115355232982503877638) * 10 ^ 70 +
        4951044870841440610596008826866288096974368613101423441075331337141933) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (150 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (151 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_151 :
    recurrence4Scalar1First.coeff 151 =
      -((((7294890720916563859303346631688106889110751452099726894328657103107 * 10 ^ 70 +
        8856324311623333698968951318559840948453836111150396284968553730596844) * 10 ^ 70 +
        3109226592266269409062780706277530594152682407173304960755384212657209) * 10 ^ 70 +
        1153069681618151252548756465793354871877463931985213801665069457676850) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (151 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (152 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_152 :
    recurrence4Scalar1First.coeff 152 =
      ((((31111202286538449944955261439643363952579006142318057064633887701533 * 10 ^ 70 +
        2516797038628614828877462887503477159379129721695947540500415280679441) * 10 ^ 70 +
        2125052472155339453424507868297301658371359693170140906753894248093210) * 10 ^ 70 +
        7291703686053322913104133314068305418727835395653402378895853010509904) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (152 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (153 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_153 :
    recurrence4Scalar1First.coeff 153 =
      -((((130493672846739412842273529336190190722315416107084450970504829019371 * 10 ^ 70 +
        1903187464733736977809869613116506807562932039012920310300998366466318) * 10 ^ 70 +
        3103841156520696528675127082762989606558149607489799141181707111762159) * 10 ^ 70 +
        2582921524933124311127004507392933080858906108658992764574676706417822) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (153 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (154 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_154 :
    recurrence4Scalar1First.coeff 154 =
      ((((538369834346519325169379493854918168449798724385623817585710979103087 * 10 ^ 70 +
        6272517397321164771791476104799979848508533770179494508625449178041116) * 10 ^ 70 +
        1825896537665266200428621269302742653047728140250870972793366655940513) * 10 ^ 70 +
        6245308504040193974433331468583476127007819281259498363924824362674731) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (154 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (155 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_155 :
    recurrence4Scalar1First.coeff 155 =
      -((((2184909074503572199809609334314141311413078125761375073201425750410045 * 10 ^ 70 +
        5442997063893502162930186125000049410451834012727779242187601514606412) * 10 ^ 70 +
        4598937011148805022210468383654421192173774769543303667549354221898309) * 10 ^ 70 +
        5057607585275853592186006628311159967979870672879607518487216639224654) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (155 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (156 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_156 :
    recurrence4Scalar1First.coeff 156 =
      ((((8723465758486117495419774032910021072094119248117952572584566488291493 * 10 ^ 70 +
        5355815114459683619836599887509740231091431679012757756129262324182472) * 10 ^ 70 +
        9732727116412660135653100844349646073399029003933467656643406774635526) * 10 ^ 70 +
        6188212001946032194514265278644797053980891373793623147224527317476547) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (156 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (157 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_157 :
    recurrence4Scalar1First.coeff 157 =
      -(((((3 * 10 ^ 70 +
        4267967489432985947352036652879780398100344783709120898747866831360610) * 10 ^ 70 +
        2388625531819034686627146309992612034097519358921963400737158967269196) * 10 ^ 70 +
        8382805989277702316812851987023113884310353068580494556567197600348163) * 10 ^ 70 +
        1264127921663919184575675415646950091657028996341980667325326322841643) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (157 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (158 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_158 :
    recurrence4Scalar1First.coeff 158 =
      (((((13 * 10 ^ 70 +
        2455715290548143982765684675426357714943521550086579731554295763552440) * 10 ^ 70 +
        7751300376570718611327596037401537215205418484538906293057693173402842) * 10 ^ 70 +
        0655305930065700372288482100622968710084231274127926675344795096714734) * 10 ^ 70 +
        5189300104729500877282881045950292492559730894510566302829624710377997) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (158 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (159 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_159 :
    recurrence4Scalar1First.coeff 159 =
      -(((((50 * 10 ^ 70 +
        3819020184388137425672251607412449270496347068009738524854809391920369) * 10 ^ 70 +
        0610853847140297040655971508534072969282329828534607738967683995399556) * 10 ^ 70 +
        8031386133294015807464318142528950034675384577266492102075782429483559) * 10 ^ 70 +
        6054078248814978052950698298011016526743835001002240320528371631898344) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (159 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (160 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_160 :
    recurrence4Scalar1First.coeff 160 =
      (((((188 * 10 ^ 70 +
        5981051144336518103337076348631570389442958173832961158164136909101386) * 10 ^ 70 +
        4486921723891906398347521859826185006966572617744977765154293230573797) * 10 ^ 70 +
        3089507662092962800577923092672713642469148821040017610371046212816541) * 10 ^ 70 +
        3988792303189554069242006383127842499304376097178892780475224909944463) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (160 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (161 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_161 :
    recurrence4Scalar1First.coeff 161 =
      -(((((694 * 10 ^ 70 +
        8569611468916670466865635724903017699007332673583049011958060086661806) * 10 ^ 70 +
        2970732491231334792850565994912749017164372070769984561830733521677783) * 10 ^ 70 +
        1371541958763852296512146098484167228555198603873689422488892145794188) * 10 ^ 70 +
        5769720048723013454012678394525386279197996925542437516185064886661100) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (161 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (162 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_162 :
    recurrence4Scalar1First.coeff 162 =
      (((((2519 * 10 ^ 70 +
        9055455867315514481903928856497157986012014989200775968271312610575185) * 10 ^ 70 +
        2039199791827158454446805462928367164010108767514568027277167447921028) * 10 ^ 70 +
        5584427900511414345116766949971620013918970209359326125261741201795232) * 10 ^ 70 +
        2978174567019601221037741190275672531901331266849038001769280158986255) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (162 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (163 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_163 :
    recurrence4Scalar1First.coeff 163 =
      -(((((8995 * 10 ^ 70 +
        7704581856136851449615952889967925626601248908331356388173189758622967) * 10 ^ 70 +
        1686973289191469859355323551314551833258737743761972888118338070186259) * 10 ^ 70 +
        6421485465806721793805788211191444441346209930611656755346989705085673) * 10 ^ 70 +
        3523674885449205906417244690206771804708968321257836898032599438520877) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (163 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (164 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_164 :
    recurrence4Scalar1First.coeff 164 =
      (((((31614 * 10 ^ 70 +
        8617039373880430844286395647277597159439644419972955698240008109298803) * 10 ^ 70 +
        1227574831977048611064694346285889362696236098496204275868840905600439) * 10 ^ 70 +
        7914275127278653443423468435338617674389614666231659736212871538180200) * 10 ^ 70 +
        1868883647083744865292156852180086107032669731535970017642499144101446) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (164 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (165 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_165 :
    recurrence4Scalar1First.coeff 165 =
      -(((((109389 * 10 ^ 70 +
        5123863631919108133567584919745505719572927134462223152606640025294812) * 10 ^ 70 +
        4161116086086867936038596467662502285069034846491262907577357064907358) * 10 ^ 70 +
        2959784863232612530479303526578654167267744736605589992527359080459223) * 10 ^ 70 +
        9366709071691576487432141947942338538336976669250155347670020398353767) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (165 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (166 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_166 :
    recurrence4Scalar1First.coeff 166 =
      (((((372669 * 10 ^ 70 +
        0638113284571282477956297995838104530146320848175217001957440012102365) * 10 ^ 70 +
        6637128869538721454959657058052474761918295479986855052733840339209551) * 10 ^ 70 +
        2204751348997537002288784782782484768990124929257903427276320366338930) * 10 ^ 70 +
        9582925995584639091451763413929659961333913115772657883603790611657785) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (166 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (167 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_167 :
    recurrence4Scalar1First.coeff 167 =
      -(((((1250158 * 10 ^ 70 +
        7593700921199363533315826430013491544716282471545741716385403184410587) * 10 ^ 70 +
        3369059332269473661789267300209347175207882928631880630020718287075805) * 10 ^ 70 +
        9526824134806112050993054969062886017674621360816872027577119737287428) * 10 ^ 70 +
        1947487046997200421814006498185249979731162127345745990384541251104004) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (167 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (168 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_168 :
    recurrence4Scalar1First.coeff 168 =
      (((((4129821 * 10 ^ 70 +
        0565751418866779850329968749500210973959936367025398323117615145092064) * 10 ^ 70 +
        0739819954692473996217158928431096288434857724654192858505743477739361) * 10 ^ 70 +
        0227731389255940450205122724715533333926660272732214380296715378675696) * 10 ^ 70 +
        8813887265003234576646737845147898794274527994919472290036426128389832) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (168 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (169 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_169 :
    recurrence4Scalar1First.coeff 169 =
      -(((((13435405 * 10 ^ 70 +
        7537136954609990347489017200692624451693390861809719573653559014849505) * 10 ^ 70 +
        5453209989373573093881375927414750429833968436800855470890797311201901) * 10 ^ 70 +
        1414246776809663467353734150637642437157202765019585801840106595928992) * 10 ^ 70 +
        8596968900838905484570132677906829603342420664095241124263658307722291) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (169 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (170 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_170 :
    recurrence4Scalar1First.coeff 170 =
      (((((43047929 * 10 ^ 70 +
        3131165868554641397005368402516187585552207958524581760557583386589883) * 10 ^ 70 +
        7042819105642659265381420639116216183876617249760696200447412044311777) * 10 ^ 70 +
        4970151567202322057937521974609862877669199024025334672221494597487894) * 10 ^ 70 +
        5377938626231457310282902299271655489757478866416011161237411760704392) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (170 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
