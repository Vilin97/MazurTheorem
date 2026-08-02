/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_1
  recurrence4A0_coeff_10
  recurrence4A0_coeff_100
  recurrence4A0_coeff_101
  recurrence4A0_coeff_102
  recurrence4A0_coeff_103
  recurrence4A0_coeff_104
  recurrence4A0_coeff_105
  recurrence4A0_coeff_106
  recurrence4A0_coeff_107
  recurrence4A0_coeff_108
  recurrence4A0_coeff_109
  recurrence4A0_coeff_11
  recurrence4A0_coeff_110
  recurrence4A0_coeff_111
  recurrence4A0_coeff_112
  recurrence4A0_coeff_113
  recurrence4A0_coeff_114
  recurrence4A0_coeff_115
  recurrence4A0_coeff_116
  recurrence4A0_coeff_117
  recurrence4A0_coeff_118
  recurrence4A0_coeff_119
  recurrence4A0_coeff_12
  recurrence4A0_coeff_120
  recurrence4A0_coeff_121
  recurrence4A0_coeff_122
  recurrence4A0_coeff_123
  recurrence4A0_coeff_124
  recurrence4A0_coeff_125
  recurrence4A0_coeff_126
  recurrence4A0_coeff_127
  recurrence4A0_coeff_128
  recurrence4A0_coeff_129
  recurrence4A0_coeff_13
  recurrence4A0_coeff_130
  recurrence4A0_coeff_131
  recurrence4A0_coeff_132
  recurrence4A0_coeff_133
  recurrence4A0_coeff_134
  recurrence4A0_coeff_135
  recurrence4A0_coeff_136
  recurrence4A0_coeff_137
  recurrence4A0_coeff_138
  recurrence4A0_coeff_139
  recurrence4A0_coeff_14
  recurrence4A0_coeff_140
  recurrence4A0_coeff_141
  recurrence4A0_coeff_142
  recurrence4A0_coeff_143
  recurrence4A0_coeff_144
  recurrence4A0_coeff_145
  recurrence4A0_coeff_146
  recurrence4A0_coeff_147
  recurrence4A0_coeff_148
  recurrence4A0_coeff_149
  recurrence4A0_coeff_15
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156

attribute [local simp]
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_16
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_17
  recurrence4A0_coeff_18
  recurrence4A0_coeff_19
  recurrence4A0_coeff_2
  recurrence4A0_coeff_20
  recurrence4A0_coeff_21
  recurrence4A0_coeff_22
  recurrence4A0_coeff_23
  recurrence4A0_coeff_24
  recurrence4A0_coeff_25
  recurrence4A0_coeff_26
  recurrence4A0_coeff_27
  recurrence4A0_coeff_28
  recurrence4A0_coeff_29
  recurrence4A0_coeff_3
  recurrence4A0_coeff_30
  recurrence4A0_coeff_31
  recurrence4A0_coeff_32
  recurrence4A0_coeff_33
  recurrence4A0_coeff_34
  recurrence4A0_coeff_35
  recurrence4A0_coeff_36
  recurrence4A0_coeff_37
  recurrence4A0_coeff_38
  recurrence4A0_coeff_39
  recurrence4A0_coeff_4
  recurrence4A0_coeff_40
  recurrence4A0_coeff_41
  recurrence4A0_coeff_42
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
  recurrence4A0_coeff_5
  recurrence4A0_coeff_50
  recurrence4A0_coeff_51
  recurrence4A0_coeff_52
  recurrence4A0_coeff_53
  recurrence4A0_coeff_54
  recurrence4A0_coeff_55
  recurrence4A0_coeff_56
  recurrence4A0_coeff_57
  recurrence4A0_coeff_58
  recurrence4A0_coeff_59
  recurrence4A0_coeff_6
  recurrence4A0_coeff_60
  recurrence4A0_coeff_61
  recurrence4A0_coeff_62
  recurrence4A0_coeff_63
  recurrence4A0_coeff_64
  recurrence4A0_coeff_65
  recurrence4A0_coeff_66
  recurrence4A0_coeff_67
  recurrence4A0_coeff_68

attribute [local simp]
  recurrence4A0_coeff_69
  recurrence4A0_coeff_7
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
  recurrence4A0_coeff_8
  recurrence4A0_coeff_80
  recurrence4A0_coeff_81
  recurrence4A0_coeff_82
  recurrence4A0_coeff_83
  recurrence4A0_coeff_84
  recurrence4A0_coeff_85
  recurrence4A0_coeff_86
  recurrence4A0_coeff_87
  recurrence4A0_coeff_88
  recurrence4A0_coeff_89
  recurrence4A0_coeff_9
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1
  recurrence4LeadingSquare_coeff_10
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_11
  recurrence4LeadingSquare_coeff_110
  recurrence4LeadingSquare_coeff_111
  recurrence4LeadingSquare_coeff_112
  recurrence4LeadingSquare_coeff_113
  recurrence4LeadingSquare_coeff_114
  recurrence4LeadingSquare_coeff_115
  recurrence4LeadingSquare_coeff_116
  recurrence4LeadingSquare_coeff_117
  recurrence4LeadingSquare_coeff_118
  recurrence4LeadingSquare_coeff_119
  recurrence4LeadingSquare_coeff_12
  recurrence4LeadingSquare_coeff_120
  recurrence4LeadingSquare_coeff_121
  recurrence4LeadingSquare_coeff_122
  recurrence4LeadingSquare_coeff_123
  recurrence4LeadingSquare_coeff_124

attribute [local simp]
  recurrence4LeadingSquare_coeff_125
  recurrence4LeadingSquare_coeff_126
  recurrence4LeadingSquare_coeff_127
  recurrence4LeadingSquare_coeff_128
  recurrence4LeadingSquare_coeff_129
  recurrence4LeadingSquare_coeff_13
  recurrence4LeadingSquare_coeff_130
  recurrence4LeadingSquare_coeff_131
  recurrence4LeadingSquare_coeff_132
  recurrence4LeadingSquare_coeff_133
  recurrence4LeadingSquare_coeff_134
  recurrence4LeadingSquare_coeff_135
  recurrence4LeadingSquare_coeff_136
  recurrence4LeadingSquare_coeff_137
  recurrence4LeadingSquare_coeff_138
  recurrence4LeadingSquare_coeff_139
  recurrence4LeadingSquare_coeff_14
  recurrence4LeadingSquare_coeff_140
  recurrence4LeadingSquare_coeff_141
  recurrence4LeadingSquare_coeff_142
  recurrence4LeadingSquare_coeff_143
  recurrence4LeadingSquare_coeff_144
  recurrence4LeadingSquare_coeff_145
  recurrence4LeadingSquare_coeff_146
  recurrence4LeadingSquare_coeff_147
  recurrence4LeadingSquare_coeff_148
  recurrence4LeadingSquare_coeff_149
  recurrence4LeadingSquare_coeff_15
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_16
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_17
  recurrence4LeadingSquare_coeff_18
  recurrence4LeadingSquare_coeff_19
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_22
  recurrence4LeadingSquare_coeff_23
  recurrence4LeadingSquare_coeff_24
  recurrence4LeadingSquare_coeff_25
  recurrence4LeadingSquare_coeff_26
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_28
  recurrence4LeadingSquare_coeff_29
  recurrence4LeadingSquare_coeff_3
  recurrence4LeadingSquare_coeff_30
  recurrence4LeadingSquare_coeff_31
  recurrence4LeadingSquare_coeff_32
  recurrence4LeadingSquare_coeff_33
  recurrence4LeadingSquare_coeff_34
  recurrence4LeadingSquare_coeff_35
  recurrence4LeadingSquare_coeff_36
  recurrence4LeadingSquare_coeff_37

attribute [local simp]
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_4
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_5
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_6
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69
  recurrence4LeadingSquare_coeff_7
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_8
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_9
  recurrence4LeadingSquare_coeff_90
  recurrence4LeadingSquare_coeff_91
  recurrence4LeadingSquare_coeff_92
  recurrence4LeadingSquare_coeff_93
  recurrence4LeadingSquare_coeff_94
  recurrence4LeadingSquare_coeff_95

attribute [local simp]
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

private theorem recurrence4Scalar0Left_coeff_0_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (x) *
        remainder4Coefficient0.coeff (0 - (x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < x
  · rw [recurrence4LeadingSquare_coeff_high (x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (0 - (x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_0 :
    recurrence4Scalar0Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_0_suffix_zero]

private theorem recurrence4Scalar0Left_coeff_1_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (1 + x) *
        remainder4Coefficient0.coeff (1 - (1 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 1 + x
  · rw [recurrence4LeadingSquare_coeff_high (1 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (1 - (1 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_1 :
    recurrence4Scalar0Left.coeff 1 =
      (-956033368688907243392302809638568532869120 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_1_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_2_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (2 + x) *
        remainder4Coefficient0.coeff (2 - (2 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 2 + x
  · rw [recurrence4LeadingSquare_coeff_high (2 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (2 - (2 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_2 :
    recurrence4Scalar0Left.coeff 2 =
      (2035939666856210925036617294642176608682192896 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_2_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_3_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (3 + x) *
        remainder4Coefficient0.coeff (3 - (3 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 3 + x
  · rw [recurrence4LeadingSquare_coeff_high (3 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (3 - (3 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_3 :
    recurrence4Scalar0Left.coeff 3 =
      (21162950099910863018132271059959809869575315353600 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_3_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_4_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (4 + x) *
        remainder4Coefficient0.coeff (4 - (4 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 4 + x
  · rw [recurrence4LeadingSquare_coeff_high (4 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (4 - (4 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_4 :
    recurrence4Scalar0Left.coeff 4 =
      (-132290974344460475854466767936055460169212491505454848 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_4_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_5_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (5 + x) *
        remainder4Coefficient0.coeff (5 - (5 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 5 + x
  · rw [recurrence4LeadingSquare_coeff_high (5 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (5 - (5 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_5 :
    recurrence4Scalar0Left.coeff 5 =
      (350840852257233413802932470543512662399192681836079108352 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_5_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_6_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (6 + x) *
        remainder4Coefficient0.coeff (6 - (6 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 6 + x
  · rw [recurrence4LeadingSquare_coeff_high (6 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (6 - (6 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_6 :
    recurrence4Scalar0Left.coeff 6 =
      (-540881519986109736505128043780595679960896334359076814770000 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_6_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_7_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (7 + x) *
        remainder4Coefficient0.coeff (7 - (7 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 7 + x
  · rw [recurrence4LeadingSquare_coeff_high (7 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (7 - (7 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_7 :
    recurrence4Scalar0Left.coeff 7 =
      (524983290515435684698342384717972549255836054710467167554359776 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_7_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_8_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (8 + x) *
        remainder4Coefficient0.coeff (8 - (8 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 8 + x
  · rw [recurrence4LeadingSquare_coeff_high (8 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (8 - (8 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_8 :
    recurrence4Scalar0Left.coeff 8 =
      (-333524259082078755982462545762437962674345925659675531696185925252 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_8_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_9_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (9 + x) *
        remainder4Coefficient0.coeff (9 - (9 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 9 + x
  · rw [recurrence4LeadingSquare_coeff_high (9 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (9 - (9 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_9 :
    recurrence4Scalar0Left.coeff 9 =
      (151777817199192759287214497564225748840832069387794482193977366505132 : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_9_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_10_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (10 + x) *
        remainder4Coefficient0.coeff (10 - (10 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 10 + x
  · rw [recurrence4LeadingSquare_coeff_high (10 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (10 - (10 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_10 :
    recurrence4Scalar0Left.coeff 10 =
      -((6 * 10 ^ 70 +
        3789438510792076960782734964570318940419596928608868674638697912670040) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_10_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_11_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (11 + x) *
        remainder4Coefficient0.coeff (11 - (11 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 11 + x
  · rw [recurrence4LeadingSquare_coeff_high (11 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (11 - (11 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_11 :
    recurrence4Scalar0Left.coeff 11 =
      ((2592 * 10 ^ 70 +
        3167865687119761642664514784601965405424619836747514422743908793760124) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_11_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_12_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (12 + x) *
        remainder4Coefficient0.coeff (12 - (12 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 12 + x
  · rw [recurrence4LeadingSquare_coeff_high (12 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (12 - (12 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_12 :
    recurrence4Scalar0Left.coeff 12 =
      -((568923 * 10 ^ 70 +
        1659608789426311409756512620529417252395361292148718427698406375340284) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_12_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_13_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (13 + x) *
        remainder4Coefficient0.coeff (13 - (13 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 13 + x
  · rw [recurrence4LeadingSquare_coeff_high (13 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (13 - (13 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_13 :
    recurrence4Scalar0Left.coeff 13 =
      -((202360450 * 10 ^ 70 +
        7165551712562588561660997133327850925868150049692146174663792209665300) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_13_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_14_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (14 + x) *
        remainder4Coefficient0.coeff (14 - (14 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 14 + x
  · rw [recurrence4LeadingSquare_coeff_high (14 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (14 - (14 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_14 :
    recurrence4Scalar0Left.coeff 14 =
      ((242965396393 * 10 ^ 70 +
        1870840738803041745158510643530619584035315549282566530860646923054488) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_14_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_15_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (15 + x) *
        remainder4Coefficient0.coeff (15 - (15 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 15 + x
  · rw [recurrence4LeadingSquare_coeff_high (15 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (15 - (15 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_15 :
    recurrence4Scalar0Left.coeff 15 =
      -((123818725105637 * 10 ^ 70 +
        1836213643208900308846640671667505322224185146058273913040947443180800) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_15_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_16_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (16 + x) *
        remainder4Coefficient0.coeff (16 - (16 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 16 + x
  · rw [recurrence4LeadingSquare_coeff_high (16 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (16 - (16 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_16 :
    recurrence4Scalar0Left.coeff 16 =
      ((49654403603503748 * 10 ^ 70 +
        6639550767040404652350944201738236930899183236575123267269417323319080) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_16_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_17_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (17 + x) *
        remainder4Coefficient0.coeff (17 - (17 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 17 + x
  · rw [recurrence4LeadingSquare_coeff_high (17 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (17 - (17 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_17 :
    recurrence4Scalar0Left.coeff 17 =
      -((18053053522028586943 * 10 ^ 70 +
        3069629735590447067482767815719921956976229161076283549152031154322256) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_17_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_18_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (18 + x) *
        remainder4Coefficient0.coeff (18 - (18 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 18 + x
  · rw [recurrence4LeadingSquare_coeff_high (18 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (18 - (18 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_18 :
    recurrence4Scalar0Left.coeff 18 =
      ((4981747561080371216148 * 10 ^ 70 +
        0107192382786951188043995135256494465960449098499746309522210144390347) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_18_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_19_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (19 + x) *
        remainder4Coefficient0.coeff (19 - (19 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 19 + x
  · rw [recurrence4LeadingSquare_coeff_high (19 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (19 - (19 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_19 :
    recurrence4Scalar0Left.coeff 19 =
      -((358983589670808836926496 * 10 ^ 70 +
        4482974327494428523924939678169229001249598689372628397221483771902177) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_19_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_20_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (20 + x) *
        remainder4Coefficient0.coeff (20 - (20 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 20 + x
  · rw [recurrence4LeadingSquare_coeff_high (20 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (20 - (20 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_20 :
    recurrence4Scalar0Left.coeff 20 =
      -((517940007395599801627754419 * 10 ^ 70 +
        8812688751161534451079640041451319179553215959363207736293405142954496) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_20_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_21_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (21 + x) *
        remainder4Coefficient0.coeff (21 - (21 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 21 + x
  · rw [recurrence4LeadingSquare_coeff_high (21 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (21 - (21 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_21 :
    recurrence4Scalar0Left.coeff 21 =
      ((333436542743350296690626252187 * 10 ^ 70 +
        2762936406697982388858516320402479269749626164023637817064415181599287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_21_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_22_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (22 + x) *
        remainder4Coefficient0.coeff (22 - (22 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 22 + x
  · rw [recurrence4LeadingSquare_coeff_high (22 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (22 - (22 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_22 :
    recurrence4Scalar0Left.coeff 22 =
      -((118380423911552037331777863563626 * 10 ^ 70 +
        7366003131222934670919448671173408360037866138533459590830770527416120) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_22_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_23_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (23 + x) *
        remainder4Coefficient0.coeff (23 - (23 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 23 + x
  · rw [recurrence4LeadingSquare_coeff_high (23 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (23 - (23 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_23 :
    recurrence4Scalar0Left.coeff 23 =
      ((28541749487957886905182207116071974 * 10 ^ 70 +
        5971678299132564895549215348107910257587985217095350427445536189928851) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_23_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_24_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (24 + x) *
        remainder4Coefficient0.coeff (24 - (24 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 24 + x
  · rw [recurrence4LeadingSquare_coeff_high (24 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (24 - (24 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_24 :
    recurrence4Scalar0Left.coeff 24 =
      -((4593276624478587063442805627586039543 * 10 ^ 70 +
        5646380173268724972492095228311240760832707924102554758634350466314540) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_24_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_25_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (25 + x) *
        remainder4Coefficient0.coeff (25 - (25 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 25 + x
  · rw [recurrence4LeadingSquare_coeff_high (25 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (25 - (25 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_25 :
    recurrence4Scalar0Left.coeff 25 =
      ((314575394241842978066401606684469886961 * 10 ^ 70 +
        1862660831899487752141058172230858260149791746714504580968234561886289) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_25_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_26_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (26 + x) *
        remainder4Coefficient0.coeff (26 - (26 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 26 + x
  · rw [recurrence4LeadingSquare_coeff_high (26 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (26 - (26 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_26 :
    recurrence4Scalar0Left.coeff 26 =
      ((90188739822873726597645640712345975407336 * 10 ^ 70 +
        1848408656321956770453570574339366768476405372777930598330545271736192) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_26_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_27_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (27 + x) *
        remainder4Coefficient0.coeff (27 - (27 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 27 + x
  · rw [recurrence4LeadingSquare_coeff_high (27 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (27 - (27 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_27 :
    recurrence4Scalar0Left.coeff 27 =
      -((47472945155781104805881557576272279970829270 * 10 ^ 70 +
        2463096933659531822014426013344799255186839795914061129044617960421811) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_27_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_28_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (28 + x) *
        remainder4Coefficient0.coeff (28 - (28 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 28 + x
  · rw [recurrence4LeadingSquare_coeff_high (28 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (28 - (28 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_28 :
    recurrence4Scalar0Left.coeff 28 =
      ((14860783678875038475650658693032404309568113452 * 10 ^ 70 +
        5062683973086312434130255268409539615405407396157439143558632436092881) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_28_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_29_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (29 + x) *
        remainder4Coefficient0.coeff (29 - (29 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 29 + x
  · rw [recurrence4LeadingSquare_coeff_high (29 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (29 - (29 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_29 :
    recurrence4Scalar0Left.coeff 29 =
      -((4009486755537940051369205241685237169159833060881 * 10 ^ 70 +
        0448703897744713800821481200751062039777913283766194757810194023803389) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_29_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_30_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (30 + x) *
        remainder4Coefficient0.coeff (30 - (30 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 30 + x
  · rw [recurrence4LeadingSquare_coeff_high (30 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (30 - (30 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_30 :
    recurrence4Scalar0Left.coeff 30 =
      ((991325432159248126817767444863576661726970409518664 * 10 ^ 70 +
        4763689709160270247270502862119605829291747742375935454158963160288750) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_30_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_31_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (31 + x) *
        remainder4Coefficient0.coeff (31 - (31 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 31 + x
  · rw [recurrence4LeadingSquare_coeff_high (31 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (31 - (31 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_31 :
    recurrence4Scalar0Left.coeff 31 =
      -((222766125487281248884502158755589038328448550491205800 * 10 ^ 70 +
        1732260284052116144575532853231655950920389723961399212879042225177039) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_31_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_32_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (32 + x) *
        remainder4Coefficient0.coeff (32 - (32 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 32 + x
  · rw [recurrence4LeadingSquare_coeff_high (32 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (32 - (32 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_32 :
    recurrence4Scalar0Left.coeff 32 =
      ((44654929890076778110346828028692245495767061942482502850 * 10 ^ 70 +
        9417726356810555127461233760149721944452682589147747084437460840662033) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Left_coeff_32_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_33_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (33 + x) *
        remainder4Coefficient0.coeff (33 - (33 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 33 + x
  · rw [recurrence4LeadingSquare_coeff_high (33 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (33 - (33 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_33 :
    recurrence4Scalar0Left.coeff 33 =
      -((7877649534575521649089888418514468349733659212204717866770 * 10 ^ 70 +
        0257681197005537610461666333360155361191864936945338246990357637870317) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (33 - x)) = _
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_33_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_34_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (34 + x) *
        remainder4Coefficient0.coeff (34 - (34 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 34 + x
  · rw [recurrence4LeadingSquare_coeff_high (34 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (34 - (34 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_34 :
    recurrence4Scalar0Left.coeff 34 =
      ((1210150920670225404857902116339205835451828513386344410711212 * 10 ^ 70 +
        5020537940021549941084547637431724497652189958663978125833307096499263) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (34 - x)) = _
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_34_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_35_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (35 + x) *
        remainder4Coefficient0.coeff (35 - (35 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 35 + x
  · rw [recurrence4LeadingSquare_coeff_high (35 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (35 - (35 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_35 :
    recurrence4Scalar0Left.coeff 35 =
      -((159485364398050669542907902859913061578058157789376412863813304 * 10 ^ 70 +
        1738351069935894636310465606624129546626499136616744153639226421855041) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (35 - x)) = _
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_35_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_36_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (36 + x) *
        remainder4Coefficient0.coeff (36 - (36 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 36 + x
  · rw [recurrence4LeadingSquare_coeff_high (36 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (36 - (36 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_36 :
    recurrence4Scalar0Left.coeff 36 =
      ((17458997617944449493306055401334744682602380812007448103014489114 * 10 ^ 70 +
        5511737695482662806494079848332735542441768643389567749115293230932648) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (36 - x)) = _
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_36_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_37_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (37 + x) *
        remainder4Coefficient0.coeff (37 - (37 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 37 + x
  · rw [recurrence4LeadingSquare_coeff_high (37 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (37 - (37 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_37 :
    recurrence4Scalar0Left.coeff 37 =
      -((1450115538334776121332783482490118770744671801039095164210020281860 * 10 ^ 70 +
        5266512070043421813760936156384710075046265452476702169354751172738612) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (37 - x)) = _
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_37_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_38_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (38 + x) *
        remainder4Coefficient0.coeff (38 - (38 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 38 + x
  · rw [recurrence4LeadingSquare_coeff_high (38 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (38 - (38 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_38 :
    recurrence4Scalar0Left.coeff 38 =
      ((58134567135023988216705502136830159585781645463308808683750438152361 * 10 ^ 70 +
        2283782458052865862753310909554860781095660971061656856013732510959743) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (38 - x)) = _
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_38_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_39_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (39 + x) *
        remainder4Coefficient0.coeff (39 - (39 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 39 + x
  · rw [recurrence4LeadingSquare_coeff_high (39 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (39 - (39 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_39 :
    recurrence4Scalar0Left.coeff 39 =
      ((7983218316488806869114638024823357249500098812071243105188393523812287 * 10 ^ 70 +
        1188855890801962168088383809422999183328926029879898674033569873877527) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (39 - x)) = _
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_39_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_40_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (40 + x) *
        remainder4Coefficient0.coeff (40 - (40 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 40 + x
  · rw [recurrence4LeadingSquare_coeff_high (40 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (40 - (40 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_40 :
    recurrence4Scalar0Left.coeff 40 =
      -(((240 * 10 ^ 70 +
        4111273167440109873820575764523366089483163955615204110000101011596498) * 10 ^ 70 +
        9011788551168566615622936198576158482118123357198785910778896620661411) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (40 - x)) = _
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_40_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_41_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (41 + x) *
        remainder4Coefficient0.coeff (41 - (41 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 41 + x
  · rw [recurrence4LeadingSquare_coeff_high (41 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (41 - (41 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_41 :
    recurrence4Scalar0Left.coeff 41 =
      (((38001 * 10 ^ 70 +
        5281154893136255016670484768814372122353520153118030782931967139550779) * 10 ^ 70 +
        1149150433381571411427574049261753981101940435694595870813860770556192) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (41 - x)) = _
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_41_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_42_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (42 + x) *
        remainder4Coefficient0.coeff (42 - (42 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 42 + x
  · rw [recurrence4LeadingSquare_coeff_high (42 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (42 - (42 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_42 :
    recurrence4Scalar0Left.coeff 42 =
      -(((4558517 * 10 ^ 70 +
        4260162740111173661251142196996193155541469239280333940658676694824779) * 10 ^ 70 +
        9869163515079238264490496138039070297498702919421614501463058117983600) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (42 - x)) = _
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_42_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_43_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (43 + x) *
        remainder4Coefficient0.coeff (43 - (43 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 43 + x
  · rw [recurrence4LeadingSquare_coeff_high (43 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (43 - (43 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_43 :
    recurrence4Scalar0Left.coeff 43 =
      (((443190844 * 10 ^ 70 +
        6694123409281301221569022275883461789472928056782417762011888047430581) * 10 ^ 70 +
        6543614874964110480550307228085215688886057389110851282461568763032344) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (43 - x)) = _
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_43_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_44_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (44 + x) *
        remainder4Coefficient0.coeff (44 - (44 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 44 + x
  · rw [recurrence4LeadingSquare_coeff_high (44 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (44 - (44 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_44 :
    recurrence4Scalar0Left.coeff 44 =
      -(((34527517776 * 10 ^ 70 +
        2533904207089532906223147920152272953564480188397780369275393043113081) * 10 ^ 70 +
        2576623312912762317353579325972093152850924712443762909387893598217976) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (44 - x)) = _
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_44_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_45_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (45 + x) *
        remainder4Coefficient0.coeff (45 - (45 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 45 + x
  · rw [recurrence4LeadingSquare_coeff_high (45 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (45 - (45 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_45 :
    recurrence4Scalar0Left.coeff 45 =
      (((1910832277761 * 10 ^ 70 +
        4785779100988140419101845934704381011308919785663287383054648242595294) * 10 ^ 70 +
        6987449279366145714819692895908604429702891253175307895454957028895547) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (45 - x)) = _
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_45_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_46_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (46 + x) *
        remainder4Coefficient0.coeff (46 - (46 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 46 + x
  · rw [recurrence4LeadingSquare_coeff_high (46 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (46 - (46 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_46 :
    recurrence4Scalar0Left.coeff 46 =
      -(((22781767535167 * 10 ^ 70 +
        6023402979944987577577754790006636691779656473697242080076937979870708) * 10 ^ 70 +
        9052427899566584058026022566736773443004634521464786416647159816462937) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (46 - x)) = _
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_46_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_47_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (47 + x) *
        remainder4Coefficient0.coeff (47 - (47 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 47 + x
  · rw [recurrence4LeadingSquare_coeff_high (47 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (47 - (47 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_47 :
    recurrence4Scalar0Left.coeff 47 =
      -(((12028918499149839 * 10 ^ 70 +
        1846144379037361221944721551379118233937550354177136922437781808997868) * 10 ^ 70 +
        2093810432418136430729156431220034479096616075020536689716959542656287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (47 - x)) = _
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_47_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_48_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (48 + x) *
        remainder4Coefficient0.coeff (48 - (48 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 48 + x
  · rw [recurrence4LeadingSquare_coeff_high (48 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (48 - (48 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_48 :
    recurrence4Scalar0Left.coeff 48 =
      (((2136368621102294231 * 10 ^ 70 +
        1079750537344504929876182011649666485911989174917325815599412911145869) * 10 ^ 70 +
        6227561630131234524403065074509872953436241574619765403901242707751530) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (48 - x)) = _
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_48_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_49_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (49 + x) *
        remainder4Coefficient0.coeff (49 - (49 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 49 + x
  · rw [recurrence4LeadingSquare_coeff_high (49 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (49 - (49 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_49 :
    recurrence4Scalar0Left.coeff 49 =
      -(((251547369497685171175 * 10 ^ 70 +
        7824942957700164079081590366373891448027260376137528997652384171467270) * 10 ^ 70 +
        6209282206947599568105339281768064329716014120715673586643718153159222) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (49 - x)) = _
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_49_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_50_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (50 + x) *
        remainder4Coefficient0.coeff (50 - (50 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 50 + x
  · rw [recurrence4LeadingSquare_coeff_high (50 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (50 - (50 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_50 :
    recurrence4Scalar0Left.coeff 50 =
      (((24346248404410341157012 * 10 ^ 70 +
        1514641543862408058511125639660316210423639262299550993736213131364567) * 10 ^ 70 +
        3426164228166857885840637225827561187690250939306269609950240497019275) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (50 - x)) = _
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_50_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_51_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (51 + x) *
        remainder4Coefficient0.coeff (51 - (51 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 51 + x
  · rw [recurrence4LeadingSquare_coeff_high (51 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (51 - (51 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_51 :
    recurrence4Scalar0Left.coeff 51 =
      -(((2064406062535130821722014 * 10 ^ 70 +
        4463286506593592066321072564980104259565514056721030699071021318119984) * 10 ^ 70 +
        2702179945183116400006670290058663873999981334237329245781253580254557) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (51 - x)) = _
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_51_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_52_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (52 + x) *
        remainder4Coefficient0.coeff (52 - (52 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 52 + x
  · rw [recurrence4LeadingSquare_coeff_high (52 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (52 - (52 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_52 :
    recurrence4Scalar0Left.coeff 52 =
      (((157789986329012843071787155 * 10 ^ 70 +
        8254931901052224852216906721650421109502634479381740787856220660602042) * 10 ^ 70 +
        1096388111164052151511227265247656518290502649625290571836965688568302) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (52 - x)) = _
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_52_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_53_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (53 + x) *
        remainder4Coefficient0.coeff (53 - (53 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 53 + x
  · rw [recurrence4LeadingSquare_coeff_high (53 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (53 - (53 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_53 :
    recurrence4Scalar0Left.coeff 53 =
      -(((11042594003763968968714548594 * 10 ^ 70 +
        1495239039181503563604517722576282135341192730858790811923489064085013) * 10 ^ 70 +
        5357788014430445404699853096795617806995853483725641984749397475338950) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (53 - x)) = _
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_53_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_54_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (54 + x) *
        remainder4Coefficient0.coeff (54 - (54 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 54 + x
  · rw [recurrence4LeadingSquare_coeff_high (54 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (54 - (54 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_54 :
    recurrence4Scalar0Left.coeff 54 =
      (((714491855508415378571944036865 * 10 ^ 70 +
        2266349460104601107895469291887679533835288710648929764047595804303177) * 10 ^ 70 +
        1107255919611041330435694578080393042700531492557935258018009044046853) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (54 - x)) = _
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_54_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_55_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (55 + x) *
        remainder4Coefficient0.coeff (55 - (55 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 55 + x
  · rw [recurrence4LeadingSquare_coeff_high (55 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (55 - (55 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_55 :
    recurrence4Scalar0Left.coeff 55 =
      -(((43025889348345054023874462573630 * 10 ^ 70 +
        5749874122913476493408122567728166161603717152314568730035211752832066) * 10 ^ 70 +
        8107804106089387748339082585014806453554852149610797836317510974328255) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (55 - x)) = _
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_55_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_56_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (56 + x) *
        remainder4Coefficient0.coeff (56 - (56 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 56 + x
  · rw [recurrence4LeadingSquare_coeff_high (56 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (56 - (56 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_56 :
    recurrence4Scalar0Left.coeff 56 =
      (((2422955436231366272363475581324589 * 10 ^ 70 +
        3913743660051217937144880151326754942471077164907071611153114054693994) * 10 ^ 70 +
        6882735750177578499165664238509108240030102573038503113602891544274283) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (56 - x)) = _
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_56_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_57_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (57 + x) *
        remainder4Coefficient0.coeff (57 - (57 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 57 + x
  · rw [recurrence4LeadingSquare_coeff_high (57 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (57 - (57 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_57 :
    recurrence4Scalar0Left.coeff 57 =
      -(((128060700447982653354194803887280913 * 10 ^ 70 +
        3528281100109894536392630801211186599645506724827706384416952435401606) * 10 ^ 70 +
        4730462643776946129814150113793112566042212858758356722917009318387751) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (57 - x)) = _
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_57_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_58_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (58 + x) *
        remainder4Coefficient0.coeff (58 - (58 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 58 + x
  · rw [recurrence4LeadingSquare_coeff_high (58 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (58 - (58 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_58 :
    recurrence4Scalar0Left.coeff 58 =
      (((6370472363502890833301238446746037215 * 10 ^ 70 +
        1426259858183905892829797053978458735410977887705093075718850991120769) * 10 ^ 70 +
        5064730399999307804433036624194506642510338402661162267592912700303122) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (58 - x)) = _
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_58_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_59_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (59 + x) *
        remainder4Coefficient0.coeff (59 - (59 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 59 + x
  · rw [recurrence4LeadingSquare_coeff_high (59 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (59 - (59 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_59 :
    recurrence4Scalar0Left.coeff 59 =
      -(((298950335688795679033121401750533446460 * 10 ^ 70 +
        4897027325534179392091961693504515270762382367568135652547344611721080) * 10 ^ 70 +
        0362832568416544108532751014887722425690026589396449133342615773028926) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (59 - x)) = _
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_59_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_60_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (60 + x) *
        remainder4Coefficient0.coeff (60 - (60 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 60 + x
  · rw [recurrence4LeadingSquare_coeff_high (60 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (60 - (60 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_60 :
    recurrence4Scalar0Left.coeff 60 =
      (((13258694976504515455742934688053724842740 * 10 ^ 70 +
        1957872107783871608158495256219345385806526793343723287574624850092788) * 10 ^ 70 +
        7768213451550156840085158999961877697023517608791690522606264702979289) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (60 - x)) = _
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_60_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_61_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (61 + x) *
        remainder4Coefficient0.coeff (61 - (61 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 61 + x
  · rw [recurrence4LeadingSquare_coeff_high (61 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (61 - (61 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_61 :
    recurrence4Scalar0Left.coeff 61 =
      -(((556588575939450457332142574338175650376381 * 10 ^ 70 +
        8271354462440336025928278939570000684896961242616799953854204575871767) * 10 ^ 70 +
        9029405088391327431177058498987695223061272514726180676314291521066647) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (61 - x)) = _
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_61_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_62_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (62 + x) *
        remainder4Coefficient0.coeff (62 - (62 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 62 + x
  · rw [recurrence4LeadingSquare_coeff_high (62 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (62 - (62 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_62 :
    recurrence4Scalar0Left.coeff 62 =
      (((22142983355844128234871920744080284027573785 * 10 ^ 70 +
        9222597438941621098751869863563950937900602155060159814430356536681840) * 10 ^ 70 +
        5025798318948384387178856405863890527852060067816209514817920992254143) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (62 - x)) = _
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_62_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_63_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (63 + x) *
        remainder4Coefficient0.coeff (63 - (63 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 63 + x
  · rw [recurrence4LeadingSquare_coeff_high (63 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (63 - (63 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_63 :
    recurrence4Scalar0Left.coeff 63 =
      -(((835673477117309394887862658160478524667008582 * 10 ^ 70 +
        1227959176380755363957954972386540387996833902587104093537533086707945) * 10 ^ 70 +
        3722358511081787613137615415765028599976479896596557785744433119218496) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (63 - x)) = _
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_63_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_64_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (64 + x) *
        remainder4Coefficient0.coeff (64 - (64 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 64 + x
  · rw [recurrence4LeadingSquare_coeff_high (64 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (64 - (64 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_64 :
    recurrence4Scalar0Left.coeff 64 =
      (((29941050005790950197393061624020788742229907079 * 10 ^ 70 +
        7185916946845149611366257882949696615746771878271008823694700661655390) * 10 ^ 70 +
        2590446883976693199168689324880387535601424094121408429725587538859184) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (64 - x)) = _
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_64_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_65_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (65 + x) *
        remainder4Coefficient0.coeff (65 - (65 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 65 + x
  · rw [recurrence4LeadingSquare_coeff_high (65 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (65 - (65 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_65 :
    recurrence4Scalar0Left.coeff 65 =
      -(((1018967864265472528376782959271976095085877753406 * 10 ^ 70 +
        9990714852605643035644477961406552824711602521376279649830998716033488) * 10 ^ 70 +
        2117131178673134445239342996495352595322326792912073010091777755428087) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (65 - x)) = _
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
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_65_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_66_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (66 + x) *
        remainder4Coefficient0.coeff (66 - (66 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 66 + x
  · rw [recurrence4LeadingSquare_coeff_high (66 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (66 - (66 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_66 :
    recurrence4Scalar0Left.coeff 66 =
      (((32949320014544056050641747627004905683712728247160 * 10 ^ 70 +
        6614940447028224034398510890156795562436944343788217598553303524128356) * 10 ^ 70 +
        4250926913547332097091759878109112821786784036973703088598253834254367) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (66 - x)) = _
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
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_66_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_67_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (67 + x) *
        remainder4Coefficient0.coeff (67 - (67 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 67 + x
  · rw [recurrence4LeadingSquare_coeff_high (67 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (67 - (67 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_67 :
    recurrence4Scalar0Left.coeff 67 =
      -(((1012366463098095292706572077936745255109342006523891 * 10 ^ 70 +
        9224615700322817432143639983394190760983834389936332255630049250548455) * 10 ^ 70 +
        6428654714729838699742654992854730525210678906769045199084671306442733) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (67 - x)) = _
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
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_67_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_68_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (68 + x) *
        remainder4Coefficient0.coeff (68 - (68 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 68 + x
  · rw [recurrence4LeadingSquare_coeff_high (68 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (68 - (68 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_68 :
    recurrence4Scalar0Left.coeff 68 =
      (((29546614845204339697551798039632090456291729479790275 * 10 ^ 70 +
        8328702251288317992591405250805296021744454338638758047790157656628768) * 10 ^ 70 +
        4562809395644025728128387583871391054402091984152960425374315536240996) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (68 - x)) = _
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
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_68_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_69_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (69 + x) *
        remainder4Coefficient0.coeff (69 - (69 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 69 + x
  · rw [recurrence4LeadingSquare_coeff_high (69 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (69 - (69 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_69 :
    recurrence4Scalar0Left.coeff 69 =
      -(((818564810270816566380241802057809433833602845513007015 * 10 ^ 70 +
        9023657315438892267341899289592815383590996247027252720843369334192160) * 10 ^ 70 +
        5525998226743206481788582516878737191545336850733740646393171327180885) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (69 - x)) = _
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
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_69_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_70_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (70 + x) *
        remainder4Coefficient0.coeff (70 - (70 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 70 + x
  · rw [recurrence4LeadingSquare_coeff_high (70 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (70 - (70 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_70 :
    recurrence4Scalar0Left.coeff 70 =
      (((21499763434067793421474101801215550727478434484859157425 * 10 ^ 70 +
        8113859410640711325896823804742105974421480993837927331384588629864058) * 10 ^ 70 +
        1735582091587726997536136117436992227213052365835734988653953420208250) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (70 - x)) = _
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
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_70_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_71_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (71 + x) *
        remainder4Coefficient0.coeff (71 - (71 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 71 + x
  · rw [recurrence4LeadingSquare_coeff_high (71 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (71 - (71 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_71 :
    recurrence4Scalar0Left.coeff 71 =
      -(((534286216755380557396827564349533087523418983223039461780 * 10 ^ 70 +
        5941905845594411551712079861066501351950749375129466888826665397307648) * 10 ^ 70 +
        5328773380074387546807866329410097423484643388471461582861690916013296) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (71 - x)) = _
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
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_71_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_72_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (72 + x) *
        remainder4Coefficient0.coeff (72 - (72 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 72 + x
  · rw [recurrence4LeadingSquare_coeff_high (72 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (72 - (72 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_72 :
    recurrence4Scalar0Left.coeff 72 =
      (((12522582316623892643730113979161041121333372944073147840898 * 10 ^ 70 +
        1047344260966898382963541786723385113309823178907056778672847590825449) * 10 ^ 70 +
        4335424796254724911469723440384560262503424971355590396249603202929339) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (72 - x)) = _
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
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_72_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_73_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (73 + x) *
        remainder4Coefficient0.coeff (73 - (73 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 73 + x
  · rw [recurrence4LeadingSquare_coeff_high (73 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (73 - (73 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_73 :
    recurrence4Scalar0Left.coeff 73 =
      -(((275424373492871105539597386546613844009001096102753634843418 * 10 ^ 70 +
        5729207229439613740860653438332780144496126682794930045260109720781542) * 10 ^ 70 +
        0177400444904352621932880383502996934674674606207673948049071185738156) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (73 - x)) = _
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
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_73_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_74_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (74 + x) *
        remainder4Coefficient0.coeff (74 - (74 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 74 + x
  · rw [recurrence4LeadingSquare_coeff_high (74 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (74 - (74 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_74 :
    recurrence4Scalar0Left.coeff 74 =
      (((5637594451869060909688223330024894536150633233351187101347737 * 10 ^ 70 +
        9583228739338470354642173050342904850804315406242249992005742550895448) * 10 ^ 70 +
        1236984394595631163087328642992398035743677118422888111592400936937210) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (74 - x)) = _
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
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_74_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_75_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (75 + x) *
        remainder4Coefficient0.coeff (75 - (75 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 75 + x
  · rw [recurrence4LeadingSquare_coeff_high (75 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (75 - (75 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_75 :
    recurrence4Scalar0Left.coeff 75 =
      -(((105832534607992601390946781341936154732831323104222217088851448 * 10 ^ 70 +
        9934214351316092933609306547538763337424798219349898340829761179159387) * 10 ^ 70 +
        4515992905543326714096843576117808147330229577150761276376218692201020) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (75 - x)) = _
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
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_75_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_76_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (76 + x) *
        remainder4Coefficient0.coeff (76 - (76 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 76 + x
  · rw [recurrence4LeadingSquare_coeff_high (76 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (76 - (76 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_76 :
    recurrence4Scalar0Left.coeff 76 =
      (((1770268366545030571237332755521915622745178936516580995156217597 * 10 ^ 70 +
        0496475983230794100357615087969853697899763826330009305032778335686059) * 10 ^ 70 +
        8815840389438472504380624126782668735815392497947761594329818137372585) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (76 - x)) = _
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
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_76_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_77_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (77 + x) *
        remainder4Coefficient0.coeff (77 - (77 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 77 + x
  · rw [recurrence4LeadingSquare_coeff_high (77 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (77 - (77 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_77 :
    recurrence4Scalar0Left.coeff 77 =
      -(((24603505950326686471548493515986848469030849201240722220176265932 * 10 ^ 70 +
        0122253321720019354770543077447014219320573741169045682304568317190767) * 10 ^ 70 +
        2581916809575856029766721412591219226781399076540399262805579046005386) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (77 - x)) = _
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
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_77_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_78_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (78 + x) *
        remainder4Coefficient0.coeff (78 - (78 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 78 + x
  · rw [recurrence4LeadingSquare_coeff_high (78 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (78 - (78 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_78 :
    recurrence4Scalar0Left.coeff 78 =
      (((217926076760720290722142859219290063753548009634336733109061958085 * 10 ^ 70 +
        7060552760482739511377927516663527879844067589191608495696059322932648) * 10 ^ 70 +
        5489420132449559046845681570617919460960234270074968762058659409991969) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (78 - x)) = _
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
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_78_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_79_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (79 + x) *
        remainder4Coefficient0.coeff (79 - (79 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 79 + x
  · rw [recurrence4LeadingSquare_coeff_high (79 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (79 - (79 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_79 :
    recurrence4Scalar0Left.coeff 79 =
      (((1673048639643041946495720815330164736389579028738234457532966138561 * 10 ^ 70 +
        4139134060903693740819582752074656954601015102039424799611516548854347) * 10 ^ 70 +
        0456911714231995683263632626612181058624148438699425644727844322003118) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (79 - x)) = _
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
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_79_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_80_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (80 + x) *
        remainder4Coefficient0.coeff (80 - (80 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 80 + x
  · rw [recurrence4LeadingSquare_coeff_high (80 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (80 - (80 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_80 :
    recurrence4Scalar0Left.coeff 80 =
      -(((150354273604292061758884674484842375753657384723692167592568943023249 * 10 ^ 70 +
        6153159458717098656821212263670528671372714752218782263734229721932027) * 10 ^ 70 +
        3327212050189921311361794453915865938617218860491415517010013547784868) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (80 - x)) = _
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
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_80_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_81_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (81 + x) *
        remainder4Coefficient0.coeff (81 - (81 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 81 + x
  · rw [recurrence4LeadingSquare_coeff_high (81 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (81 - (81 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_81 :
    recurrence4Scalar0Left.coeff 81 =
      (((4981786765728666368063660286162624166841278066940512484046434351253009 * 10 ^ 70 +
        1762129820505435569771546041626096146468711873650944412719817691803241) * 10 ^ 70 +
        2957628292413822506142328195766960965260498601481653241446174414260771) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (81 - x)) = _
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
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_81_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_82_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (82 + x) *
        remainder4Coefficient0.coeff (82 - (82 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 82 + x
  · rw [recurrence4LeadingSquare_coeff_high (82 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (82 - (82 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_82 :
    recurrence4Scalar0Left.coeff 82 =
      -((((12 * 10 ^ 70 +
        7301837273871653453109977975546464419408692385790457471506556333852224) * 10 ^ 70 +
        3034948897822938594259810729028485480755012872233451767577542403496974) * 10 ^ 70 +
        5994246679932087578188387108413309425138933025214661730641388325020322) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (82 - x)) = _
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_82_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_83_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (83 + x) *
        remainder4Coefficient0.coeff (83 - (83 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 83 + x
  · rw [recurrence4LeadingSquare_coeff_high (83 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (83 - (83 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_83 :
    recurrence4Scalar0Left.coeff 83 =
      ((((281 * 10 ^ 70 +
        1742355349828597490060188186106307788062875232531916439096158671538778) * 10 ^ 70 +
        1851440391759689462039974350351558779370356263813657871702853468035446) * 10 ^ 70 +
        9967329524969851474161804409736576708991951749878001356347818694465400) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (83 - x)) = _
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
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_83_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_84_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (84 + x) *
        remainder4Coefficient0.coeff (84 - (84 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 84 + x
  · rw [recurrence4LeadingSquare_coeff_high (84 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (84 - (84 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_84 :
    recurrence4Scalar0Left.coeff 84 =
      -((((5571 * 10 ^ 70 +
        6973589885254018468354839693466303883108942971566363612041680028476878) * 10 ^ 70 +
        9319328186049321918073744999837372371027053482978597187508682344531585) * 10 ^ 70 +
        9577289611199652251477055292993631188387496235535973825782408566155892) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (84 - x)) = _
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
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_84_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_85_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (85 + x) *
        remainder4Coefficient0.coeff (85 - (85 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 85 + x
  · rw [recurrence4LeadingSquare_coeff_high (85 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (85 - (85 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_85 :
    recurrence4Scalar0Left.coeff 85 =
      ((((100317 * 10 ^ 70 +
        3152013465218831836859138496288695721617237283479965790396757069383939) * 10 ^ 70 +
        8221977815766014617374053136334199863891405400821780664031781215665719) * 10 ^ 70 +
        3435523252940950997196195705774546690076512318660328109647731992782783) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (85 - x)) = _
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
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_85_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_86_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (86 + x) *
        remainder4Coefficient0.coeff (86 - (86 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 86 + x
  · rw [recurrence4LeadingSquare_coeff_high (86 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (86 - (86 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_86 :
    recurrence4Scalar0Left.coeff 86 =
      -((((1639250 * 10 ^ 70 +
        1638350126170341529400106319763866406388677181850564839803270068677311) * 10 ^ 70 +
        3987037231085030036003351022021931418229307582025684864586408976312183) * 10 ^ 70 +
        7499187374975944850275754056063439010942525894124709658665692626778906) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (86 - x)) = _
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_86_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_87_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (87 + x) *
        remainder4Coefficient0.coeff (87 - (87 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 87 + x
  · rw [recurrence4LeadingSquare_coeff_high (87 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (87 - (87 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_87 :
    recurrence4Scalar0Left.coeff 87 =
      ((((23919922 * 10 ^ 70 +
        1226624173898458764923325098378231568741821121049394705653708171688484) * 10 ^ 70 +
        7920282606404260801297533039906673418230162889374292708593296744113445) * 10 ^ 70 +
        5400135522514710789634612829207816123902688511004907483750781504432370) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (87 - x)) = _
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
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_87_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_88_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (88 + x) *
        remainder4Coefficient0.coeff (88 - (88 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 88 + x
  · rw [recurrence4LeadingSquare_coeff_high (88 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (88 - (88 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_88 :
    recurrence4Scalar0Left.coeff 88 =
      -((((297325431 * 10 ^ 70 +
        3112194823407423820224136397595532040405700977289944640850403370867936) * 10 ^ 70 +
        3784577238991989068636925554490985366498050463472770150807910790631668) * 10 ^ 70 +
        0921768348613827437736365125401431371895342452280230944559253603424459) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (88 - x)) = _
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
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_88_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_89_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (89 + x) *
        remainder4Coefficient0.coeff (89 - (89 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 89 + x
  · rw [recurrence4LeadingSquare_coeff_high (89 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (89 - (89 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_89 :
    recurrence4Scalar0Left.coeff 89 =
      ((((2682380163 * 10 ^ 70 +
        6172666377700809967195636266173019641638348181703839262400826698472668) * 10 ^ 70 +
        4734863992658268868610745525692773497518467279450729256026565658898314) * 10 ^ 70 +
        7337910829559052052277290742847117702954285276331837678466499568964234) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (89 - x)) = _
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
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_89_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_90_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (90 + x) *
        remainder4Coefficient0.coeff (90 - (90 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 90 + x
  · rw [recurrence4LeadingSquare_coeff_high (90 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (90 - (90 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_90 :
    recurrence4Scalar0Left.coeff 90 =
      -((((1167265320 * 10 ^ 70 +
        1318691109367909353441514947164116294366398751299543817199147634664391) * 10 ^ 70 +
        1478593581820974122557484500137872072600269452514704688813137558967017) * 10 ^ 70 +
        6908381415303840350261746171215610593833181357287781005324846709281582) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (90 - x)) = _
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
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_90_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_91_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (91 + x) *
        remainder4Coefficient0.coeff (91 - (91 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 91 + x
  · rw [recurrence4LeadingSquare_coeff_high (91 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (91 - (91 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_91 :
    recurrence4Scalar0Left.coeff 91 =
      -((((720891350617 * 10 ^ 70 +
        8412404548108106748800997182410828552789314827821974384658605090018684) * 10 ^ 70 +
        2893587909559923665792549721733907570378843408689753966698192394093823) * 10 ^ 70 +
        5269729633881917609597894366251774188613991504706904139605961190217580) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (91 - x)) = _
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
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_91_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_92_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (92 + x) *
        remainder4Coefficient0.coeff (92 - (92 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 92 + x
  · rw [recurrence4LeadingSquare_coeff_high (92 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (92 - (92 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_92 :
    recurrence4Scalar0Left.coeff 92 =
      ((((23305656252322 * 10 ^ 70 +
        3399262422030462410334262475490194061518169636224916280866558497715434) * 10 ^ 70 +
        3324917358927224806416589158759888486248942952725428970567539923233790) * 10 ^ 70 +
        9273624398854588217805561768656624430271539086256833711168192033710590) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (92 - x)) = _
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
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_92_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_93_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (93 + x) *
        remainder4Coefficient0.coeff (93 - (93 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 93 + x
  · rw [recurrence4LeadingSquare_coeff_high (93 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (93 - (93 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_93 :
    recurrence4Scalar0Left.coeff 93 =
      -((((541500941232666 * 10 ^ 70 +
        8811084335905720490929652746104786873329286524791508690579347998061183) * 10 ^ 70 +
        2489666089838820706575792570828499676362074220139678678586302739725899) * 10 ^ 70 +
        5128470707859306291869926911683582876604377172646479603467973297688547) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (93 - x)) = _
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
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_93_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_94_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (94 + x) *
        remainder4Coefficient0.coeff (94 - (94 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 94 + x
  · rw [recurrence4LeadingSquare_coeff_high (94 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (94 - (94 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_94 :
    recurrence4Scalar0Left.coeff 94 =
      ((((10801120164071971 * 10 ^ 70 +
        7527271279984338084602087679231794249038845163738001403248742306134420) * 10 ^ 70 +
        0535076974613238680494849541185411377750116296362633904573371203090385) * 10 ^ 70 +
        5797619579458386619985850277819319855699187889277135836456316090657606) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (94 - x)) = _
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_94_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_95_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (95 + x) *
        remainder4Coefficient0.coeff (95 - (95 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 95 + x
  · rw [recurrence4LeadingSquare_coeff_high (95 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (95 - (95 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_95 :
    recurrence4Scalar0Left.coeff 95 =
      -((((195520904181684886 * 10 ^ 70 +
        9605159408041373721645797937635057871942479247100099667232495278655327) * 10 ^ 70 +
        5598449143641440021625457997535882255424283084119351019721329207556035) * 10 ^ 70 +
        2890543901431255903592566654736325086236095666230947506319146725531089) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (95 - x)) = _
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_95_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_96_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (96 + x) *
        remainder4Coefficient0.coeff (96 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 96 + x
  · rw [recurrence4LeadingSquare_coeff_high (96 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (96 - (96 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_96 :
    recurrence4Scalar0Left.coeff 96 =
      ((((3293327121765458463 * 10 ^ 70 +
        5189739665568590863550207078344040637263042089630665001655560507901249) * 10 ^ 70 +
        0303366534141634762367369689655977913672856181008490865621954885278230) * 10 ^ 70 +
        5297683410859280861764113987182782743430334258861520878435433635595481) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (96 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_96_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_97_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (97 + x) *
        remainder4Coefficient0.coeff (97 - (97 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 97 + x
  · rw [recurrence4LeadingSquare_coeff_high (97 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (97 - (97 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_97 :
    recurrence4Scalar0Left.coeff 97 =
      -((((52323885106779167934 * 10 ^ 70 +
        9781604901718306325025182175536158890979842883171227022028163463055693) * 10 ^ 70 +
        2012764391058947798096023124799802363867622933843783863159292921816853) * 10 ^ 70 +
        9240933170007009380043028042657682041249644750108986791798799939804889) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (97 - x)) = _
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
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_97_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_98_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (98 + x) *
        remainder4Coefficient0.coeff (98 - (98 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 98 + x
  · rw [recurrence4LeadingSquare_coeff_high (98 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (98 - (98 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_98 :
    recurrence4Scalar0Left.coeff 98 =
      ((((790689453196746369879 * 10 ^ 70 +
        0515009917705799283807268613991265460978478008817943920370735063360823) * 10 ^ 70 +
        6468324798674430030720098905547828520945719948495619897453547576280700) * 10 ^ 70 +
        0223287471507567235803216014513284562131007321622643601945354269444807) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (98 - x)) = _
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
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_98_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_99_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (99 + x) *
        remainder4Coefficient0.coeff (99 - (99 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 99 + x
  · rw [recurrence4LeadingSquare_coeff_high (99 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (99 - (99 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_99 :
    recurrence4Scalar0Left.coeff 99 =
      -((((11427751295482303261566 * 10 ^ 70 +
        4935258101913146100876446959824364460324419561440548523231672932405872) * 10 ^ 70 +
        0580790734073699170275666512780694116529525788936551991691949836462921) * 10 ^ 70 +
        5085469181161670752888138655161892820756524865829391529811129297836639) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (99 - x)) = _
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
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_99_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_100_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (100 + x) *
        remainder4Coefficient0.coeff (100 - (100 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 100 + x
  · rw [recurrence4LeadingSquare_coeff_high (100 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (100 - (100 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_100 :
    recurrence4Scalar0Left.coeff 100 =
      ((((158587895501008482492398 * 10 ^ 70 +
        8316510687979620163528872140030644433144578870786561989858367549478383) * 10 ^ 70 +
        8321389390428394213226864959473284353680431123319086331946295697567432) * 10 ^ 70 +
        0032362862975085344913798457297027223530957090107445862832816352992287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (100 - x)) = _
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
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_100_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_101_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (101 + x) *
        remainder4Coefficient0.coeff (101 - (101 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 101 + x
  · rw [recurrence4LeadingSquare_coeff_high (101 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (101 - (101 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_101 :
    recurrence4Scalar0Left.coeff 101 =
      -((((2119343666560896093707196 * 10 ^ 70 +
        7447801553911981893218984526307386025272430389502154423083122800227386) * 10 ^ 70 +
        8901551945234926700278184207775190227637309938693997316170602436733582) * 10 ^ 70 +
        8400070654306381237037956269298661710431326102168652196995133444009560) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (101 - x)) = _
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
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_101_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_102_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (102 + x) *
        remainder4Coefficient0.coeff (102 - (102 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 102 + x
  · rw [recurrence4LeadingSquare_coeff_high (102 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (102 - (102 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_102 :
    recurrence4Scalar0Left.coeff 102 =
      ((((27335948379356391712975000 * 10 ^ 70 +
        1180631519234737820470549716144117066327932819145924367133595622674456) * 10 ^ 70 +
        0598564235603791923405209220943553276340069652593768332933092040972908) * 10 ^ 70 +
        1596521183931632012919090908162922909239229401342852103032882798983645) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (102 - x)) = _
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
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_102_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_103_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (103 + x) *
        remainder4Coefficient0.coeff (103 - (103 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 103 + x
  · rw [recurrence4LeadingSquare_coeff_high (103 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (103 - (103 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_103 :
    recurrence4Scalar0Left.coeff 103 =
      -((((340917400671477545617271403 * 10 ^ 70 +
        8593353681087517582061189721311779290944425498767416590613086997515026) * 10 ^ 70 +
        7714246994602292194699376317526354530821032494894843646646995891073427) * 10 ^ 70 +
        8075334712044828536457677029234581816644916420245856260887320306739351) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (103 - x)) = _
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
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_103_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_104_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (104 + x) *
        remainder4Coefficient0.coeff (104 - (104 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 104 + x
  · rw [recurrence4LeadingSquare_coeff_high (104 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (104 - (104 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_104 :
    recurrence4Scalar0Left.coeff 104 =
      ((((4117045549774448030510618911 * 10 ^ 70 +
        7170354777767147546061934995531610200566770009507179873086075178582129) * 10 ^ 70 +
        0083906326977056943312703687405074499677945935225953354465085203842150) * 10 ^ 70 +
        9625520314293110338377612435975834409654905044184119401670321809478760) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (104 - x)) = _
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
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_104_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_105_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (105 + x) *
        remainder4Coefficient0.coeff (105 - (105 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 105 + x
  · rw [recurrence4LeadingSquare_coeff_high (105 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (105 - (105 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_105 :
    recurrence4Scalar0Left.coeff 105 =
      -((((48203509783147252418676414157 * 10 ^ 70 +
        0534892902855907650544977936180782703219759776944987939099428271225918) * 10 ^ 70 +
        3917664785390734959154554641258268767992735943367014406484759103987759) * 10 ^ 70 +
        1173268609024903780069879229984067329253859957412698469092309862760105) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (105 - x)) = _
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
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_105_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (106 + x) *
        remainder4Coefficient0.coeff (106 - (106 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 106 + x
  · rw [recurrence4LeadingSquare_coeff_high (106 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (106 - (106 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_106 :
    recurrence4Scalar0Left.coeff 106 =
      ((((547752597517484859419774155918 * 10 ^ 70 +
        5664935105567559126296457101284405237653628860979709578883167742396298) * 10 ^ 70 +
        1892779265035573228593331574669255020260515037955672296374866763977821) * 10 ^ 70 +
        5100805850843484502584134515684846713623197854435309545902101580846887) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (106 - x)) = _
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
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_106_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (107 + x) *
        remainder4Coefficient0.coeff (107 - (107 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 107 + x
  · rw [recurrence4LeadingSquare_coeff_high (107 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (107 - (107 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_107 :
    recurrence4Scalar0Left.coeff 107 =
      -((((6046423409505427397799281062817 * 10 ^ 70 +
        2806619779844032953700390431955912022278242599398626075661595475647120) * 10 ^ 70 +
        6821485943918508478208957860502606439402644405119585733422245740137000) * 10 ^ 70 +
        5989419290267414580155255763402077961642021882744245425077452521957605) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (107 - x)) = _
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
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_107_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (108 + x) *
        remainder4Coefficient0.coeff (108 - (108 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 108 + x
  · rw [recurrence4LeadingSquare_coeff_high (108 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (108 - (108 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_108 :
    recurrence4Scalar0Left.coeff 108 =
      ((((64888636197293623194179400160150 * 10 ^ 70 +
        0361405332940038697200285525896327440211717365892964081590851197349794) * 10 ^ 70 +
        8896116488808104924277622362146690217133282059744178114809314052918408) * 10 ^ 70 +
        1534628555378287335896398221800616475103089025752358631742338651776472) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (108 - x)) = _
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
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_108_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (109 + x) *
        remainder4Coefficient0.coeff (109 - (109 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 109 + x
  · rw [recurrence4LeadingSquare_coeff_high (109 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (109 - (109 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_109 :
    recurrence4Scalar0Left.coeff 109 =
      -((((677491727254049457797154536070737 * 10 ^ 70 +
        5764572015648194036935071872540969394396712571019314707303415006913886) * 10 ^ 70 +
        2436573065085164886760122349121257612659779930583607308114937766410416) * 10 ^ 70 +
        4324428336983565751514925943465800453670948010295484741426325698809343) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (109 - x)) = _
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
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_109_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (110 + x) *
        remainder4Coefficient0.coeff (110 - (110 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 110 + x
  · rw [recurrence4LeadingSquare_coeff_high (110 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (110 - (110 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_110 :
    recurrence4Scalar0Left.coeff 110 =
      ((((6886247756142637379368605968014456 * 10 ^ 70 +
        1789872556566126441800893153699543114194484575908800510808524459472940) * 10 ^ 70 +
        4957807168470975020443890216831168333129352272060713812479620094858552) * 10 ^ 70 +
        5640126116643238332509441559599565441616967413555592554297332317447350) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (110 - x)) = _
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
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_110_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (111 + x) *
        remainder4Coefficient0.coeff (111 - (111 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 111 + x
  · rw [recurrence4LeadingSquare_coeff_high (111 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (111 - (111 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_111 :
    recurrence4Scalar0Left.coeff 111 =
      -((((68179974356060145067112651917991212 * 10 ^ 70 +
        0311326774422926020481685540816432441605069100023923153541955358815064) * 10 ^ 70 +
        8501312982621269657171862204259598982798115086854369776547542483329855) * 10 ^ 70 +
        9657353638143753248943069551431117913665657338248897490717844848414825) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (111 - x)) = _
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
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_111_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (112 + x) *
        remainder4Coefficient0.coeff (112 - (112 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 112 + x
  · rw [recurrence4LeadingSquare_coeff_high (112 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (112 - (112 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_112 :
    recurrence4Scalar0Left.coeff 112 =
      ((((657895998352260826275264960870876777 * 10 ^ 70 +
        8230625291278692745650817298585867298371898980984266101751344606417138) * 10 ^ 70 +
        3757091008542331227756906207958770657025090606860713861579277626463541) * 10 ^ 70 +
        5431205519766912060118789434614361755385629312732769740387559373929735) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (112 - x)) = _
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
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_112_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (113 + x) *
        remainder4Coefficient0.coeff (113 - (113 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 113 + x
  · rw [recurrence4LeadingSquare_coeff_high (113 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (113 - (113 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_113 :
    recurrence4Scalar0Left.coeff 113 =
      -((((6190080780075539133652046739755224996 * 10 ^ 70 +
        5358541766075477840171706955383280951355951044351052300646840160976884) * 10 ^ 70 +
        8702826771942192042599605726093886744664464852757950328850336753007391) * 10 ^ 70 +
        0129190594395617567875828609253605836612635713541829687919746491328128) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (113 - x)) = _
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
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_113_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (114 + x) *
        remainder4Coefficient0.coeff (114 - (114 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 114 + x
  · rw [recurrence4LeadingSquare_coeff_high (114 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (114 - (114 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_114 :
    recurrence4Scalar0Left.coeff 114 =
      ((((56816031556860573638995686098177696629 * 10 ^ 70 +
        7732046264339603443734573488159283945915471394446847034797131875220481) * 10 ^ 70 +
        3072652277306571119823816383135013276637911932005839207554375883475179) * 10 ^ 70 +
        2232910304022351527434826446459704523265644233726996504523348763102887) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (114 - x)) = _
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_114_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (115 + x) *
        remainder4Coefficient0.coeff (115 - (115 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 115 + x
  · rw [recurrence4LeadingSquare_coeff_high (115 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (115 - (115 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_115 :
    recurrence4Scalar0Left.coeff 115 =
      -((((508937408278338384276460037887685912900 * 10 ^ 70 +
        2289101240902219947954758654537838279373167657048550430027544941453304) * 10 ^ 70 +
        1180642260577827267703130689196087917178320881755979790082362255090546) * 10 ^ 70 +
        7332074116281751332444594270789963178120959941283718101208040840654972) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (115 - x)) = _
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
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_115_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (116 + x) *
        remainder4Coefficient0.coeff (116 - (116 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 116 + x
  · rw [recurrence4LeadingSquare_coeff_high (116 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (116 - (116 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_116 :
    recurrence4Scalar0Left.coeff 116 =
      ((((4450905982870626392489645287647757598194 * 10 ^ 70 +
        9731050712205768138782620388583925381643450642971914330151052373761463) * 10 ^ 70 +
        2145402992841643279979421273030477029560521211120918751259104728044326) * 10 ^ 70 +
        2169672172637062055228374430302189391343686863569909190624100675051253) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (116 - x)) = _
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
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_116_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (117 + x) *
        remainder4Coefficient0.coeff (117 - (117 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 117 + x
  · rw [recurrence4LeadingSquare_coeff_high (117 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (117 - (117 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_117 :
    recurrence4Scalar0Left.coeff 117 =
      -((((38017575534284951748772830166757768888348 * 10 ^ 70 +
        9144781627310629193477330838720939463725959958240847227468380952697454) * 10 ^ 70 +
        1683510593837223335178288397915591616380920256964795605525263642453489) * 10 ^ 70 +
        0129461455985402829846964318311046924155907149468102213704856828450978) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (117 - x)) = _
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
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_117_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (118 + x) *
        remainder4Coefficient0.coeff (118 - (118 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 118 + x
  · rw [recurrence4LeadingSquare_coeff_high (118 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (118 - (118 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_118 :
    recurrence4Scalar0Left.coeff 118 =
      ((((317266808482271799175914024478997158580677 * 10 ^ 70 +
        2387384777210730886291666841254942407731924854779587688949423869189526) * 10 ^ 70 +
        9380268438188978954386465333694367796758375586921100092236157153495953) * 10 ^ 70 +
        9550110563735188012736412795306574459182202526387299160722396774796981) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (118 - x)) = _
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_118_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (119 + x) *
        remainder4Coefficient0.coeff (119 - (119 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 119 + x
  · rw [recurrence4LeadingSquare_coeff_high (119 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (119 - (119 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_119 :
    recurrence4Scalar0Left.coeff 119 =
      -((((2587695971718547610149028969810437232374413 * 10 ^ 70 +
        1276667031358898827475136195073918291404948334052999037387083128695132) * 10 ^ 70 +
        0713601382049434376763124625311389193607855524825090372945695422577009) * 10 ^ 70 +
        1728865365225240095504081457955692764138573276942062569285378021244397) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (119 - x)) = _
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
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_119_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (120 + x) *
        remainder4Coefficient0.coeff (120 - (120 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 120 + x
  · rw [recurrence4LeadingSquare_coeff_high (120 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (120 - (120 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_120 :
    recurrence4Scalar0Left.coeff 120 =
      ((((20634176003573188128709480168691432135810172 * 10 ^ 70 +
        9339440106208596486740655471603985004100764205880986987074576869442805) * 10 ^ 70 +
        9100121809879202671888102712553990616884639205667864676325899240028796) * 10 ^ 70 +
        2624072178550078724398345542187371903815692736386375095442931081405293) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (120 - x)) = _
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
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_120_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (121 + x) *
        remainder4Coefficient0.coeff (121 - (121 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 121 + x
  · rw [recurrence4LeadingSquare_coeff_high (121 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (121 - (121 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_121 :
    recurrence4Scalar0Left.coeff 121 =
      -((((160907614631005604855774422086839555606086735 * 10 ^ 70 +
        8677450497652159802001075742604834243249003274888092676674475820623380) * 10 ^ 70 +
        3710536958293681500299212661077646631399937701994263859493246645033933) * 10 ^ 70 +
        9657569386412891834770078281106185488065370076173691648103527139170256) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (121 - x)) = _
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
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_121_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (122 + x) *
        remainder4Coefficient0.coeff (122 - (122 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 122 + x
  · rw [recurrence4LeadingSquare_coeff_high (122 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (122 - (122 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_122 :
    recurrence4Scalar0Left.coeff 122 =
      ((((1227456185831557800247809519643692198298386828 * 10 ^ 70 +
        0610002613216335861122778850849458541286368690701675747916823928992212) * 10 ^ 70 +
        0092442322929875890520488885446781438397001943557124891368549581111261) * 10 ^ 70 +
        3121778898543855961034283744876204869250178876617016541588934812470290) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (122 - x)) = _
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
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_122_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (123 + x) *
        remainder4Coefficient0.coeff (123 - (123 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 123 + x
  · rw [recurrence4LeadingSquare_coeff_high (123 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (123 - (123 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_123 :
    recurrence4Scalar0Left.coeff 123 =
      -((((9162083508453453588520119834810048118906942341 * 10 ^ 70 +
        0133641577191825066472176868286888122836348145255630957399167963481040) * 10 ^ 70 +
        2928355248304986676508189239481379528001525863875029446374177786703366) * 10 ^ 70 +
        2904562946431313418040087761381756044174946022179522107015563987933066) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (123 - x)) = _
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
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_123_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (124 + x) *
        remainder4Coefficient0.coeff (124 - (124 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 124 + x
  · rw [recurrence4LeadingSquare_coeff_high (124 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (124 - (124 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_124 :
    recurrence4Scalar0Left.coeff 124 =
      ((((66935306262582220226315271335449995880148631721 * 10 ^ 70 +
        5314478041483016656305334021595608833900723478757899364317474036068589) * 10 ^ 70 +
        7875840694496226392735131982962971096385490134693764733714834307752332) * 10 ^ 70 +
        7912141627083880085643240440621704858634707492237531083479751708180924) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (124 - x)) = _
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
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_124_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (125 + x) *
        remainder4Coefficient0.coeff (125 - (125 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 125 + x
  · rw [recurrence4LeadingSquare_coeff_high (125 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (125 - (125 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_125 :
    recurrence4Scalar0Left.coeff 125 =
      -((((478738487805394099580586421973706307322379454186 * 10 ^ 70 +
        3388446789262803786766795972523057005277619551251771556004447224912134) * 10 ^ 70 +
        4928681337913576612640980001434962194356212640099065837666981417335436) * 10 ^ 70 +
        9446329306397717750744978782755843726058212605183738413814602708633071) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (125 - x)) = _
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
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_125_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (126 + x) *
        remainder4Coefficient0.coeff (126 - (126 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 126 + x
  · rw [recurrence4LeadingSquare_coeff_high (126 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (126 - (126 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_126 :
    recurrence4Scalar0Left.coeff 126 =
      ((((3352961553275085163811999874486749383751948421504 * 10 ^ 70 +
        3846571608485765269774604930597404080436603617794452776621945737734822) * 10 ^ 70 +
        8704665990359791185700033014137004013338990323997393998723229485295672) * 10 ^ 70 +
        1599911030879947834766904936864605464164299627798656939366536628129444) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (126 - x)) = _
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_126_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (127 + x) *
        remainder4Coefficient0.coeff (127 - (127 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 127 + x
  · rw [recurrence4LeadingSquare_coeff_high (127 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (127 - (127 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_127 :
    recurrence4Scalar0Left.coeff 127 =
      -((((23001017636079532241562531518964940196144890182200 * 10 ^ 70 +
        8783733871660109675055410225232494166050118999972161280875849750278754) * 10 ^ 70 +
        3099407399628829295973580247946417733373370812457069162188026081165342) * 10 ^ 70 +
        1709217492261365022611556842833855782391279571888312409824952109443247) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (127 - x)) = _
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_127_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (128 + x) *
        remainder4Coefficient0.coeff (128 - (128 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 128 + x
  · rw [recurrence4LeadingSquare_coeff_high (128 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (128 - (128 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_128 :
    recurrence4Scalar0Left.coeff 128 =
      ((((154579248976738808453411795614315459997734933758154 * 10 ^ 70 +
        9734270124933435668131131431531151585369134978978181266749363461552868) * 10 ^ 70 +
        7807883217914958392838919293263998136965624751048105590772660797599342) * 10 ^ 70 +
        0227796058205782629088780928318474618724884165713360962866600413578687) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (128 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_128_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (129 + x) *
        remainder4Coefficient0.coeff (129 - (129 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 129 + x
  · rw [recurrence4LeadingSquare_coeff_high (129 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (129 - (129 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_129 :
    recurrence4Scalar0Left.coeff 129 =
      -((((1017969963876943359528060907196329826673394879294027 * 10 ^ 70 +
        3063816542049330337663584669703453361545471762558349483609385929203870) * 10 ^ 70 +
        3228889189539486035244158987196004303185331986345673529487428915681892) * 10 ^ 70 +
        0109507071299842539742281950622318586024282470815117320916642127328556) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (129 - x)) = _
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
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_129_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (130 + x) *
        remainder4Coefficient0.coeff (130 - (130 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 130 + x
  · rw [recurrence4LeadingSquare_coeff_high (130 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (130 - (130 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_130 :
    recurrence4Scalar0Left.coeff 130 =
      ((((6570358790066920521306235968785566652714182546128988 * 10 ^ 70 +
        2620826592353684501883791772521113353362816431185752981615942720963182) * 10 ^ 70 +
        2041400359497465384464250112806851730979760093018910779337634692912663) * 10 ^ 70 +
        9295685064525466091223887715065458998919952641046250411940285964418177) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (130 - x)) = _
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
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_130_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (131 + x) *
        remainder4Coefficient0.coeff (131 - (131 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 131 + x
  · rw [recurrence4LeadingSquare_coeff_high (131 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (131 - (131 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_131 :
    recurrence4Scalar0Left.coeff 131 =
      -((((41572029477964387637749998115567568866110137856146609 * 10 ^ 70 +
        7121919950252201019738479951277174234617148622507098613448365689364017) * 10 ^ 70 +
        8373705867326298700230273214704861908066900062625505876030794950399910) * 10 ^ 70 +
        7667322229945143335880129509295305263482394410913360203791727486748985) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (131 - x)) = _
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
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_131_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (132 + x) *
        remainder4Coefficient0.coeff (132 - (132 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 132 + x
  · rw [recurrence4LeadingSquare_coeff_high (132 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (132 - (132 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_132 :
    recurrence4Scalar0Left.coeff 132 =
      ((((257902866199474941776779290542398480243905130356916501 * 10 ^ 70 +
        5030867195356958064473193790399554724080462354708532142676957032209594) * 10 ^ 70 +
        8285075088938082174150946178226978324416653407690039051535542436034211) * 10 ^ 70 +
        3668525520921301738918860463283716240265787534795255291388622587277621) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (132 - x)) = _
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
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_132_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (133 + x) *
        remainder4Coefficient0.coeff (133 - (133 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 133 + x
  · rw [recurrence4LeadingSquare_coeff_high (133 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (133 - (133 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_133 :
    recurrence4Scalar0Left.coeff 133 =
      -((((1569047034907863692883355826180082587393909494977056135 * 10 ^ 70 +
        8270755062364134696426034331659940836209980676357934911103779549682314) * 10 ^ 70 +
        3723988017517356266047398108555036382570881042230570633947530116638528) * 10 ^ 70 +
        9285675977479514589467541636370705124822402607666510800928004980327670) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (133 - x)) = _
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
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_133_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (134 + x) *
        remainder4Coefficient0.coeff (134 - (134 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 134 + x
  · rw [recurrence4LeadingSquare_coeff_high (134 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (134 - (134 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_134 :
    recurrence4Scalar0Left.coeff 134 =
      ((((9363108669755041342023435103893231988594209645781284130 * 10 ^ 70 +
        7149859568160056915094335310091271850039655883521814556983377155849980) * 10 ^ 70 +
        0350096037447818069854600022441969590700525689371455164290465170777499) * 10 ^ 70 +
        1371374342365128821767944469646478524155774741429164298031458169112010) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (134 - x)) = _
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
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_134_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (135 + x) *
        remainder4Coefficient0.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 135 + x
  · rw [recurrence4LeadingSquare_coeff_high (135 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (135 - (135 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_135 :
    recurrence4Scalar0Left.coeff 135 =
      -((((54813238226920978366371500310469547637911993826201015727 * 10 ^ 70 +
        0591227961759512646393321232449099388637535199568604671087023759544852) * 10 ^ 70 +
        3917313303937190941400733515637285162075777725691282349194081468937146) * 10 ^ 70 +
        7298600109393621874059875234530574492748925016586257636829928437681441) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (135 - x)) = _
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
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_135_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (136 + x) *
        remainder4Coefficient0.coeff (136 - (136 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 136 + x
  · rw [recurrence4LeadingSquare_coeff_high (136 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (136 - (136 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_136 :
    recurrence4Scalar0Left.coeff 136 =
      ((((314852236662517487607346837466039904980770564795600033044 * 10 ^ 70 +
        3734052811969507995664359964799930083379511236042648293496212916499278) * 10 ^ 70 +
        5682153709397262389934186717040088426083920417558234009402462480913685) * 10 ^ 70 +
        3294789636317614630399407398922952380470758651219439575662260488441021) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (136 - x)) = _
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
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_136_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (137 + x) *
        remainder4Coefficient0.coeff (137 - (137 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 137 + x
  · rw [recurrence4LeadingSquare_coeff_high (137 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (137 - (137 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_137 :
    recurrence4Scalar0Left.coeff 137 =
      -((((1774828587855102458767742643329368122991414759590751484108 * 10 ^ 70 +
        9422360065784288867284082719387794062688924880997642151122745056650646) * 10 ^ 70 +
        4089270371782359349059966236107192345369305637988357089633462655622390) * 10 ^ 70 +
        0071631917011182380953586299550913636421126399002770403319205597224351) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (137 - x)) = _
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
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_137_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (138 + x) *
        remainder4Coefficient0.coeff (138 - (138 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 138 + x
  · rw [recurrence4LeadingSquare_coeff_high (138 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (138 - (138 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_138 :
    recurrence4Scalar0Left.coeff 138 =
      ((((9819843956687692115889527163890247349745691934017736918978 * 10 ^ 70 +
        4760812694346963166541411946880387206939998048461782133446500587813564) * 10 ^ 70 +
        5761399348466204507441512997542696937291238400772086832451402731952939) * 10 ^ 70 +
        2862628377434434448086616322206323374678740269933528561918546939216127) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (138 - x)) = _
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
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_138_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (139 + x) *
        remainder4Coefficient0.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 139 + x
  · rw [recurrence4LeadingSquare_coeff_high (139 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (139 - (139 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_139 :
    recurrence4Scalar0Left.coeff 139 =
      -((((53335879374996119925864622382308309493976724913891356963546 * 10 ^ 70 +
        6653788699261969764063143489688777323021701508229886835813617633316807) * 10 ^ 70 +
        9035212813761588591599111558223744040469243602664676076712994161463020) * 10 ^ 70 +
        7544905028392763604509407370539756781109891553794443237244598199926763) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (139 - x)) = _
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
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (140 + x) *
        remainder4Coefficient0.coeff (140 - (140 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 140 + x
  · rw [recurrence4LeadingSquare_coeff_high (140 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (140 - (140 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_140 :
    recurrence4Scalar0Left.coeff 140 =
      ((((284424638765686293322647915478476865728361456755457151057873 * 10 ^ 70 +
        4683899469389285357105382238793130818374463209827032430563341300362682) * 10 ^ 70 +
        5111647368524003168913876241498037053390997463803748755104088661213139) * 10 ^ 70 +
        8665747133713239938486729950478991955013017325180079292630374437944778) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (140 - x)) = _
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
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (141 + x) *
        remainder4Coefficient0.coeff (141 - (141 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 141 + x
  · rw [recurrence4LeadingSquare_coeff_high (141 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (141 - (141 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_141 :
    recurrence4Scalar0Left.coeff 141 =
      -((((1489402657388471955435736378235877503296316322883820716301287 * 10 ^ 70 +
        6388589230655832945373237922004642712577885333538684689317186661426953) * 10 ^ 70 +
        0850333814622282464112398893520460526003030440283134699069260049570449) * 10 ^ 70 +
        7251237335113278845937356875367013125129381285805955911884089159826688) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (141 - x)) = _
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
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (142 + x) *
        remainder4Coefficient0.coeff (142 - (142 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 142 + x
  · rw [recurrence4LeadingSquare_coeff_high (142 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (142 - (142 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_142 :
    recurrence4Scalar0Left.coeff 142 =
      ((((7659785741176226916561718361967380823684930039315230462890261 * 10 ^ 70 +
        6515522634230965497678799038121543979331771677529530470611990529883715) * 10 ^ 70 +
        6954221339234285301503209695545693497595854277519181832762768937899853) * 10 ^ 70 +
        9442725414936002643680944250045228883535472208180814105890478041728415) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (142 - x)) = _
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
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (143 + x) *
        remainder4Coefficient0.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 143 + x
  · rw [recurrence4LeadingSquare_coeff_high (143 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (143 - (143 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_143 :
    recurrence4Scalar0Left.coeff 143 =
      -((((38693798829747665190436217149697812987811190721458826500379461 * 10 ^ 70 +
        3183841075742266135663553021115044417830747856684165852327270089676031) * 10 ^ 70 +
        5391996504013769777381155947800982981348718014687789336228889232302904) * 10 ^ 70 +
        9605747636809278167928265713235243624303780963963606007470472151092887) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (143 - x)) = _
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
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (144 + x) *
        remainder4Coefficient0.coeff (144 - (144 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 144 + x
  · rw [recurrence4LeadingSquare_coeff_high (144 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (144 - (144 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_144 :
    recurrence4Scalar0Left.coeff 144 =
      ((((192019492904576894289356233721258317874061637421476706510340472 * 10 ^ 70 +
        8417522986839700581914836963259506693621445349786179398107583746283374) * 10 ^ 70 +
        1716534776689889539272488305377590853264085683731567010499050550394489) * 10 ^ 70 +
        0964940668754285389463878540363343069743379216252884177915950477238327) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (144 - x)) = _
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
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (145 + x) *
        remainder4Coefficient0.coeff (145 - (145 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 145 + x
  · rw [recurrence4LeadingSquare_coeff_high (145 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (145 - (145 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_145 :
    recurrence4Scalar0Left.coeff 145 =
      -((((936236926388480854792375401580633880051517588247668518209460513 * 10 ^ 70 +
        2999061431401286632570801037877133707905039148690101406046513890513356) * 10 ^ 70 +
        3285054437949147079858793178024309140794340882771222154574654828230621) * 10 ^ 70 +
        1604934841841981941506972589545604777804131035837747038036696304748356) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (145 - x)) = _
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
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (146 + x) *
        remainder4Coefficient0.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 146 + x
  · rw [recurrence4LeadingSquare_coeff_high (146 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (146 - (146 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_146 :
    recurrence4Scalar0Left.coeff 146 =
      ((((4485577972379420835801572335315351578026724776009342825917937750 * 10 ^ 70 +
        5619365594404735280023191742191771878720792187851089982172242252673108) * 10 ^ 70 +
        5184579065639229889457694283797013006936660134603859826977057919280114) * 10 ^ 70 +
        3218598652849718934422860933932058354960089329105351446323791803439856) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (146 - x)) = _
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (147 + x) *
        remainder4Coefficient0.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 147 + x
  · rw [recurrence4LeadingSquare_coeff_high (147 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (147 - (147 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_147 :
    recurrence4Scalar0Left.coeff 147 =
      -((((21120169488760465233919412178322864614086614226699831601809893220 * 10 ^ 70 +
        0278618392134642712164291281913191302904913972178049223090007694354158) * 10 ^ 70 +
        8476145374966580970798081748880413382853610732908158065143240945604026) * 10 ^ 70 +
        8538953107293324870134921174569364147075682326563690799644417027357685) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (147 - x)) = _
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
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (148 + x) *
        remainder4Coefficient0.coeff (148 - (148 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 148 + x
  · rw [recurrence4LeadingSquare_coeff_high (148 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (148 - (148 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_148 :
    recurrence4Scalar0Left.coeff 148 =
      ((((97740685178183524378606310698234792308129674027585511632420848121 * 10 ^ 70 +
        7628904442361559000481696971875006687781158997739690903092332572567290) * 10 ^ 70 +
        4467749888704752448788118209660995586939092626549506993469143141782248) * 10 ^ 70 +
        0502512675601602026475194478664618620520175654553869333147133499288052) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (148 - x)) = _
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
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (149 + x) *
        remainder4Coefficient0.coeff (149 - (149 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 149 + x
  · rw [recurrence4LeadingSquare_coeff_high (149 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (149 - (149 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_149 :
    recurrence4Scalar0Left.coeff 149 =
      -((((444634892980022301699122871396247723915559208061136704925912859122 * 10 ^ 70 +
        0692974433383668854031522257916740416877492378089610191843498422590116) * 10 ^ 70 +
        2954662522305738812754045738155777027231314947201711606228825312856546) * 10 ^ 70 +
        2400350489262217322007837162380437644222014008864375460621771981202832) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (149 - x)) = _
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
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (150 + x) *
        remainder4Coefficient0.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 150 + x
  · rw [recurrence4LeadingSquare_coeff_high (150 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (150 - (150 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_150 :
    recurrence4Scalar0Left.coeff 150 =
      ((((1988527778617387588674114467152183438506925146787772200698306227688 * 10 ^ 70 +
        0444101230087621713466334544785802408019496311150192453297576271496688) * 10 ^ 70 +
        9050830784549249454316162869090727322892493069468125144359513926029463) * 10 ^ 70 +
        8276805080276969612016879256287177273674719750214793648286146039973075) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (150 - x)) = _
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (151 + x) *
        remainder4Coefficient0.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 151 + x
  · rw [recurrence4LeadingSquare_coeff_high (151 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (151 - (151 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_151 :
    recurrence4Scalar0Left.coeff 151 =
      -((((8743959680853543042953601185860347823630101337245274836119481313270 * 10 ^ 70 +
        5122526772476742141535339576447958503595721164568831053546292599289676) * 10 ^ 70 +
        4072603492313934184032262380688097124766346938044415697218741312269933) * 10 ^ 70 +
        9835462131847635835524809990538562807180193351856538368666195936347856) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (151 - x)) = _
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
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (152 + x) *
        remainder4Coefficient0.coeff (152 - (152 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 152 + x
  · rw [recurrence4LeadingSquare_coeff_high (152 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (152 - (152 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_152 :
    recurrence4Scalar0Left.coeff 152 =
      ((((37807683064189673497141684931776192509832807739970325278366810493870 * 10 ^ 70 +
        9286713500666181075816694117291203330785588324867915515887225234295071) * 10 ^ 70 +
        8119127583689919625568778317175330103262134342554985762760495446464118) * 10 ^ 70 +
        1373498754710036332318573720496963387082168797328345662418498685308994) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (152 - x)) = _
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
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (153 + x) *
        remainder4Coefficient0.coeff (153 - (153 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 153 + x
  · rw [recurrence4LeadingSquare_coeff_high (153 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (153 - (153 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_153 :
    recurrence4Scalar0Left.coeff 153 =
      -((((160765622592281569280805023635264586481975722415702869228033669279006 * 10 ^ 70 +
        6622889220897107516422458025385488105224087911738627046483835791423694) * 10 ^ 70 +
        3406253318649183774353503704555741748079224942317195864253746005628325) * 10 ^ 70 +
        9226684269991089205148599991324901980988381422799480116199973330619611) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (153 - x)) = _
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
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (154 + x) *
        remainder4Coefficient0.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 154 + x
  · rw [recurrence4LeadingSquare_coeff_high (154 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (154 - (154 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_154 :
    recurrence4Scalar0Left.coeff 154 =
      ((((672344762185203307934492202805093163158816844998301622178591088557359 * 10 ^ 70 +
        4020069396652838138999285285213276293878983655399160181889782426088206) * 10 ^ 70 +
        8317346116613439609384269963528451735935664880833692800835037496144805) * 10 ^ 70 +
        6001584685423772289209143194898407872234839590569587547216915339246718) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (154 - x)) = _
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
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (155 + x) *
        remainder4Coefficient0.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 155 + x
  · rw [recurrence4LeadingSquare_coeff_high (155 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (155 - (155 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_155 :
    recurrence4Scalar0Left.coeff 155 =
      -((((2765794208874419492220867157547259939267410007696629330242299960219987 * 10 ^ 70 +
        8859780127275249308815700602969994017031514451471210837372313940660646) * 10 ^ 70 +
        7488237494054083765386632967656880880331526701371941963171520306068076) * 10 ^ 70 +
        8438607989848311020767949256692628137593059215448478688822098467622386) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (155 - x)) = _
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
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (156 + x) *
        remainder4Coefficient0.coeff (156 - (156 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 156 + x
  · rw [recurrence4LeadingSquare_coeff_high (156 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (156 - (156 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_156 :
    recurrence4Scalar0Left.coeff 156 =
      (((((1 * 10 ^ 70 +
        1192285582873756997726626964787282559789111066080978242054640379400767) * 10 ^ 70 +
        9545232182157526158560239880684494900211671475843385954870712015694203) * 10 ^ 70 +
        1151023030196431672348576325513284395609247120097755719973278148261718) * 10 ^ 70 +
        0231624990486254274401083133824074624812241228096076889372032728456695) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (156 - x)) = _
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
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (157 + x) *
        remainder4Coefficient0.coeff (157 - (157 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 157 + x
  · rw [recurrence4LeadingSquare_coeff_high (157 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (157 - (157 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_157 :
    recurrence4Scalar0Left.coeff 157 =
      -(((((4 * 10 ^ 70 +
        4558412120649568780362792321583885805074663980878399182056177861832161) * 10 ^ 70 +
        6093140880687732762345394038201587529362884042903816095691887494338028) * 10 ^ 70 +
        8816734001394562430712162369249767953082732202425268440972946438208471) * 10 ^ 70 +
        0439922482501746490951837720605490011743350583425615191865881860912384) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (157 - x)) = _
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
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (158 + x) *
        remainder4Coefficient0.coeff (158 - (158 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 158 + x
  · rw [recurrence4LeadingSquare_coeff_high (158 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (158 - (158 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_158 :
    recurrence4Scalar0Left.coeff 158 =
      (((((17 * 10 ^ 70 +
        4538972517567483494176437163030230788871912630314425600996914784081361) * 10 ^ 70 +
        7599564538406672426492508881107370280151091460234051929224432924765372) * 10 ^ 70 +
        0084485031533966693387886907433967470610787388974440183365414184766659) * 10 ^ 70 +
        4932855805401018322804331617208783819594157678504186851866477352979268) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (158 - x)) = _
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (159 + x) *
        remainder4Coefficient0.coeff (159 - (159 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 159 + x
  · rw [recurrence4LeadingSquare_coeff_high (159 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (159 - (159 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_159 :
    recurrence4Scalar0Left.coeff 159 =
      -(((((67 * 10 ^ 70 +
        2737421102361317117194509294778915557852410075869162913422785555908411) * 10 ^ 70 +
        3341834745306938229130535674643912978099605700153837276772316043491221) * 10 ^ 70 +
        1226818025193379947270967044423747893784521042485734465701251252777777) * 10 ^ 70 +
        4602212172299243784977948703619764635628730401857772020161135357704032) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (159 - x)) = _
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (160 + x) *
        remainder4Coefficient0.coeff (160 - (160 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 160 + x
  · rw [recurrence4LeadingSquare_coeff_high (160 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (160 - (160 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_160 :
    recurrence4Scalar0Left.coeff 160 =
      (((((255 * 10 ^ 70 +
        1683553143240329775647795827119712559273972459464307349703318464068043) * 10 ^ 70 +
        2644146650440872156318240952154154949051175906353963805143452377089475) * 10 ^ 70 +
        5553469076193667550508205527175618256028733156970027259447613644284191) * 10 ^ 70 +
        9271156323805852086403625215216150781974587468111953120985644266051413) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (160 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (161 + x) *
        remainder4Coefficient0.coeff (161 - (161 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 161 + x
  · rw [recurrence4LeadingSquare_coeff_high (161 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (161 - (161 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_161 :
    recurrence4Scalar0Left.coeff 161 =
      -(((((952 * 10 ^ 70 +
        5167933876858770961754830199150845961428535582726197312310707099411109) * 10 ^ 70 +
        2633262664940719238363592031786603753344853818593180649857777050845494) * 10 ^ 70 +
        3023577925726305236885261092360344001208294509523802649891872001036296) * 10 ^ 70 +
        1048355215850873981512060544498376473507012768383993172118189969474301) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (161 - x)) = _
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
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (162 + x) *
        remainder4Coefficient0.coeff (162 - (162 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 162 + x
  · rw [recurrence4LeadingSquare_coeff_high (162 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (162 - (162 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_162 :
    recurrence4Scalar0Left.coeff 162 =
      (((((3499 * 10 ^ 70 +
        6013787481189289166633245890829536901422818967359721710162942277948776) * 10 ^ 70 +
        1380399420474739099491381763394908771484577674528968109627628001730437) * 10 ^ 70 +
        7348036099103673754596893137896023054018530328792688778264250898420374) * 10 ^ 70 +
        6812044780854591228949355402554755850704611875607838234064996393717101) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (162 - x)) = _
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
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
