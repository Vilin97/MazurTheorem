/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
