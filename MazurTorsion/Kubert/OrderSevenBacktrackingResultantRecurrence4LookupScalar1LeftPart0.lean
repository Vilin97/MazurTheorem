/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_1
  recurrence4A1_coeff_10
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_11
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_12
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_13
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_14
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_15
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156

attribute [local simp]
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_16
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_17
  recurrence4A1_coeff_18
  recurrence4A1_coeff_19
  recurrence4A1_coeff_2
  recurrence4A1_coeff_20
  recurrence4A1_coeff_21
  recurrence4A1_coeff_22
  recurrence4A1_coeff_23
  recurrence4A1_coeff_24
  recurrence4A1_coeff_25
  recurrence4A1_coeff_26
  recurrence4A1_coeff_27
  recurrence4A1_coeff_28
  recurrence4A1_coeff_29
  recurrence4A1_coeff_3
  recurrence4A1_coeff_30
  recurrence4A1_coeff_31
  recurrence4A1_coeff_32
  recurrence4A1_coeff_33
  recurrence4A1_coeff_34
  recurrence4A1_coeff_35
  recurrence4A1_coeff_36
  recurrence4A1_coeff_37
  recurrence4A1_coeff_38
  recurrence4A1_coeff_39
  recurrence4A1_coeff_4
  recurrence4A1_coeff_40
  recurrence4A1_coeff_41
  recurrence4A1_coeff_42
  recurrence4A1_coeff_43
  recurrence4A1_coeff_44
  recurrence4A1_coeff_45
  recurrence4A1_coeff_46
  recurrence4A1_coeff_47
  recurrence4A1_coeff_48
  recurrence4A1_coeff_49
  recurrence4A1_coeff_5
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_6
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68

attribute [local simp]
  recurrence4A1_coeff_69
  recurrence4A1_coeff_7
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_8
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_9
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
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

private theorem recurrence4Scalar1Left_coeff_0_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (x) *
        remainder4Coefficient1.coeff (0 - (x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < x
  · rw [recurrence4LeadingSquare_coeff_high (x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (0 - (x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_0 :
    recurrence4Scalar1Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_0_suffix_zero]

private theorem recurrence4Scalar1Left_coeff_1_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (1 + x) *
        remainder4Coefficient1.coeff (1 - (1 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 1 + x
  · rw [recurrence4LeadingSquare_coeff_high (1 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (1 - (1 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_1 :
    recurrence4Scalar1Left.coeff 1 =
      (-99315933117299314134403723541286627756220416 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_1_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_2_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (2 + x) *
        remainder4Coefficient1.coeff (2 - (2 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 2 + x
  · rw [recurrence4LeadingSquare_coeff_high (2 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (2 - (2 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_2 :
    recurrence4Scalar1Left.coeff 2 =
      (733478399094153464288561736022755528725209251840 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_2_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_3_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (3 + x) *
        remainder4Coefficient1.coeff (3 - (3 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 3 + x
  · rw [recurrence4LeadingSquare_coeff_high (3 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (3 - (3 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_3 :
    recurrence4Scalar1Left.coeff 3 =
      (-1498265309169662814642809029245769854881970893526528 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_3_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_4_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (4 + x) *
        remainder4Coefficient1.coeff (4 - (4 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 4 + x
  · rw [recurrence4LeadingSquare_coeff_high (4 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (4 - (4 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_4 :
    recurrence4Scalar1Left.coeff 4 =
      (-753815074531733876920528261656772787411932682339518464 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_4_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_5_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (5 + x) *
        remainder4Coefficient1.coeff (5 - (5 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 5 + x
  · rw [recurrence4LeadingSquare_coeff_high (5 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (5 - (5 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_5 :
    recurrence4Scalar1Left.coeff 5 =
      (8515727816507089124145629256063472034584041436965337427808 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_5_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_6_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (6 + x) *
        remainder4Coefficient1.coeff (6 - (6 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 6 + x
  · rw [recurrence4LeadingSquare_coeff_high (6 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (6 - (6 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_6 :
    recurrence4Scalar1Left.coeff 6 =
      (-16784324902503465892903450520340026793206451037199474341745328 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_6_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_7_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (7 + x) *
        remainder4Coefficient1.coeff (7 - (7 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 7 + x
  · rw [recurrence4LeadingSquare_coeff_high (7 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (7 - (7 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_7 :
    recurrence4Scalar1Left.coeff 7 =
      (17452452303134609742725667282368232718837598035417312767803431440 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_7_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_8_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (8 + x) *
        remainder4Coefficient1.coeff (8 - (8 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 8 + x
  · rw [recurrence4LeadingSquare_coeff_high (8 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (8 - (8 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_8 :
    recurrence4Scalar1Left.coeff 8 =
      (-11092363346271294338983144153628813438350300602420714447124101089052 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_8_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_9_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (9 + x) *
        remainder4Coefficient1.coeff (9 - (9 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 9 + x
  · rw [recurrence4LeadingSquare_coeff_high (9 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (9 - (9 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_9 :
    recurrence4Scalar1Left.coeff 9 =
      (5007472240346861592806715407473327833885531584382254591860017598926248 : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_9_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_10_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (10 + x) *
        remainder4Coefficient1.coeff (10 - (10 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 10 + x
  · rw [recurrence4LeadingSquare_coeff_high (10 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (10 - (10 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_10 :
    recurrence4Scalar1Left.coeff 10 =
      -((218 * 10 ^ 70 +
        1950586782191303261305479848480916699471710730223417122123031698509208) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_10_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_11_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (11 + x) *
        remainder4Coefficient1.coeff (11 - (11 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 11 + x
  · rw [recurrence4LeadingSquare_coeff_high (11 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (11 - (11 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_11 :
    recurrence4Scalar1Left.coeff 11 =
      ((92627 * 10 ^ 70 +
        3046242656670227312552367090840187009906912575965939252470839523343300) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_11_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_12_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (12 + x) *
        remainder4Coefficient1.coeff (12 - (12 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 12 + x
  · rw [recurrence4LeadingSquare_coeff_high (12 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (12 - (12 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_12 :
    recurrence4Scalar1Left.coeff 12 =
      -((20946035 * 10 ^ 70 +
        3205036313978438054484114138136796522942799807113920143169940847682748) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_12_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_13_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (13 + x) *
        remainder4Coefficient1.coeff (13 - (13 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 13 + x
  · rw [recurrence4LeadingSquare_coeff_high (13 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (13 - (13 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_13 :
    recurrence4Scalar1Left.coeff 13 =
      -((6465549589 * 10 ^ 70 +
        4972365266738326457785023301598908396458894887131539891860586258567852) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_13_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_14_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (14 + x) *
        remainder4Coefficient1.coeff (14 - (14 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 14 + x
  · rw [recurrence4LeadingSquare_coeff_high (14 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (14 - (14 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_14 :
    recurrence4Scalar1Left.coeff 14 =
      ((7969456870458 * 10 ^ 70 +
        5432808864849330025725042880114869528564104716352435737631577229694948) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_14_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_15_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (15 + x) *
        remainder4Coefficient1.coeff (15 - (15 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 15 + x
  · rw [recurrence4LeadingSquare_coeff_high (15 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (15 - (15 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_15 :
    recurrence4Scalar1Left.coeff 15 =
      -((4069853363068965 * 10 ^ 70 +
        0498206078930994780633838862243877439284804958336784066203440812409056) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_15_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_16_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (16 + x) *
        remainder4Coefficient1.coeff (16 - (16 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 16 + x
  · rw [recurrence4LeadingSquare_coeff_high (16 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (16 - (16 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_16 :
    recurrence4Scalar1Left.coeff 16 =
      ((1675027463587444949 * 10 ^ 70 +
        9291062629028271432071332178670070640153244427576712151067063036137260) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_16_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_17_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (17 + x) *
        remainder4Coefficient1.coeff (17 - (17 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 17 + x
  · rw [recurrence4LeadingSquare_coeff_high (17 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (17 - (17 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_17 :
    recurrence4Scalar1Left.coeff 17 =
      -((629172661599693645957 * 10 ^ 70 +
        9565317195665560982696212105898832086226612984352690409406545748497464) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_17_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_18_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (18 + x) *
        remainder4Coefficient1.coeff (18 - (18 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 18 + x
  · rw [recurrence4LeadingSquare_coeff_high (18 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (18 - (18 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_18 :
    recurrence4Scalar1Left.coeff 18 =
      ((177467237012452387685301 * 10 ^ 70 +
        9808960915946791564902535217270854490046057474514052239408703123819557) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_18_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_19_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (19 + x) *
        remainder4Coefficient1.coeff (19 - (19 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 19 + x
  · rw [recurrence4LeadingSquare_coeff_high (19 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (19 - (19 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_19 :
    recurrence4Scalar1Left.coeff 19 =
      -((14705129426543327020089251 * 10 ^ 70 +
        7539033886093657919814384732516975022779496247462294740250062290125766) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_19_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_20_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (20 + x) *
        remainder4Coefficient1.coeff (20 - (20 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 20 + x
  · rw [recurrence4LeadingSquare_coeff_high (20 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (20 - (20 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_20 :
    recurrence4Scalar1Left.coeff 20 =
      -((16709842783333280897830127284 * 10 ^ 70 +
        9840731317765515853802927055833734466175720397617859053191005942165000) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_20_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_21_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (21 + x) *
        remainder4Coefficient1.coeff (21 - (21 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 21 + x
  · rw [recurrence4LeadingSquare_coeff_high (21 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (21 - (21 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_21 :
    recurrence4Scalar1Left.coeff 21 =
      ((10992260451616636513145676131225 * 10 ^ 70 +
        6877199433317576896733918155383310855448127797387712726547744103878759) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_21_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_22_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (22 + x) *
        remainder4Coefficient1.coeff (22 - (22 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 22 + x
  · rw [recurrence4LeadingSquare_coeff_high (22 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (22 - (22 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_22 :
    recurrence4Scalar1Left.coeff 22 =
      -((3955411624033755179348072452215922 * 10 ^ 70 +
        2127966492195027564280330625058516528220818151267301715538059298106368) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_22_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_23_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (23 + x) *
        remainder4Coefficient1.coeff (23 - (23 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 23 + x
  · rw [recurrence4LeadingSquare_coeff_high (23 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (23 - (23 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_23 :
    recurrence4Scalar1Left.coeff 23 =
      ((985830500568056944420134865475079135 * 10 ^ 70 +
        2484002289182763773394479827598310344072758897183841471635407084663408) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_23_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_24_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (24 + x) *
        remainder4Coefficient1.coeff (24 - (24 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 24 + x
  · rw [recurrence4LeadingSquare_coeff_high (24 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (24 - (24 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_24 :
    recurrence4Scalar1Left.coeff 24 =
      -((173194276210504783118178109210883219967 * 10 ^ 70 +
        5971025799695322573401981438206996473678713565593302332067933611009326) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_24_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_25_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (25 + x) *
        remainder4Coefficient1.coeff (25 - (25 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 25 + x
  · rw [recurrence4LeadingSquare_coeff_high (25 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (25 - (25 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_25 :
    recurrence4Scalar1Left.coeff 25 =
      ((17167362548421172705139828814289278610927 * 10 ^ 70 +
        1469845955212189787664833072658393179577582413234752574554992772966886) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_25_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_26_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (26 + x) *
        remainder4Coefficient1.coeff (26 - (26 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 26 + x
  · rw [recurrence4LeadingSquare_coeff_high (26 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (26 - (26 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_26 :
    recurrence4Scalar1Left.coeff 26 =
      ((1666521741794707344392985996496435930890514 * 10 ^ 70 +
        3492907017598397559301086280750328542452638865409192556080368549037006) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_26_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_27_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (27 + x) *
        remainder4Coefficient1.coeff (27 - (27 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 27 + x
  · rw [recurrence4LeadingSquare_coeff_high (27 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (27 - (27 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_27 :
    recurrence4Scalar1Left.coeff 27 =
      -((1493838530461415026912767500722914411136644117 * 10 ^ 70 +
        1222069756626056249339378349452634368093989826952550371122536817334212) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_27_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_28_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (28 + x) *
        remainder4Coefficient1.coeff (28 - (28 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 28 + x
  · rw [recurrence4LeadingSquare_coeff_high (28 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (28 - (28 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_28 :
    recurrence4Scalar1Left.coeff 28 =
      ((540742949586439889367849200559674015178865630926 * 10 ^ 70 +
        3330815758271553538868721218720122177029257181460505302741129031715050) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_28_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_29_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (29 + x) *
        remainder4Coefficient1.coeff (29 - (29 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 29 + x
  · rw [recurrence4LeadingSquare_coeff_high (29 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (29 - (29 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_29 :
    recurrence4Scalar1Left.coeff 29 =
      -((154714906603283044196475614625334388989303423061677 * 10 ^ 70 +
        2919835359488490127393336822996908203946388061306578767778256839986404) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_29_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_30_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (30 + x) *
        remainder4Coefficient1.coeff (30 - (30 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 30 + x
  · rw [recurrence4LeadingSquare_coeff_high (30 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (30 - (30 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_30 :
    recurrence4Scalar1Left.coeff 30 =
      ((38279842410806734520404944715281743126624833214280536 * 10 ^ 70 +
        3641733455765872660128854431118078295564350514790482455809517297404234) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_30_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_31_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (31 + x) *
        remainder4Coefficient1.coeff (31 - (31 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 31 + x
  · rw [recurrence4LeadingSquare_coeff_high (31 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (31 - (31 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_31 :
    recurrence4Scalar1Left.coeff 31 =
      -((8313500566436207906980073230737730148820438205970285128 * 10 ^ 70 +
        7103739708128782398803416060536674517644459055965568496405943041127982) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_31_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_32_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (32 + x) *
        remainder4Coefficient1.coeff (32 - (32 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 32 + x
  · rw [recurrence4LeadingSquare_coeff_high (32 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (32 - (32 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_32 :
    recurrence4Scalar1Left.coeff 32 =
      ((1583281894841204524512588254683629929442909339445844114376 * 10 ^ 70 +
        3957593169130929874466564563484990795521287493518435926324614698997352) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Left_coeff_32_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_33_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (33 + x) *
        remainder4Coefficient1.coeff (33 - (33 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 33 + x
  · rw [recurrence4LeadingSquare_coeff_high (33 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (33 - (33 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_33 :
    recurrence4Scalar1Left.coeff 33 =
      -((263165464511140530947177917167356333231897235381288664689580 * 10 ^ 70 +
        5099462856969823874535845717672956971459983423680393004038682929834377) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (33 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_33_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_34_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (34 + x) *
        remainder4Coefficient1.coeff (34 - (34 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 34 + x
  · rw [recurrence4LeadingSquare_coeff_high (34 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (34 - (34 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_34 :
    recurrence4Scalar1Left.coeff 34 =
      ((37830812628647212455436772592675696145850601734906414147522102 * 10 ^ 70 +
        1813436261986104203036108425382420487577375009202865670707421830335136) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (34 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_34_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_35_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (35 + x) *
        remainder4Coefficient1.coeff (35 - (35 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 35 + x
  · rw [recurrence4LeadingSquare_coeff_high (35 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (35 - (35 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_35 :
    recurrence4Scalar1Left.coeff 35 =
      -((4610273168351078482982374856854549770872881554269593852180628407 * 10 ^ 70 +
        6942353006240364226086415778824153200709240831298862861909863875870908) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (35 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_35_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_36_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (36 + x) *
        remainder4Coefficient1.coeff (36 - (36 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 36 + x
  · rw [recurrence4LeadingSquare_coeff_high (36 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (36 - (36 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_36 :
    recurrence4Scalar1Left.coeff 36 =
      ((452983993227737748731170738442723748081132658592020189736231179882 * 10 ^ 70 +
        0588724266403483041382874424061558094057790461782534598165047179807993) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (36 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_36_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_37_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (37 + x) *
        remainder4Coefficient1.coeff (37 - (37 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 37 + x
  · rw [recurrence4LeadingSquare_coeff_high (37 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (37 - (37 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_37 :
    recurrence4Scalar1Left.coeff 37 =
      -((30307912086844440078394090078971534368149492903178979281698358285923 * 10 ^ 70 +
        9593478463845892780573147013006270899750399091971859818927173903946004) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (37 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_37_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_38_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (38 + x) *
        remainder4Coefficient1.coeff (38 - (38 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 38 + x
  · rw [recurrence4LeadingSquare_coeff_high (38 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (38 - (38 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_38 :
    recurrence4Scalar1Left.coeff 38 =
      -((21800842576280918363133335347365236331568191856252751784453210520362 * 10 ^ 70 +
        6884657859565740672560316142691098407264989294604361100450762054727461) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (38 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_38_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_39_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (39 + x) *
        remainder4Coefficient1.coeff (39 - (39 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 39 + x
  · rw [recurrence4LeadingSquare_coeff_high (39 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (39 - (39 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_39 :
    recurrence4Scalar1Left.coeff 39 =
      (((41 * 10 ^ 70 +
        7189623283299405956587290229637541136991224504239021697389851155052880) * 10 ^ 70 +
        8216985231481152095416515535402943502166084902646896584413846114338391) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (39 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_39_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_40_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (40 + x) *
        remainder4Coefficient1.coeff (40 - (40 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 40 + x
  · rw [recurrence4LeadingSquare_coeff_high (40 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (40 - (40 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_40 :
    recurrence4Scalar1Left.coeff 40 =
      -(((8407 * 10 ^ 70 +
        7014442074565049838349904743160421503967820551317042942288937986118340) * 10 ^ 70 +
        4197816159802119225892267286704384893273592313828850238187933700509043) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (40 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_40_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_41_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (41 + x) *
        remainder4Coefficient1.coeff (41 - (41 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 41 + x
  · rw [recurrence4LeadingSquare_coeff_high (41 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (41 - (41 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_41 :
    recurrence4Scalar1Left.coeff 41 =
      (((1148846 * 10 ^ 70 +
        1626572250667005079425759856297232727257996451614468228865094920222026) * 10 ^ 70 +
        3792495794554404785681662751583174858064112866812140091935480513022931) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (41 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_41_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_42_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (42 + x) *
        remainder4Coefficient1.coeff (42 - (42 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 42 + x
  · rw [recurrence4LeadingSquare_coeff_high (42 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (42 - (42 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_42 :
    recurrence4Scalar1Left.coeff 42 =
      -(((124308326 * 10 ^ 70 +
        3221735196797081044441833709157382764775843958464065854995075992914235) * 10 ^ 70 +
        0010252046830046343361212501601916422917948223909433562945445174033837) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (42 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_42_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_43_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (43 + x) *
        remainder4Coefficient1.coeff (43 - (43 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 43 + x
  · rw [recurrence4LeadingSquare_coeff_high (43 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (43 - (43 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_43 :
    recurrence4Scalar1Left.coeff 43 =
      (((10913350609 * 10 ^ 70 +
        3225905214195092533048606518572526601835524101804677867375848131920922) * 10 ^ 70 +
        2969121297382274173820844489849694431048179651609709824595325739709436) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (43 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_43_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_44_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (44 + x) *
        remainder4Coefficient1.coeff (44 - (44 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 44 + x
  · rw [recurrence4LeadingSquare_coeff_high (44 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (44 - (44 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_44 :
    recurrence4Scalar1Left.coeff 44 =
      -(((739332237013 * 10 ^ 70 +
        7504607518401542299917024329655125842142354044791876901123928470328442) * 10 ^ 70 +
        8075615207926955139669317154830048393559817964842013129583655107410632) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (44 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_44_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_45_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (45 + x) *
        remainder4Coefficient1.coeff (45 - (45 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 45 + x
  · rw [recurrence4LeadingSquare_coeff_high (45 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (45 - (45 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_45 :
    recurrence4Scalar1Left.coeff 45 =
      (((28902952590510 * 10 ^ 70 +
        5214474693553824868924779110769165782742141414723386825438643958872162) * 10 ^ 70 +
        0772477451838890395178278622616462989142547151883703274294522444572154) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (45 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_45_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_46_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (46 + x) *
        remainder4Coefficient1.coeff (46 - (46 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 46 + x
  · rw [recurrence4LeadingSquare_coeff_high (46 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (46 - (46 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_46 :
    recurrence4Scalar1Left.coeff 46 =
      (((1433083287659396 * 10 ^ 70 +
        5182620558734669929277434720698797523685607495836743829463563897269255) * 10 ^ 70 +
        5592188378715877942958035305732199235488182575508901428184224619185139) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (46 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_46_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_47_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (47 + x) *
        remainder4Coefficient1.coeff (47 - (47 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 47 + x
  · rw [recurrence4LeadingSquare_coeff_high (47 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (47 - (47 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_47 :
    recurrence4Scalar1Left.coeff 47 =
      -(((467825012025360587 * 10 ^ 70 +
        1229019258667720152222877242863814248283457028901049268262574229044204) * 10 ^ 70 +
        2911267944771046770336243144437473159491353247110663938414554785326295) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (47 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_47_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_48_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (48 + x) *
        remainder4Coefficient1.coeff (48 - (48 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 48 + x
  · rw [recurrence4LeadingSquare_coeff_high (48 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (48 - (48 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_48 :
    recurrence4Scalar1Left.coeff 48 =
      (((64357831141051309904 * 10 ^ 70 +
        7550022315575286603205434792065644540527317658217170067568085056690785) * 10 ^ 70 +
        8593564258855357598288974834245892632080546773583592928303714330123153) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (48 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_48_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_49_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (49 + x) *
        remainder4Coefficient1.coeff (49 - (49 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 49 + x
  · rw [recurrence4LeadingSquare_coeff_high (49 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (49 - (49 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_49 :
    recurrence4Scalar1Left.coeff 49 =
      -(((6780283266861045609800 * 10 ^ 70 +
        7146285368243627927768157052128879010501561634520113784553497703404740) * 10 ^ 70 +
        5692723102804397706380259354327566626733494837786774798519315844539137) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (49 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_49_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_50_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (50 + x) *
        remainder4Coefficient1.coeff (50 - (50 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 50 + x
  · rw [recurrence4LeadingSquare_coeff_high (50 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (50 - (50 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_50 :
    recurrence4Scalar1Left.coeff 50 =
      (((610168502147786387417529 * 10 ^ 70 +
        3610903284770278198739749426641189494694081413204614037087598518002998) * 10 ^ 70 +
        6814344214990134625063780258654579733723893496350998192641617502700328) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (50 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_50_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_51_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (51 + x) *
        remainder4Coefficient1.coeff (51 - (51 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 51 + x
  · rw [recurrence4LeadingSquare_coeff_high (51 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (51 - (51 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_51 :
    recurrence4Scalar1Left.coeff 51 =
      -(((48887946504534378661299359 * 10 ^ 70 +
        4375449768558053770594703440818438198096539657645964227289110978414487) * 10 ^ 70 +
        4905676138968354679254882647990583976697812655438731515697504218436751) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (51 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_51_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_52_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (52 + x) *
        remainder4Coefficient1.coeff (52 - (52 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 52 + x
  · rw [recurrence4LeadingSquare_coeff_high (52 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (52 - (52 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_52 :
    recurrence4Scalar1Left.coeff 52 =
      (((3560679445490136693662319550 * 10 ^ 70 +
        4647344494608828640323442988044477726519204161207628088669710350554821) * 10 ^ 70 +
        6527557643248453634950335476913092626890225239088447104248380336495307) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (52 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_52_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_53_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (53 + x) *
        remainder4Coefficient1.coeff (53 - (53 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 53 + x
  · rw [recurrence4LeadingSquare_coeff_high (53 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (53 - (53 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_53 :
    recurrence4Scalar1Left.coeff 53 =
      -(((238646809675073624706211386436 * 10 ^ 70 +
        4141306506171006693083216261805812214440741256522335866169879438367425) * 10 ^ 70 +
        3560394786854932913407908441894571920508140415362523344006947170201688) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (53 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_53_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_54_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (54 + x) *
        remainder4Coefficient1.coeff (54 - (54 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 54 + x
  · rw [recurrence4LeadingSquare_coeff_high (54 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (54 - (54 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_54 :
    recurrence4Scalar1Left.coeff 54 =
      (((14836786514148983290105204548637 * 10 ^ 70 +
        6587187293508553269601859475571523704217474189671877080096985616506811) * 10 ^ 70 +
        8058757587765952306334152399140680840848249995540124865331357280859805) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (54 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_54_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_55_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (55 + x) *
        remainder4Coefficient1.coeff (55 - (55 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 55 + x
  · rw [recurrence4LeadingSquare_coeff_high (55 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (55 - (55 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_55 :
    recurrence4Scalar1Left.coeff 55 =
      -(((860447010897594386915041264688006 * 10 ^ 70 +
        5265920558591492832269040048350859057150167833076428391937893708536744) * 10 ^ 70 +
        9545687732039591013881292421284666174229994695004407607661927952325489) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (55 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_55_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_56_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (56 + x) *
        remainder4Coefficient1.coeff (56 - (56 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 56 + x
  · rw [recurrence4LeadingSquare_coeff_high (56 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (56 - (56 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_56 :
    recurrence4Scalar1Left.coeff 56 =
      (((46742964372635072294072957003256544 * 10 ^ 70 +
        4904727091637327378814984400813374904218998835370483493206938808708853) * 10 ^ 70 +
        9375192573660945834370959759206586832704162003901519962842455986849666) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (56 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_56_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_57_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (57 + x) *
        remainder4Coefficient1.coeff (57 - (57 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 57 + x
  · rw [recurrence4LeadingSquare_coeff_high (57 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (57 - (57 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_57 :
    recurrence4Scalar1Left.coeff 57 =
      -(((2386216665867495163519465091104100735 * 10 ^ 70 +
        1907936441170802483191698657078080190816223344543582264579029549836029) * 10 ^ 70 +
        9047086916480904166455746045302324492675210655788063413020486493014131) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (57 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_57_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_58_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (58 + x) *
        remainder4Coefficient1.coeff (58 - (58 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 58 + x
  · rw [recurrence4LeadingSquare_coeff_high (58 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (58 - (58 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_58 :
    recurrence4Scalar1Left.coeff 58 =
      (((114765201730165933141693608321536500188 * 10 ^ 70 +
        7382531825053547069957739742583549980024061209554012745228799589462386) * 10 ^ 70 +
        2696726090768896127999945140139119095395214778587672750965328414116970) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (58 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_58_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_59_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (59 + x) *
        remainder4Coefficient1.coeff (59 - (59 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 59 + x
  · rw [recurrence4LeadingSquare_coeff_high (59 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (59 - (59 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_59 :
    recurrence4Scalar1Left.coeff 59 =
      -(((5210875159667630936719224841498579927975 * 10 ^ 70 +
        6856249408647331795947989159777786803072861048405605265955119854644814) * 10 ^ 70 +
        7875165961771509647075662453475601817506846425321267945540017287272128) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (59 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_59_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_60_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (60 + x) *
        remainder4Coefficient1.coeff (60 - (60 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 60 + x
  · rw [recurrence4LeadingSquare_coeff_high (60 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (60 - (60 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_60 :
    recurrence4Scalar1Left.coeff 60 =
      (((223738594196880232461554248417531322898954 * 10 ^ 70 +
        7016823691268610999203068389219404389291632299746922216999937936891549) * 10 ^ 70 +
        5452978925730142787868006974668739393136901899950988218424626420984124) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (60 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_60_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_61_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (61 + x) *
        remainder4Coefficient1.coeff (61 - (61 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 61 + x
  · rw [recurrence4LeadingSquare_coeff_high (61 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (61 - (61 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_61 :
    recurrence4Scalar1Left.coeff 61 =
      -(((9096987294408812842074380093160974537091082 * 10 ^ 70 +
        3204832670381819113453642940792988055689068156606539976185468732631170) * 10 ^ 70 +
        0368662891600321197146854251398542174155105780570175058582533381925572) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (61 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_61_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_62_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (62 + x) *
        remainder4Coefficient1.coeff (62 - (62 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 62 + x
  · rw [recurrence4LeadingSquare_coeff_high (62 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (62 - (62 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_62 :
    recurrence4Scalar1Left.coeff 62 =
      (((350641481928570222263478078266082979191703866 * 10 ^ 70 +
        9235609072650698007686601735613198215683923741117847445691302442993742) * 10 ^ 70 +
        9971172206746708703087862030096286737605837989009835841634093464442485) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (62 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_62_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_63_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (63 + x) *
        remainder4Coefficient1.coeff (63 - (63 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 63 + x
  · rw [recurrence4LeadingSquare_coeff_high (63 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (63 - (63 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_63 :
    recurrence4Scalar1Left.coeff 63 =
      -(((12823808366569304465001724623884927802456498291 * 10 ^ 70 +
        9969983796099265273748866418791053591085291967605405685769401837610523) * 10 ^ 70 +
        4168215909657886497860008241588146969861930893181790973108078775779987) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (63 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_63_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_64_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (64 + x) *
        remainder4Coefficient1.coeff (64 - (64 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 64 + x
  · rw [recurrence4LeadingSquare_coeff_high (64 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (64 - (64 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_64 :
    recurrence4Scalar1Left.coeff 64 =
      (((445284741373591801078605305672985401823601325496 * 10 ^ 70 +
        5530801315266029942761163081991696212557191768215546373468357062459479) * 10 ^ 70 +
        9843808370801173515709496157274526438564892382348949360444765766899993) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (64 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_64_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_65_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (65 + x) *
        remainder4Coefficient1.coeff (65 - (65 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 65 + x
  · rw [recurrence4LeadingSquare_coeff_high (65 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (65 - (65 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_65 :
    recurrence4Scalar1Left.coeff 65 =
      -(((14685946089273671127277102050077392688640489173671 * 10 ^ 70 +
        3369080307753899659948392867563739013794184714393524295305836441440582) * 10 ^ 70 +
        3573338226450530566029013851835824820283823337100393178033835932774035) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (65 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_65_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_66_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (66 + x) *
        remainder4Coefficient1.coeff (66 - (66 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 66 + x
  · rw [recurrence4LeadingSquare_coeff_high (66 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (66 - (66 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_66 :
    recurrence4Scalar1Left.coeff 66 =
      (((460121910934922548055121423059897461076770400474722 * 10 ^ 70 +
        1258019505228362489233071073004623390128835813067357314083796418291910) * 10 ^ 70 +
        2933449273451948981283574011047813536830572833175748483766321368409517) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (66 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_66_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_67_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (67 + x) *
        remainder4Coefficient1.coeff (67 - (67 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 67 + x
  · rw [recurrence4LeadingSquare_coeff_high (67 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (67 - (67 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_67 :
    recurrence4Scalar1Left.coeff 67 =
      -(((13692500228338617985877875048806420663373835425181025 * 10 ^ 70 +
        2615731608165097880640727509892121915318074024056398614173181858510825) * 10 ^ 70 +
        1470346815514409985843539542685648913225142788783032499120439357642556) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (67 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_67_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_68_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (68 + x) *
        remainder4Coefficient1.coeff (68 - (68 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 68 + x
  · rw [recurrence4LeadingSquare_coeff_high (68 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (68 - (68 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_68 :
    recurrence4Scalar1Left.coeff 68 =
      (((386812428029844055545897810595385365863151180546812759 * 10 ^ 70 +
        4620160469540114108078017996693006107924004381483026570338740879107311) * 10 ^ 70 +
        5225654811531264242027628243624435737429930960160157004798537253261952) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (68 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_68_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_69_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (69 + x) *
        remainder4Coefficient1.coeff (69 - (69 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 69 + x
  · rw [recurrence4LeadingSquare_coeff_high (69 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (69 - (69 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_69 :
    recurrence4Scalar1Left.coeff 69 =
      -(((10362891398884054381157678296779478938966774179586587648 * 10 ^ 70 +
        3120303204651012185444888839768890028628971745664567383476460472141421) * 10 ^ 70 +
        3396181779674732956463888731845972429674708206745698559577191077728288) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (69 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_69_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_70_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (70 + x) *
        remainder4Coefficient1.coeff (70 - (70 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 70 + x
  · rw [recurrence4LeadingSquare_coeff_high (70 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (70 - (70 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_70 :
    recurrence4Scalar1Left.coeff 70 =
      (((262834534570918265924859582973296467155649575441531300942 * 10 ^ 70 +
        0152975579874813740810233484226540240232651321417949087604842321580769) * 10 ^ 70 +
        5048059233583509320184263296298291703231545068894593228816909215869509) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (70 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_70_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_71_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (71 + x) *
        remainder4Coefficient1.coeff (71 - (71 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 71 + x
  · rw [recurrence4LeadingSquare_coeff_high (71 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (71 - (71 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_71 :
    recurrence4Scalar1Left.coeff 71 =
      -(((6293989670181592235016332602295101387829989261085438577955 * 10 ^ 70 +
        4600304166630872454343665481268687728452509453689892288180394475626303) * 10 ^ 70 +
        7992432390920348999397602249737382195501576748086737702988558661803898) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (71 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_71_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_72_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (72 + x) *
        remainder4Coefficient1.coeff (72 - (72 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 72 + x
  · rw [recurrence4LeadingSquare_coeff_high (72 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (72 - (72 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_72 :
    recurrence4Scalar1Left.coeff 72 =
      (((141692697025926772899155886331354035503894189025498995750862 * 10 ^ 70 +
        5115399134217000855242725012174807279109370154950764524786577064757357) * 10 ^ 70 +
        5261281937729863266322240661404374283432979179499407835860932828720898) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (72 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_72_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_73_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (73 + x) *
        remainder4Coefficient1.coeff (73 - (73 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 73 + x
  · rw [recurrence4LeadingSquare_coeff_high (73 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (73 - (73 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_73 :
    recurrence4Scalar1Left.coeff 73 =
      -(((2977984861340611018823121761970407706910997721066846574446565 * 10 ^ 70 +
        7805324934295045106160888420637470993378943910155543154887642668285641) * 10 ^ 70 +
        5781375178675759466112660908163798170999522144727434806741046822482320) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (73 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_73_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_74_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (74 + x) *
        remainder4Coefficient1.coeff (74 - (74 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 74 + x
  · rw [recurrence4LeadingSquare_coeff_high (74 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (74 - (74 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_74 :
    recurrence4Scalar1Left.coeff 74 =
      (((57738442344721287215089886848936175877840210588918246766682761 * 10 ^ 70 +
        0408708600045991348866855012557095907504682872654688907855401071968475) * 10 ^ 70 +
        0340328575376606051615884953787294458326655913630536335612987862360050) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (74 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_74_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_75_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (75 + x) *
        remainder4Coefficient1.coeff (75 - (75 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 75 + x
  · rw [recurrence4LeadingSquare_coeff_high (75 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (75 - (75 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_75 :
    recurrence4Scalar1Left.coeff 75 =
      -(((1009690425283115674511188902559491274757411568150575229542857569 * 10 ^ 70 +
        6096035974609497791169137625568859908766398555801831850545580343335656) * 10 ^ 70 +
        8554606215835850382081872166668168181846294093807465526790679439706542) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (75 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_75_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_76_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (76 + x) *
        remainder4Coefficient1.coeff (76 - (76 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 76 + x
  · rw [recurrence4LeadingSquare_coeff_high (76 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (76 - (76 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_76 :
    recurrence4Scalar1Left.coeff 76 =
      (((15146156816077858297723561340917545816848083626738418136433933577 * 10 ^ 70 +
        7136070400977813247816899334683281778702417779554995924169124938880790) * 10 ^ 70 +
        9854840953080144337334320610124605293402301929385579930247365459744180) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (76 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_76_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_77_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (77 + x) *
        remainder4Coefficient1.coeff (77 - (77 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 77 + x
  · rw [recurrence4LeadingSquare_coeff_high (77 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (77 - (77 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_77 :
    recurrence4Scalar1Left.coeff 77 =
      -(((166891154775828011797824928021106409927882644201027535092157594999 * 10 ^ 70 +
        3375198654969829509048583484872425318418543196308750092681218848715166) * 10 ^ 70 +
        2651935274850140301838153722568214600620701753281186993596549350776638) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (77 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_77_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_78_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (78 + x) *
        remainder4Coefficient1.coeff (78 - (78 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 78 + x
  · rw [recurrence4LeadingSquare_coeff_high (78 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (78 - (78 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_78 :
    recurrence4Scalar1Left.coeff 78 =
      (((204893610075827548963453874660839094199734251534703098169306418443 * 10 ^ 70 +
        0073898833706641920039022227354657346950707298145582273490558732887329) * 10 ^ 70 +
        4075406648458199977765930026434255620057842316613746764942739649854165) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (78 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_78_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_79_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (79 + x) *
        remainder4Coefficient1.coeff (79 - (79 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 79 + x
  · rw [recurrence4LeadingSquare_coeff_high (79 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (79 - (79 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_79 :
    recurrence4Scalar1Left.coeff 79 =
      (((59290712064035236209740044742536174707384705351388703164251781571757 * 10 ^ 70 +
        4957445696923475033238861644424919472778744520529562220399072957453641) * 10 ^ 70 +
        6097703271141154838953717869572328873148366041106224267684322444622466) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (79 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_79_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_80_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (80 + x) *
        remainder4Coefficient1.coeff (80 - (80 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 80 + x
  · rw [recurrence4LeadingSquare_coeff_high (80 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (80 - (80 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_80 :
    recurrence4Scalar1Left.coeff 80 =
      -(((2310722540481163671234525295507082200667241994980770494463629178324585 * 10 ^ 70 +
        4284747781118398420399154938033448436185627635149966446383938646319162) * 10 ^ 70 +
        9488064897745613176112567585808746226755278209940254959184444598579315) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (80 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_80_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_81_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (81 + x) *
        remainder4Coefficient1.coeff (81 - (81 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 81 + x
  · rw [recurrence4LeadingSquare_coeff_high (81 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (81 - (81 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_81 :
    recurrence4Scalar1Left.coeff 81 =
      ((((6 * 10 ^ 70 +
        3159886090066864534476018766655298419767629741331667292277198175848076) * 10 ^ 70 +
        0913747303801679136971303844295564175394949950472679422975488016756564) * 10 ^ 70 +
        4748896266249746685040323725305624572582115934584347975647255785030502) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (81 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_81_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_82_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (82 + x) *
        remainder4Coefficient1.coeff (82 - (82 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 82 + x
  · rw [recurrence4LeadingSquare_coeff_high (82 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (82 - (82 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_82 :
    recurrence4Scalar1Left.coeff 82 =
      -((((145 * 10 ^ 70 +
        6105295941353402545651087574584401054601799256733680305864713243862921) * 10 ^ 70 +
        7888350461184898008033220375653709237443670088053129666723415253154723) * 10 ^ 70 +
        8068411246186700908029197857051050834923355181356756037315621270860321) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (82 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_82_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_83_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (83 + x) *
        remainder4Coefficient1.coeff (83 - (83 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 83 + x
  · rw [recurrence4LeadingSquare_coeff_high (83 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (83 - (83 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_83 :
    recurrence4Scalar1Left.coeff 83 =
      ((((2984 * 10 ^ 70 +
        9518555509497788256446021583024559767086750706891048748526115742002928) * 10 ^ 70 +
        2799584483255317298792388417995052618061693779850483636157978293755921) * 10 ^ 70 +
        5235619827118797225656688117117732523785266030696389585746212880702062) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (83 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_83_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_84_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (84 + x) *
        remainder4Coefficient1.coeff (84 - (84 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 84 + x
  · rw [recurrence4LeadingSquare_coeff_high (84 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (84 - (84 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_84 :
    recurrence4Scalar1Left.coeff 84 =
      -((((55444 * 10 ^ 70 +
        8865890780866390462873918802482085201193500087451930464700403665792694) * 10 ^ 70 +
        4783263491861298454745684083399225209994669325698317152053551640482503) * 10 ^ 70 +
        7412276713744750051764905412588690992032115617351455427602841638512428) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (84 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_84_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_85_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (85 + x) *
        remainder4Coefficient1.coeff (85 - (85 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 85 + x
  · rw [recurrence4LeadingSquare_coeff_high (85 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (85 - (85 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_85 :
    recurrence4Scalar1Left.coeff 85 =
      ((((936091 * 10 ^ 70 +
        7538635854371928848103517109936136779584315397009802374408324072551045) * 10 ^ 70 +
        4380442959283984800746963871246765450453412161507556195590944361329771) * 10 ^ 70 +
        8727602241572144117402268010943096058426210133251609378782531180102965) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (85 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_85_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_86_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (86 + x) *
        remainder4Coefficient1.coeff (86 - (86 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 86 + x
  · rw [recurrence4LeadingSquare_coeff_high (86 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (86 - (86 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_86 :
    recurrence4Scalar1Left.coeff 86 =
      -((((14214648 * 10 ^ 70 +
        4829362198867329353452665472957958483512855297398812355443066957671121) * 10 ^ 70 +
        0403499527214525125519934473017494096865513862072334097044208168145961) * 10 ^ 70 +
        1342215033255424336322728636689233983148140731227645296294377150602133) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (86 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_86_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_87_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (87 + x) *
        remainder4Coefficient1.coeff (87 - (87 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 87 + x
  · rw [recurrence4LeadingSquare_coeff_high (87 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (87 - (87 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_87 :
    recurrence4Scalar1Left.coeff 87 =
      ((((187712247 * 10 ^ 70 +
        7412175100358095952245909998005455499190587583075750014892396455657092) * 10 ^ 70 +
        8033732922971079640013970645098765054458573911402959831838666059950441) * 10 ^ 70 +
        5367059537528083179945802157197215192623539166927343101284772805581357) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (87 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_87_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_88_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (88 + x) *
        remainder4Coefficient1.coeff (88 - (88 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 88 + x
  · rw [recurrence4LeadingSquare_coeff_high (88 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (88 - (88 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_88 :
    recurrence4Scalar1Left.coeff 88 =
      -((((1944958226 * 10 ^ 70 +
        3294746522892729903315228522627326138904286405784951356372328003421869) * 10 ^ 70 +
        6836719510262491827203224569290990751803970099971128555924756995032524) * 10 ^ 70 +
        4264002852795818880794760333064200993258408097410730279066191489173890) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (88 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_88_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_89_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (89 + x) *
        remainder4Coefficient1.coeff (89 - (89 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 89 + x
  · rw [recurrence4LeadingSquare_coeff_high (89 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (89 - (89 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_89 :
    recurrence4Scalar1Left.coeff 89 =
      ((((8710282534 * 10 ^ 70 +
        4844106797167736595049137713458956064019553317935698832666313321552374) * 10 ^ 70 +
        4169237070479994386945565201016574217274004645758270708721639863587576) * 10 ^ 70 +
        7964061827077230795629236390022983251368372480778548093216010346106868) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (89 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_89_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_90_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (90 + x) *
        remainder4Coefficient1.coeff (90 - (90 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 90 + x
  · rw [recurrence4LeadingSquare_coeff_high (90 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (90 - (90 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_90 :
    recurrence4Scalar1Left.coeff 90 =
      ((((272714461067 * 10 ^ 70 +
        3172041484215833730620443276810608448624307496557319885895892308692381) * 10 ^ 70 +
        2094792112444464078882026111895160764346699321442032677431754895346649) * 10 ^ 70 +
        7863484935767995143537495487229742832715443809064333510866996090386523) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (90 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_90_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_91_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (91 + x) *
        remainder4Coefficient1.coeff (91 - (91 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 91 + x
  · rw [recurrence4LeadingSquare_coeff_high (91 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (91 - (91 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_91 :
    recurrence4Scalar1Left.coeff 91 =
      -((((11142394613039 * 10 ^ 70 +
        0927741777125391130711025468862394095952495862146326185978250660307136) * 10 ^ 70 +
        3459973807163848888742583675791719905484642210920186371676071377230479) * 10 ^ 70 +
        8678539296584428624831584961902834622516221213641368274546504802450136) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (91 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_91_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_92_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (92 + x) *
        remainder4Coefficient1.coeff (92 - (92 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 92 + x
  · rw [recurrence4LeadingSquare_coeff_high (92 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (92 - (92 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_92 :
    recurrence4Scalar1Left.coeff 92 =
      ((((278730620855645 * 10 ^ 70 +
        1284438290631800270528046811689957636579593178036542656902781443750711) * 10 ^ 70 +
        9947242712952254299344909270413126056256320926643102721530700723938673) * 10 ^ 70 +
        3993622735277471095527347672956035018924658964761866273067789424499725) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (92 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_92_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_93_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (93 + x) *
        remainder4Coefficient1.coeff (93 - (93 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 93 + x
  · rw [recurrence4LeadingSquare_coeff_high (93 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (93 - (93 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_93 :
    recurrence4Scalar1Left.coeff 93 =
      -((((5786792717783718 * 10 ^ 70 +
        2687260351459806505636309607288772461085167718390214231750454123500580) * 10 ^ 70 +
        9635724864195849576224011549294924344252865596679084061335930259840268) * 10 ^ 70 +
        6455066995764625434696711833754651647293772363900632444601169659878363) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (93 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_93_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_94_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (94 + x) *
        remainder4Coefficient1.coeff (94 - (94 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 94 + x
  · rw [recurrence4LeadingSquare_coeff_high (94 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (94 - (94 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_94 :
    recurrence4Scalar1Left.coeff 94 =
      ((((107632043102952038 * 10 ^ 70 +
        0111533130641923201730676227475266462129833062848766771668297463228162) * 10 ^ 70 +
        4573931216069228255323406209568572101101532915896558679659155261862370) * 10 ^ 70 +
        2557990834209450187936903814106895141408346474142457662826657973647006) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (94 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_94_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_95_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (95 + x) *
        remainder4Coefficient1.coeff (95 - (95 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 95 + x
  · rw [recurrence4LeadingSquare_coeff_high (95 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (95 - (95 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_95 :
    recurrence4Scalar1Left.coeff 95 =
      -((((1850912568549979125 * 10 ^ 70 +
        5141426363920189289392075125390053477274356883932409364813717311564951) * 10 ^ 70 +
        5787755359355571485315379775242774810750033937240685974217812132132971) * 10 ^ 70 +
        6823772565286090129484395636761418675654933573888085346988753289883657) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (95 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_95_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_96_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (96 + x) *
        remainder4Coefficient1.coeff (96 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 96 + x
  · rw [recurrence4LeadingSquare_coeff_high (96 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (96 - (96 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_96 :
    recurrence4Scalar1Left.coeff 96 =
      ((((29912225396993126344 * 10 ^ 70 +
        4380851384972313768944936729252189508227160948716221740261588056137504) * 10 ^ 70 +
        5918123200249840567695299927706620302426029789216415818078924880546935) * 10 ^ 70 +
        9663201313671278860741440303367422409504283698549785145780185939207419) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (96 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_96_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_97_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (97 + x) *
        remainder4Coefficient1.coeff (97 - (97 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 97 + x
  · rw [recurrence4LeadingSquare_coeff_high (97 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (97 - (97 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_97 :
    recurrence4Scalar1Left.coeff 97 =
      -((((458693978598539308661 * 10 ^ 70 +
        2998168939185510937701084557054927245103429571505826985402914198211055) * 10 ^ 70 +
        8469369063300873945455082558831399331777203074089797102197536575233303) * 10 ^ 70 +
        4975023709195372776284603201009063069596015254261173107838392031397501) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (97 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_97_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_98_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (98 + x) *
        remainder4Coefficient1.coeff (98 - (98 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 98 + x
  · rw [recurrence4LeadingSquare_coeff_high (98 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (98 - (98 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_98 :
    recurrence4Scalar1Left.coeff 98 =
      ((((6716361539785557248193 * 10 ^ 70 +
        7419510035589798434704288004292383122764458782091879145803831264269071) * 10 ^ 70 +
        1194730338089256032602965927413677295353170338851193630186915614367094) * 10 ^ 70 +
        6367055598662292647461591794929718637742945803048739673381844880099000) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (98 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_98_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_99_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (99 + x) *
        remainder4Coefficient1.coeff (99 - (99 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 99 + x
  · rw [recurrence4LeadingSquare_coeff_high (99 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (99 - (99 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_99 :
    recurrence4Scalar1Left.coeff 99 =
      -((((94314264623537929121230 * 10 ^ 70 +
        1993272107912861974334159002580329447726700595048356089908086582850478) * 10 ^ 70 +
        3614972269480782735503314195746500793324540633323748045812273078661151) * 10 ^ 70 +
        8736342530189028071151653748843815619144209269333157494191275309759259) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (99 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_99_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_100_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (100 + x) *
        remainder4Coefficient1.coeff (100 - (100 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 100 + x
  · rw [recurrence4LeadingSquare_coeff_high (100 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (100 - (100 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_100 :
    recurrence4Scalar1Left.coeff 100 =
      ((((1274212902025355147875235 * 10 ^ 70 +
        0014241203934253662527405830399146318088681246521975359832332285998854) * 10 ^ 70 +
        2936924723892812670140415866056675602993240309372292656853631161216375) * 10 ^ 70 +
        8607416354159560816086237855989417100748525509674045704288905704741706) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (100 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_100_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_101_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (101 + x) *
        remainder4Coefficient1.coeff (101 - (101 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 101 + x
  · rw [recurrence4LeadingSquare_coeff_high (101 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (101 - (101 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_101 :
    recurrence4Scalar1Left.coeff 101 =
      -((((16603081853502501038361117 * 10 ^ 70 +
        6692383062566148240561966064666104581636955764093641357196626369124798) * 10 ^ 70 +
        8594765053886884299777417803108667654203273810957822704420648238810494) * 10 ^ 70 +
        3393442175412502942760722335494704361827404454696622340356484393678511) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (101 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_101_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_102_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (102 + x) *
        remainder4Coefficient1.coeff (102 - (102 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 102 + x
  · rw [recurrence4LeadingSquare_coeff_high (102 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (102 - (102 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_102 :
    recurrence4Scalar1Left.coeff 102 =
      ((((209052507173516768567385405 * 10 ^ 70 +
        4684965479907523367208766375750577589808117671622619891374299172832619) * 10 ^ 70 +
        9451257585633984456010191203876055246134678114345023749444762683508762) * 10 ^ 70 +
        8545211967768798891900006409352901212263784501723163517995574944326098) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (102 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_102_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_103_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (103 + x) *
        remainder4Coefficient1.coeff (103 - (103 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 103 + x
  · rw [recurrence4LeadingSquare_coeff_high (103 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (103 - (103 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_103 :
    recurrence4Scalar1Left.coeff 103 =
      -((((2547548741110108178173629026 * 10 ^ 70 +
        4253184931435668001558158788688136523569643848678245726162190202984598) * 10 ^ 70 +
        0314380006087575152061397373296977886511148055311821369275520582848761) * 10 ^ 70 +
        0109459551617273334552868183941196106235464644207234601254787350176883) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (103 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_103_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_104_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (104 + x) *
        remainder4Coefficient1.coeff (104 - (104 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 104 + x
  · rw [recurrence4LeadingSquare_coeff_high (104 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (104 - (104 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_104 :
    recurrence4Scalar1Left.coeff 104 =
      ((((30085402918850463451951265135 * 10 ^ 70 +
        1632767673150371381353358404343365625730818608802911037072074032536021) * 10 ^ 70 +
        1856111289078332551895763159724830004400459429423496756888433234300088) * 10 ^ 70 +
        6004914908528459649564537319223547084425383229345196985811572201297351) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (104 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_104_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_105_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (105 + x) *
        remainder4Coefficient1.coeff (105 - (105 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 105 + x
  · rw [recurrence4LeadingSquare_coeff_high (105 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (105 - (105 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_105 :
    recurrence4Scalar1Left.coeff 105 =
      -((((344695149055073916158690794229 * 10 ^ 70 +
        5964130752038863486925832687284127411215049907905551179644708524074762) * 10 ^ 70 +
        8975593033911498583032625312969742082888957921916244995761087799803051) * 10 ^ 70 +
        8859379112282105276618130620467469801349167878370096677037924634150781) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (105 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_105_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (106 + x) *
        remainder4Coefficient1.coeff (106 - (106 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 106 + x
  · rw [recurrence4LeadingSquare_coeff_high (106 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (106 - (106 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_106 :
    recurrence4Scalar1Left.coeff 106 =
      ((((3835079622278795157236889490386 * 10 ^ 70 +
        2039860541009361024337538044030593332693471422385709522254614274187096) * 10 ^ 70 +
        2224938527404640193263036540468645915025539673002328764089634388813707) * 10 ^ 70 +
        4216301650161910008340355761660456717889071599590413322461949888112189) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (106 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_106_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (107 + x) *
        remainder4Coefficient1.coeff (107 - (107 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 107 + x
  · rw [recurrence4LeadingSquare_coeff_high (107 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (107 - (107 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_107 :
    recurrence4Scalar1Left.coeff 107 =
      -((((41470160009675924921391946907331 * 10 ^ 70 +
        7448152629047715039569783366327566330927685096365594093628044456922395) * 10 ^ 70 +
        4825188341940219665390084322931075045020036083397770675552919247963270) * 10 ^ 70 +
        6927838124624072554935301563757078736342494894956094664689925775557857) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (107 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_107_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (108 + x) *
        remainder4Coefficient1.coeff (108 - (108 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 108 + x
  · rw [recurrence4LeadingSquare_coeff_high (108 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (108 - (108 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_108 :
    recurrence4Scalar1Left.coeff 108 =
      ((((436154368793780843651788324745273 * 10 ^ 70 +
        9792312517821524725084529911041320245614261232667462791705767232405615) * 10 ^ 70 +
        3956393687510937429878623458380434626770456738350149409660647652817235) * 10 ^ 70 +
        0595579902822300032928881903203208533753205551909615890990306700759982) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (108 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_108_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (109 + x) *
        remainder4Coefficient1.coeff (109 - (109 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 109 + x
  · rw [recurrence4LeadingSquare_coeff_high (109 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (109 - (109 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_109 :
    recurrence4Scalar1Left.coeff 109 =
      -((((4464529112687811945148164122015098 * 10 ^ 70 +
        5469450660740003829176794268129618763408810383082261032534836860723576) * 10 ^ 70 +
        3450278000372993156077026385479711333090728245910051127332921993339752) * 10 ^ 70 +
        2608813395443129951972047725485646304760707960106052327112541820590068) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (109 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_109_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (110 + x) *
        remainder4Coefficient1.coeff (110 - (110 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 110 + x
  · rw [recurrence4LeadingSquare_coeff_high (110 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (110 - (110 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_110 :
    recurrence4Scalar1Left.coeff 110 =
      ((((44504335236510943139052651158525894 * 10 ^ 70 +
        6171011136429891894043326534815724420078203777025898210772239957217362) * 10 ^ 70 +
        2375722440889557379716482566330121050182458990339542068271053597612921) * 10 ^ 70 +
        2187065545870370014478820394571172021345874272925151100164634616772014) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (110 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_110_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (111 + x) *
        remainder4Coefficient1.coeff (111 - (111 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 111 + x
  · rw [recurrence4LeadingSquare_coeff_high (111 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (111 - (111 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_111 :
    recurrence4Scalar1Left.coeff 111 =
      -((((432272572583619348595243494836119849 * 10 ^ 70 +
        3792966885602613315541635368006402646631276152628564405878659419739683) * 10 ^ 70 +
        0488992807096885739740816709532517667882765026302777688553212773588685) * 10 ^ 70 +
        9060807344877176660661920134298025807830902848665339594896407352769951) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (111 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_111_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (112 + x) *
        remainder4Coefficient1.coeff (112 - (112 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 112 + x
  · rw [recurrence4LeadingSquare_coeff_high (112 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (112 - (112 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_112 :
    recurrence4Scalar1Left.coeff 112 =
      ((((4093171846637418152453439916231667452 * 10 ^ 70 +
        9002166296891593184868609628501341158441495622409183473435020823087489) * 10 ^ 70 +
        2626611887480184570375228390296753213859034596966123843084398427345980) * 10 ^ 70 +
        3595589343164183885389881279648267889892376105357621907764789841185443) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (112 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_112_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (113 + x) *
        remainder4Coefficient1.coeff (113 - (113 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 113 + x
  · rw [recurrence4LeadingSquare_coeff_high (113 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (113 - (113 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_113 :
    recurrence4Scalar1Left.coeff 113 =
      -((((37801675242139679891599342630928984098 * 10 ^ 70 +
        9918940972133855529890038834337736739971463508318444291741388308675896) * 10 ^ 70 +
        0134280666783206617885004326766469359908201278576289719530813166645035) * 10 ^ 70 +
        9302678775378800421583527825225716208408850845726378735342755132328287) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (113 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_113_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (114 + x) *
        remainder4Coefficient1.coeff (114 - (114 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 114 + x
  · rw [recurrence4LeadingSquare_coeff_high (114 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (114 - (114 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_114 :
    recurrence4Scalar1Left.coeff 114 =
      ((((340642327744769746243002239381884174384 * 10 ^ 70 +
        4808666203508721525096693049183790419265332914593593195005691407525296) * 10 ^ 70 +
        5414013499029866446431537868011978160510850863626010127210417932271814) * 10 ^ 70 +
        3718047999389553295643459645367929887601673745811170394551187086403984) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (114 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_114_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (115 + x) *
        remainder4Coefficient1.coeff (115 - (115 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 115 + x
  · rw [recurrence4LeadingSquare_coeff_high (115 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (115 - (115 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_115 :
    recurrence4Scalar1Left.coeff 115 =
      -((((2996388669297270437427877512510165140842 * 10 ^ 70 +
        2073615064175262391059227885770289313243257795986206521865796426315940) * 10 ^ 70 +
        7004738157667288717193858594025216050435194660651384822094967890364840) * 10 ^ 70 +
        5805789332798519967219972786409608958886333677222447231830621645481501) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (115 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_115_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (116 + x) *
        remainder4Coefficient1.coeff (116 - (116 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 116 + x
  · rw [recurrence4LeadingSquare_coeff_high (116 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (116 - (116 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_116 :
    recurrence4Scalar1Left.coeff 116 =
      ((((25737975929062535169651386915765127923576 * 10 ^ 70 +
        7250556940486314041426985764579873844913224002281376584975616907108586) * 10 ^ 70 +
        1172334272720994117967468050975654203788961354431370656313494228601737) * 10 ^ 70 +
        1549110141633992407091031175898149122658849385916136440897426068422313) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (116 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_116_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (117 + x) *
        remainder4Coefficient1.coeff (117 - (117 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 117 + x
  · rw [recurrence4LeadingSquare_coeff_high (117 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (117 - (117 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_117 :
    recurrence4Scalar1Left.coeff 117 =
      -((((215964621234868545802422839454733376376877 * 10 ^ 70 +
        3375889616606709472882293038937503654265258740103697585295852605140711) * 10 ^ 70 +
        7786788058470736159493346689654134678903656929995545222848852352151949) * 10 ^ 70 +
        3750424305260077556171651464549287772440631279297615616428951443094787) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (117 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_117_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (118 + x) *
        remainder4Coefficient1.coeff (118 - (118 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 118 + x
  · rw [recurrence4LeadingSquare_coeff_high (118 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (118 - (118 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_118 :
    recurrence4Scalar1Left.coeff 118 =
      ((((1770800578436909431545005952976755035572529 * 10 ^ 70 +
        2302429922134200253286219431197489292067924012733774538274697035305980) * 10 ^ 70 +
        9230413909913756202371961659826125751441214797021749338644505634696345) * 10 ^ 70 +
        7308389764951727673765759054110703564073587625099271800321497882738398) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (118 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_118_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (119 + x) *
        remainder4Coefficient1.coeff (119 - (119 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 119 + x
  · rw [recurrence4LeadingSquare_coeff_high (119 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (119 - (119 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_119 :
    recurrence4Scalar1Left.coeff 119 =
      -((((14193020294822084098923825276194210656226439 * 10 ^ 70 +
        9082108516586368648259880565890892417446683718438877930400706393870047) * 10 ^ 70 +
        1186473979925427321258503007942090276568648708854545897894790702907342) * 10 ^ 70 +
        6690938063076080411784153521742857674852648987870722627925859340024449) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (119 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_119_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (120 + x) *
        remainder4Coefficient1.coeff (120 - (120 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 120 + x
  · rw [recurrence4LeadingSquare_coeff_high (120 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (120 - (120 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_120 :
    recurrence4Scalar1Left.coeff 120 =
      ((((111232226112718984638331090258019654807671963 * 10 ^ 70 +
        6759788300219653010292297711626728654170295256035274540243084444282434) * 10 ^ 70 +
        9674219525516788365779609959591364531211973581349290020297979141173633) * 10 ^ 70 +
        9734106862934489881980795746426671500155279758250579129804335528629466) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (120 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_120_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (121 + x) *
        remainder4Coefficient1.coeff (121 - (121 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 121 + x
  · rw [recurrence4LeadingSquare_coeff_high (121 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (121 - (121 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_121 :
    recurrence4Scalar1Left.coeff 121 =
      -((((852635531253777267845807960412128612433912565 * 10 ^ 70 +
        6703212585852615481147827875111792146174304088853285951237126518725550) * 10 ^ 70 +
        5942602648746543869307843153192695142755345129887370913385858627118470) * 10 ^ 70 +
        6654111895381122847998021625169971209920426117755302798981864046708951) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (121 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_121_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (122 + x) *
        remainder4Coefficient1.coeff (122 - (122 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 122 + x
  · rw [recurrence4LeadingSquare_coeff_high (122 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (122 - (122 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_122 :
    recurrence4Scalar1Left.coeff 122 =
      ((((6394314094525898008852880701829322315755494500 * 10 ^ 70 +
        3698259904034862633900349712994710663993637487616597535208309257615577) * 10 ^ 70 +
        4374918784909123548936849861913115929013531891986660185018553441056100) * 10 ^ 70 +
        1222871649152798107940965486939485076275709086585267435970275052915041) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (122 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_122_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (123 + x) *
        remainder4Coefficient1.coeff (123 - (123 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 123 + x
  · rw [recurrence4LeadingSquare_coeff_high (123 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (123 - (123 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_123 :
    recurrence4Scalar1Left.coeff 123 =
      -((((46928628049956608046392858743707474527071749001 * 10 ^ 70 +
        6751991768350483394524780771388997338263132327113549539882442711087348) * 10 ^ 70 +
        3962278235694753429200763145979784488159512978759740569453330501116626) * 10 ^ 70 +
        4382344787020434977987390920196250459598966735213531196353290966195625) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (123 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_123_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (124 + x) *
        remainder4Coefficient1.coeff (124 - (124 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 124 + x
  · rw [recurrence4LeadingSquare_coeff_high (124 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (124 - (124 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_124 :
    recurrence4Scalar1Left.coeff 124 =
      ((((337136669369144159151093142946320886314516552744 * 10 ^ 70 +
        5523625196171564465121373529742797899521676522283582387779752207499989) * 10 ^ 70 +
        3827411904067961650474667563454084072227797717148147666152936357176082) * 10 ^ 70 +
        7619980515676396568328534513796276220875036672441491488393888429013476) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (124 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_124_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (125 + x) *
        remainder4Coefficient1.coeff (125 - (125 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 125 + x
  · rw [recurrence4LeadingSquare_coeff_high (125 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (125 - (125 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_125 :
    recurrence4Scalar1Left.coeff 125 =
      -((((2371400400640449810971259650923830759082133899271 * 10 ^ 70 +
        9437501497218921091320321920164410606049899064627962511268454647335322) * 10 ^ 70 +
        9830102964699212916229319282669706106644377011414494911705873823886524) * 10 ^ 70 +
        0517983537712433572095692070779933188385591158555662683271206131944783) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (125 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_125_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (126 + x) *
        remainder4Coefficient1.coeff (126 - (126 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 126 + x
  · rw [recurrence4LeadingSquare_coeff_high (126 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (126 - (126 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_126 :
    recurrence4Scalar1Left.coeff 126 =
      ((((16335672462590625920652827728009518794261101514590 * 10 ^ 70 +
        5355873575817386416037969610498198201769659750653412297194033109324523) * 10 ^ 70 +
        6320282911847938087179088769850131376578741778125578817832793359068639) * 10 ^ 70 +
        8583600515409842066002243973669035709223527814111071381173750701078242) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (126 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_126_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (127 + x) *
        remainder4Coefficient1.coeff (127 - (127 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 127 + x
  · rw [recurrence4LeadingSquare_coeff_high (127 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (127 - (127 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_127 :
    recurrence4Scalar1Left.coeff 127 =
      -((((110230320369379694139549570961065590106132842387873 * 10 ^ 70 +
        4768806468413027688302126404524318629814781852828327788734680132961725) * 10 ^ 70 +
        2031896416187248127138281301824474591505263593996146213051698404470490) * 10 ^ 70 +
        9021123558292342245826372918954126201646038479791186564212090548229508) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (127 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_127_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (128 + x) *
        remainder4Coefficient1.coeff (128 - (128 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 128 + x
  · rw [recurrence4LeadingSquare_coeff_high (128 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (128 - (128 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_128 :
    recurrence4Scalar1Left.coeff 128 =
      ((((728772892342431882562606582843696579496865295030966 * 10 ^ 70 +
        3335865644290234649865702105271261127432260119349921227767799434344497) * 10 ^ 70 +
        6583469126959067377932835624416123220390603894868949005475807710710416) * 10 ^ 70 +
        5747070421955253865631860047279397153026918411667384756534718858471663) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (128 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_128_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (129 + x) *
        remainder4Coefficient1.coeff (129 - (129 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 129 + x
  · rw [recurrence4LeadingSquare_coeff_high (129 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (129 - (129 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_129 :
    recurrence4Scalar1Left.coeff 129 =
      -((((4721742406929675024896201544873164958935073377120832 * 10 ^ 70 +
        5936079930676619761868362203280039571534530811966251923101873849097746) * 10 ^ 70 +
        6220204709973334011496615323915055618092646056792083976174262643291642) * 10 ^ 70 +
        9422578810885891790738186094710944860500988137429044242001597893686700) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (129 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_129_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (130 + x) *
        remainder4Coefficient1.coeff (130 - (130 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 130 + x
  · rw [recurrence4LeadingSquare_coeff_high (130 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (130 - (130 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_130 :
    recurrence4Scalar1Left.coeff 130 =
      ((((29986104291563651521575262116348269091482797910919437 * 10 ^ 70 +
        2280612338498031545343135827531502196276183438363487872204309482470367) * 10 ^ 70 +
        3378345639557355338859458063705970520070125966616231235024725913012949) * 10 ^ 70 +
        7394150545113385022486138066219529092263990995985422107859211623831542) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (130 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_130_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (131 + x) *
        remainder4Coefficient1.coeff (131 - (131 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 131 + x
  · rw [recurrence4LeadingSquare_coeff_high (131 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (131 - (131 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_131 :
    recurrence4Scalar1Left.coeff 131 =
      -((((186694392966148835127506720161753078981032408373576455 * 10 ^ 70 +
        8417281065470185561530056812310511489325528536180190659966852670342062) * 10 ^ 70 +
        6093776533539828022916790424094812974682564870479282721492519946475639) * 10 ^ 70 +
        9258918181646412916872838007194831246605581223429074921290056672105396) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (131 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_131_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (132 + x) *
        remainder4Coefficient1.coeff (132 - (132 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 132 + x
  · rw [recurrence4LeadingSquare_coeff_high (132 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (132 - (132 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_132 :
    recurrence4Scalar1Left.coeff 132 =
      ((((1139774630094335723941486416793103998446790046159043307 * 10 ^ 70 +
        1405253430120350922465083137308328425514659706646205801523487001587899) * 10 ^ 70 +
        7522283777973543697994851252407602639958291710337497329205434985732577) * 10 ^ 70 +
        0432634271172065044813783958263411513203129473734555132835229639120102) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (132 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_132_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (133 + x) *
        remainder4Coefficient1.coeff (133 - (133 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 133 + x
  · rw [recurrence4LeadingSquare_coeff_high (133 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (133 - (133 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_133 :
    recurrence4Scalar1Left.coeff 133 =
      -((((6824385505142687414994077822829962757270650054129607743 * 10 ^ 70 +
        5898311422826293630373511546720363390616698808066726893261935810836127) * 10 ^ 70 +
        6094726876796347499715607613521966091386168322908409870833660149645479) * 10 ^ 70 +
        8955826260832183005959673247585167137867144086015313839765144125545041) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (133 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_133_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (134 + x) *
        remainder4Coefficient1.coeff (134 - (134 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 134 + x
  · rw [recurrence4LeadingSquare_coeff_high (134 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (134 - (134 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_134 :
    recurrence4Scalar1Left.coeff 134 =
      ((((40081395466374212191067713293418183642428562015879421104 * 10 ^ 70 +
        0064794980485725012766961210569484789995225249257686326259830198620497) * 10 ^ 70 +
        3721698952547640999369524941313258026213886587828656456514665882807501) * 10 ^ 70 +
        9421239729053713445047156968811389060307149309094965334534932314468155) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (134 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_134_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (135 + x) *
        remainder4Coefficient1.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 135 + x
  · rw [recurrence4LeadingSquare_coeff_high (135 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (135 - (135 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_135 :
    recurrence4Scalar1Left.coeff 135 =
      -((((230957621458142933088808386290797939463050826354049388654 * 10 ^ 70 +
        6186185123122204331584243070414394776414990363953408333385402838719969) * 10 ^ 70 +
        3036398359322230819626690306898076961893128781840973394961172672571754) * 10 ^ 70 +
        8082343089004018029087659060809547084413237741516711250412300924292991) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (135 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_135_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (136 + x) *
        remainder4Coefficient1.coeff (136 - (136 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 136 + x
  · rw [recurrence4LeadingSquare_coeff_high (136 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (136 - (136 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_136 :
    recurrence4Scalar1Left.coeff 136 =
      ((((1305885587246631111664525721926236132945934089649064326486 * 10 ^ 70 +
        2039338308394911311618938132016748399500317837132479020812442063913980) * 10 ^ 70 +
        5244312942401052746326040882134444837903792049467462839265310473315554) * 10 ^ 70 +
        8700926222847752584986928324836628446722601953291435934888414634317032) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (136 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_136_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (137 + x) *
        remainder4Coefficient1.coeff (137 - (137 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 137 + x
  · rw [recurrence4LeadingSquare_coeff_high (137 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (137 - (137 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_137 :
    recurrence4Scalar1Left.coeff 137 =
      -((((7246567143532433742291002529958417240811431214738650230824 * 10 ^ 70 +
        7586929486905989430475411464251552148603488558702687236002735479063640) * 10 ^ 70 +
        4598386549834817739960622707675886671814119423209703883689071770312476) * 10 ^ 70 +
        9695732058912720511873459832424764671522321112952943390827333390351550) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (137 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_137_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (138 + x) *
        remainder4Coefficient1.coeff (138 - (138 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 138 + x
  · rw [recurrence4LeadingSquare_coeff_high (138 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (138 - (138 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_138 :
    recurrence4Scalar1Left.coeff 138 =
      ((((39471422123477837227756848367768570976631748109463343824437 * 10 ^ 70 +
        7623976770720330407088834248897095885235857573818738750399202199132442) * 10 ^ 70 +
        9175645313439270123359122532777108464088636354694085542526156679039393) * 10 ^ 70 +
        9751525819691938071595650407026855596294201102043114864171132600586175) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (138 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_138_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (139 + x) *
        remainder4Coefficient1.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 139 + x
  · rw [recurrence4LeadingSquare_coeff_high (139 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (139 - (139 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_139 :
    recurrence4Scalar1Left.coeff 139 =
      -((((211068477394068145201335917990235780962701742756185757339572 * 10 ^ 70 +
        6210116991021289063557811027915826761784511472062592733911270909492305) * 10 ^ 70 +
        4115475721753361424052085546373360933560734433556150405745484924040761) * 10 ^ 70 +
        5793384683995923449795281582540360672250157650341448429071369041776038) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (139 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (140 + x) *
        remainder4Coefficient1.coeff (140 - (140 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 140 + x
  · rw [recurrence4LeadingSquare_coeff_high (140 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (140 - (140 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_140 :
    recurrence4Scalar1Left.coeff 140 =
      ((((1108202395047440006986964287974530885550475448590885941212739 * 10 ^ 70 +
        6647964515239709201609479291328908754435628812301887242549460817323806) * 10 ^ 70 +
        8357685028716384396105576428053511575769313530647340001686943995910250) * 10 ^ 70 +
        3125549513819604985669902169926263775201767193257958461272984095366608) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (140 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (141 + x) *
        remainder4Coefficient1.coeff (141 - (141 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 141 + x
  · rw [recurrence4LeadingSquare_coeff_high (141 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (141 - (141 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_141 :
    recurrence4Scalar1Left.coeff 141 =
      -((((5713904628745579487679880378653370690579722667581277769481000 * 10 ^ 70 +
        2107084555043936216457602081016290478707187521134807767715897167021718) * 10 ^ 70 +
        7577923332404685496596971814593054342570673533642860089911499084574205) * 10 ^ 70 +
        1546884602230452653294762802553214219919361014729312094633859754991924) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (141 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (142 + x) *
        remainder4Coefficient1.coeff (142 - (142 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 142 + x
  · rw [recurrence4LeadingSquare_coeff_high (142 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (142 - (142 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_142 :
    recurrence4Scalar1Left.coeff 142 =
      ((((28935192917495262722649811512245059555039439558953041554768845 * 10 ^ 70 +
        9424786605040892914284566903250371540724921614294155951948914486607839) * 10 ^ 70 +
        1460079470788775490300366721093587425052132773358695805140971065328013) * 10 ^ 70 +
        1406169508639045197041270430415690759138307787499084653800020492171881) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (142 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (143 + x) *
        remainder4Coefficient1.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 143 + x
  · rw [recurrence4LeadingSquare_coeff_high (143 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (143 - (143 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_143 :
    recurrence4Scalar1Left.coeff 143 =
      -((((143932488174961270478544881182549441310327954436638380990806134 * 10 ^ 70 +
        4624350111609449115579532657180148027647887506539819853131005863826140) * 10 ^ 70 +
        1539168744434189141795854880018382607912636946322684784207428983738224) * 10 ^ 70 +
        1217871795681462709661542979013418607458243470754097336298535246202252) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (143 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (144 + x) *
        remainder4Coefficient1.coeff (144 - (144 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 144 + x
  · rw [recurrence4LeadingSquare_coeff_high (144 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (144 - (144 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_144 :
    recurrence4Scalar1Left.coeff 144 =
      ((((703377107665657374750520656955736560519087885586638954207180399 * 10 ^ 70 +
        0368719100433791274736913915003165974948543656350580699233105847261142) * 10 ^ 70 +
        1539709072976292939995149949564844853269030967684313971901772260908048) * 10 ^ 70 +
        1523267959009883751771142100270456748047320911392762656456598024619638) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (144 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (145 + x) *
        remainder4Coefficient1.coeff (145 - (145 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 145 + x
  · rw [recurrence4LeadingSquare_coeff_high (145 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (145 - (145 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_145 :
    recurrence4Scalar1Left.coeff 145 =
      -((((3377309344523401663786701520981810798711347744734241551753540277 * 10 ^ 70 +
        8957010814979120685767647816291671050064954342291495397477804139769639) * 10 ^ 70 +
        9642129291452390692006061683399237701205967643483707493525775137279099) * 10 ^ 70 +
        9341178807045647488961017793904807973188966272105755812659269328515583) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (145 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (146 + x) *
        remainder4Coefficient1.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 146 + x
  · rw [recurrence4LeadingSquare_coeff_high (146 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (146 - (146 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_146 :
    recurrence4Scalar1Left.coeff 146 =
      ((((15935341394096552146299900493446153239108982967401328701351865084 * 10 ^ 70 +
        8693627957825815273674252891818377366814663493505768066362512292901594) * 10 ^ 70 +
        9892627443520054489229291485337963663520244460011417213182549506413780) * 10 ^ 70 +
        4494280286932599355252484480405385775305496066654320425595822037636760) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (146 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (147 + x) *
        remainder4Coefficient1.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 147 + x
  · rw [recurrence4LeadingSquare_coeff_high (147 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (147 - (147 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_147 :
    recurrence4Scalar1Left.coeff 147 =
      -((((73894651373416678683881211397959528346336996650033823645041323556 * 10 ^ 70 +
        5370772859540863891406745742221514835888496374751688888503344009292636) * 10 ^ 70 +
        6403205576056386847023482847206632226019434153753083872797712078396369) * 10 ^ 70 +
        9256163730753095070241418309444079596888236369883484032188701019729766) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (147 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (148 + x) *
        remainder4Coefficient1.coeff (148 - (148 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 148 + x
  · rw [recurrence4LeadingSquare_coeff_high (148 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (148 - (148 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_148 :
    recurrence4Scalar1Left.coeff 148 =
      ((((336804161931148420131586833911315848036549652301928724522864163409 * 10 ^ 70 +
        3985863481735741119027499304633034603045944327108810639627045434193267) * 10 ^ 70 +
        6808380569003805656034701073055723761773901215909321469291771715495301) * 10 ^ 70 +
        4345382973190821802322088531780476339494667603864164478085207918403533) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (148 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (149 + x) *
        remainder4Coefficient1.coeff (149 - (149 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 149 + x
  · rw [recurrence4LeadingSquare_coeff_high (149 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (149 - (149 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_149 :
    recurrence4Scalar1Left.coeff 149 =
      -((((1509054720260841208263187787473781710677553240613316285979151733008 * 10 ^ 70 +
        4364095839207659815100436651339291346055714811451666712666701791724773) * 10 ^ 70 +
        0690232480605690455529143479063826324972563328986142373798579700174849) * 10 ^ 70 +
        7389841626661889935065914359455396696155174087721670251025678746555943) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (149 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (150 + x) *
        remainder4Coefficient1.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 150 + x
  · rw [recurrence4LeadingSquare_coeff_high (150 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (150 - (150 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_150 :
    recurrence4Scalar1Left.coeff 150 =
      ((((6647288275614925320626216414137719142167393854878810043228616677496 * 10 ^ 70 +
        1360130066434089777867590764691546671458874116101073002962780745874778) * 10 ^ 70 +
        8948206810980498162635453760884451368822048136424553936914174765009060) * 10 ^ 70 +
        5690223142803018246383251672461531674877719405759733935875881158565783) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (150 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (151 + x) *
        remainder4Coefficient1.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 151 + x
  · rw [recurrence4LeadingSquare_coeff_high (151 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (151 - (151 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_151 :
    recurrence4Scalar1Left.coeff 151 =
      -((((28790126248783433606524145756121366587494177432723155402748977105958 * 10 ^ 70 +
        1494724753717649529803927807364370539221293130291807880031782330286375) * 10 ^ 70 +
        4392197991623570186543050591384478763424803778018697637955247037140782) * 10 ^ 70 +
        2134172104182089725678232243613376062200848474450193674497244905107460) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (151 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (152 + x) *
        remainder4Coefficient1.coeff (152 - (152 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 152 + x
  · rw [recurrence4LeadingSquare_coeff_high (152 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (152 - (152 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_152 :
    recurrence4Scalar1Left.coeff 152 =
      ((((122616351217856780084763026543665285998430570631579741267111811155479 * 10 ^ 70 +
        7493818085646216693077783306269043229268195971546670238482302513788678) * 10 ^ 70 +
        0034399598784700607843613487449538316808516364878775197576279761938643) * 10 ^ 70 +
        9619206339622846039101404864517374095201315703289396235557731142381545) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (152 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (153 + x) *
        remainder4Coefficient1.coeff (153 - (153 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 153 + x
  · rw [recurrence4LeadingSquare_coeff_high (153 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (153 - (153 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_153 :
    recurrence4Scalar1Left.coeff 153 =
      -((((513575061846461407439514731207279549554656355659186499926850466038053 * 10 ^ 70 +
        0637647947531651381963642607165214524287709916470505964204353808178517) * 10 ^ 70 +
        1491044139492316830112537063328169339984069195529430861880192312549660) * 10 ^ 70 +
        4401316339682256266011063623110058484554790539396587046500665221130487) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (153 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (154 + x) *
        remainder4Coefficient1.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 154 + x
  · rw [recurrence4LeadingSquare_coeff_high (154 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (154 - (154 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_154 :
    recurrence4Scalar1Left.coeff 154 =
      ((((2115699094989533225165478861583546909537321939865621631356731537201462 * 10 ^ 70 +
        6191655394902801391793638496953571634800693465998600129966647168725898) * 10 ^ 70 +
        6468815086407716599975943094194293533009665420986429559478361939871887) * 10 ^ 70 +
        4818819344018549460644760216725868025405391482030393073211866037288257) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (154 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (155 + x) *
        remainder4Coefficient1.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 155 + x
  · rw [recurrence4LeadingSquare_coeff_high (155 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (155 - (155 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_155 :
    recurrence4Scalar1Left.coeff 155 =
      -((((8573157715465033042180239794756596250774418719755672785759979926660745 * 10 ^ 70 +
        6051111755659961187590030982535822869950934246476187414335456685919625) * 10 ^ 70 +
        3563609482355274962038260558053508539709121654472196233287489355294741) * 10 ^ 70 +
        3630104818890341964500423741313522401828606468182916680644315213084489) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (155 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (156 + x) *
        remainder4Coefficient1.coeff (156 - (156 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 156 + x
  · rw [recurrence4LeadingSquare_coeff_high (156 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (156 - (156 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_156 :
    recurrence4Scalar1Left.coeff 156 =
      (((((3 * 10 ^ 70 +
        4174800922734981182965463450735471776805296053441893751308003716819026) * 10 ^ 70 +
        5474295502728210318866366456314982787759068644793513876753793040462671) * 10 ^ 70 +
        1937460715867705960172304585509997810698850599888470333062833476948166) * 10 ^ 70 +
        8751146924034491321392950273920409981921977937305355211054346960174327) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (156 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (157 + x) *
        remainder4Coefficient1.coeff (157 - (157 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 157 + x
  · rw [recurrence4LeadingSquare_coeff_high (157 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (157 - (157 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_157 :
    recurrence4Scalar1Left.coeff 157 =
      -(((((13 * 10 ^ 70 +
        4026173858778127588761980981574403366284862594866075354133606495674612) * 10 ^ 70 +
        3172283854523659335376845722457755566500936925999046079265860582650222) * 10 ^ 70 +
        8167432739138624529723963619679060814507415965964755014356715021187815) * 10 ^ 70 +
        3693126540558433362953535160300824351735073162889594247005260485409478) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (157 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (158 + x) *
        remainder4Coefficient1.coeff (158 - (158 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 158 + x
  · rw [recurrence4LeadingSquare_coeff_high (158 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (158 - (158 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_158 :
    recurrence4Scalar1Left.coeff 158 =
      (((((51 * 10 ^ 70 +
        7166936328631962922708342752439466420729432430051665559925976502627964) * 10 ^ 70 +
        1026522102086042207219422163685795682642144598002203006596680901571580) * 10 ^ 70 +
        3955639605157031808355620522813620373025171224562947572424656352854885) * 10 ^ 70 +
        0889634079686815127019649975942196563689124972887540949333123086590920) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (158 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (159 + x) *
        remainder4Coefficient1.coeff (159 - (159 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 159 + x
  · rw [recurrence4LeadingSquare_coeff_high (159 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (159 - (159 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_159 :
    recurrence4Scalar1Left.coeff 159 =
      -(((((196 * 10 ^ 70 +
        3664807839383566866539888602367568308140981094587611475773773799724209) * 10 ^ 70 +
        5201455631795481236369835759205044187255448445185228493473350033753577) * 10 ^ 70 +
        4924263176646624013656637084150383017588825502364581795488243396531328) * 10 ^ 70 +
        2699308228407021637338368529969161575771804140567082319741558854943731) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (159 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (160 + x) *
        remainder4Coefficient1.coeff (160 - (160 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 160 + x
  · rw [recurrence4LeadingSquare_coeff_high (160 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (160 - (160 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_160 :
    recurrence4Scalar1Left.coeff 160 =
      (((((733 * 10 ^ 70 +
        7301031123220794522986366477019237897598305365485907893024029835872056) * 10 ^ 70 +
        0627348515824885590022455673822888456550941776212385587543911682181532) * 10 ^ 70 +
        9724442063468040282407289710674440584096900918787203333967780506631034) * 10 ^ 70 +
        3254088603400413924567211762875668142709611665979742797257663351117083) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (160 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (161 + x) *
        remainder4Coefficient1.coeff (161 - (161 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 161 + x
  · rw [recurrence4LeadingSquare_coeff_high (161 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (161 - (161 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_161 :
    recurrence4Scalar1Left.coeff 161 =
      -(((((2698 * 10 ^ 70 +
        1963799780767528004897909398985686593249658446515735058012099542678176) * 10 ^ 70 +
        7177136355199734052016703610812792032559515952513718129203553113160546) * 10 ^ 70 +
        8577146315254621348328623077639921995550893592433708962533024370488360) * 10 ^ 70 +
        9344502120157696401102763121573963063662334789747510607889702104606259) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (161 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (162 + x) *
        remainder4Coefficient1.coeff (162 - (162 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 162 + x
  · rw [recurrence4LeadingSquare_coeff_high (162 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (162 - (162 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_162 :
    recurrence4Scalar1Left.coeff 162 =
      (((((9765 * 10 ^ 70 +
        9356167476377851770820528171046157378007860059686520229685329202770280) * 10 ^ 70 +
        5536992070057220132941370990691628345360557054557096736194136207860322) * 10 ^ 70 +
        5258075204680635428809434206875360895680146121963255727510200588341087) * 10 ^ 70 +
        9904303404972139596744935386496663529035057748446106311019740896593142) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (162 - x)) = _
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
  rw [recurrence4Scalar1Left_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
