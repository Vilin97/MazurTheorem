/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C0_coeff_1
  recurrence4C0_coeff_10
  recurrence4C0_coeff_100
  recurrence4C0_coeff_101
  recurrence4C0_coeff_102
  recurrence4C0_coeff_103
  recurrence4C0_coeff_104
  recurrence4C0_coeff_105
  recurrence4C0_coeff_106
  recurrence4C0_coeff_107
  recurrence4C0_coeff_108
  recurrence4C0_coeff_109
  recurrence4C0_coeff_11
  recurrence4C0_coeff_110
  recurrence4C0_coeff_111
  recurrence4C0_coeff_112
  recurrence4C0_coeff_113
  recurrence4C0_coeff_114
  recurrence4C0_coeff_115
  recurrence4C0_coeff_116
  recurrence4C0_coeff_117
  recurrence4C0_coeff_118
  recurrence4C0_coeff_119
  recurrence4C0_coeff_12
  recurrence4C0_coeff_120
  recurrence4C0_coeff_121
  recurrence4C0_coeff_122
  recurrence4C0_coeff_123
  recurrence4C0_coeff_124
  recurrence4C0_coeff_125
  recurrence4C0_coeff_126
  recurrence4C0_coeff_127
  recurrence4C0_coeff_128
  recurrence4C0_coeff_129
  recurrence4C0_coeff_13
  recurrence4C0_coeff_130
  recurrence4C0_coeff_131
  recurrence4C0_coeff_132
  recurrence4C0_coeff_133
  recurrence4C0_coeff_134
  recurrence4C0_coeff_135
  recurrence4C0_coeff_136
  recurrence4C0_coeff_137
  recurrence4C0_coeff_138
  recurrence4C0_coeff_139
  recurrence4C0_coeff_14
  recurrence4C0_coeff_140
  recurrence4C0_coeff_141
  recurrence4C0_coeff_142
  recurrence4C0_coeff_143
  recurrence4C0_coeff_144
  recurrence4C0_coeff_145
  recurrence4C0_coeff_146
  recurrence4C0_coeff_147
  recurrence4C0_coeff_148
  recurrence4C0_coeff_149
  recurrence4C0_coeff_15
  recurrence4C0_coeff_150
  recurrence4C0_coeff_151
  recurrence4C0_coeff_152
  recurrence4C0_coeff_153
  recurrence4C0_coeff_16
  recurrence4C0_coeff_17
  recurrence4C0_coeff_18

attribute [local simp]
  recurrence4C0_coeff_19
  recurrence4C0_coeff_2
  recurrence4C0_coeff_20
  recurrence4C0_coeff_21
  recurrence4C0_coeff_22
  recurrence4C0_coeff_23
  recurrence4C0_coeff_24
  recurrence4C0_coeff_25
  recurrence4C0_coeff_26
  recurrence4C0_coeff_27
  recurrence4C0_coeff_28
  recurrence4C0_coeff_29
  recurrence4C0_coeff_3
  recurrence4C0_coeff_30
  recurrence4C0_coeff_31
  recurrence4C0_coeff_32
  recurrence4C0_coeff_33
  recurrence4C0_coeff_34
  recurrence4C0_coeff_35
  recurrence4C0_coeff_36
  recurrence4C0_coeff_37
  recurrence4C0_coeff_38
  recurrence4C0_coeff_39
  recurrence4C0_coeff_4
  recurrence4C0_coeff_40
  recurrence4C0_coeff_41
  recurrence4C0_coeff_42
  recurrence4C0_coeff_43
  recurrence4C0_coeff_44
  recurrence4C0_coeff_45
  recurrence4C0_coeff_46
  recurrence4C0_coeff_47
  recurrence4C0_coeff_48
  recurrence4C0_coeff_49
  recurrence4C0_coeff_5
  recurrence4C0_coeff_50
  recurrence4C0_coeff_51
  recurrence4C0_coeff_52
  recurrence4C0_coeff_53
  recurrence4C0_coeff_54
  recurrence4C0_coeff_55
  recurrence4C0_coeff_56
  recurrence4C0_coeff_57
  recurrence4C0_coeff_58
  recurrence4C0_coeff_59
  recurrence4C0_coeff_6
  recurrence4C0_coeff_60
  recurrence4C0_coeff_61
  recurrence4C0_coeff_62
  recurrence4C0_coeff_63
  recurrence4C0_coeff_64
  recurrence4C0_coeff_65
  recurrence4C0_coeff_66
  recurrence4C0_coeff_67
  recurrence4C0_coeff_68
  recurrence4C0_coeff_69
  recurrence4C0_coeff_7
  recurrence4C0_coeff_70
  recurrence4C0_coeff_71
  recurrence4C0_coeff_72
  recurrence4C0_coeff_73
  recurrence4C0_coeff_74
  recurrence4C0_coeff_75
  recurrence4C0_coeff_76

attribute [local simp]
  recurrence4C0_coeff_77
  recurrence4C0_coeff_78
  recurrence4C0_coeff_79
  recurrence4C0_coeff_8
  recurrence4C0_coeff_80
  recurrence4C0_coeff_81
  recurrence4C0_coeff_82
  recurrence4C0_coeff_83
  recurrence4C0_coeff_84
  recurrence4C0_coeff_85
  recurrence4C0_coeff_86
  recurrence4C0_coeff_87
  recurrence4C0_coeff_88
  recurrence4C0_coeff_89
  recurrence4C0_coeff_9
  recurrence4C0_coeff_90
  recurrence4C0_coeff_91
  recurrence4C0_coeff_92
  recurrence4C0_coeff_93
  recurrence4C0_coeff_94
  recurrence4C0_coeff_95
  recurrence4C0_coeff_96
  recurrence4C0_coeff_97
  recurrence4C0_coeff_98
  recurrence4C0_coeff_99
  recurrence4ExceptionalProduct_coeff_0
  recurrence4ExceptionalProduct_coeff_1
  recurrence4ExceptionalProduct_coeff_10
  recurrence4ExceptionalProduct_coeff_100
  recurrence4ExceptionalProduct_coeff_101
  recurrence4ExceptionalProduct_coeff_102
  recurrence4ExceptionalProduct_coeff_103
  recurrence4ExceptionalProduct_coeff_104
  recurrence4ExceptionalProduct_coeff_105
  recurrence4ExceptionalProduct_coeff_106
  recurrence4ExceptionalProduct_coeff_107
  recurrence4ExceptionalProduct_coeff_108
  recurrence4ExceptionalProduct_coeff_109
  recurrence4ExceptionalProduct_coeff_11
  recurrence4ExceptionalProduct_coeff_110
  recurrence4ExceptionalProduct_coeff_111
  recurrence4ExceptionalProduct_coeff_112
  recurrence4ExceptionalProduct_coeff_113
  recurrence4ExceptionalProduct_coeff_114
  recurrence4ExceptionalProduct_coeff_115
  recurrence4ExceptionalProduct_coeff_116
  recurrence4ExceptionalProduct_coeff_117
  recurrence4ExceptionalProduct_coeff_118
  recurrence4ExceptionalProduct_coeff_119
  recurrence4ExceptionalProduct_coeff_12
  recurrence4ExceptionalProduct_coeff_120
  recurrence4ExceptionalProduct_coeff_121
  recurrence4ExceptionalProduct_coeff_122
  recurrence4ExceptionalProduct_coeff_123
  recurrence4ExceptionalProduct_coeff_124
  recurrence4ExceptionalProduct_coeff_125
  recurrence4ExceptionalProduct_coeff_126
  recurrence4ExceptionalProduct_coeff_127
  recurrence4ExceptionalProduct_coeff_128
  recurrence4ExceptionalProduct_coeff_129
  recurrence4ExceptionalProduct_coeff_13
  recurrence4ExceptionalProduct_coeff_130
  recurrence4ExceptionalProduct_coeff_131
  recurrence4ExceptionalProduct_coeff_132

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139
  recurrence4ExceptionalProduct_coeff_14
  recurrence4ExceptionalProduct_coeff_140
  recurrence4ExceptionalProduct_coeff_141
  recurrence4ExceptionalProduct_coeff_142
  recurrence4ExceptionalProduct_coeff_143
  recurrence4ExceptionalProduct_coeff_144
  recurrence4ExceptionalProduct_coeff_145
  recurrence4ExceptionalProduct_coeff_146
  recurrence4ExceptionalProduct_coeff_147
  recurrence4ExceptionalProduct_coeff_148
  recurrence4ExceptionalProduct_coeff_149
  recurrence4ExceptionalProduct_coeff_15
  recurrence4ExceptionalProduct_coeff_150
  recurrence4ExceptionalProduct_coeff_151
  recurrence4ExceptionalProduct_coeff_152
  recurrence4ExceptionalProduct_coeff_153
  recurrence4ExceptionalProduct_coeff_154
  recurrence4ExceptionalProduct_coeff_155
  recurrence4ExceptionalProduct_coeff_156
  recurrence4ExceptionalProduct_coeff_157
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_16
  recurrence4ExceptionalProduct_coeff_17
  recurrence4ExceptionalProduct_coeff_18
  recurrence4ExceptionalProduct_coeff_19
  recurrence4ExceptionalProduct_coeff_2
  recurrence4ExceptionalProduct_coeff_20
  recurrence4ExceptionalProduct_coeff_21
  recurrence4ExceptionalProduct_coeff_22
  recurrence4ExceptionalProduct_coeff_23
  recurrence4ExceptionalProduct_coeff_24
  recurrence4ExceptionalProduct_coeff_25
  recurrence4ExceptionalProduct_coeff_26
  recurrence4ExceptionalProduct_coeff_27
  recurrence4ExceptionalProduct_coeff_28
  recurrence4ExceptionalProduct_coeff_29
  recurrence4ExceptionalProduct_coeff_3
  recurrence4ExceptionalProduct_coeff_30
  recurrence4ExceptionalProduct_coeff_31
  recurrence4ExceptionalProduct_coeff_32
  recurrence4ExceptionalProduct_coeff_33
  recurrence4ExceptionalProduct_coeff_34
  recurrence4ExceptionalProduct_coeff_35
  recurrence4ExceptionalProduct_coeff_36
  recurrence4ExceptionalProduct_coeff_37
  recurrence4ExceptionalProduct_coeff_38
  recurrence4ExceptionalProduct_coeff_39
  recurrence4ExceptionalProduct_coeff_4
  recurrence4ExceptionalProduct_coeff_40
  recurrence4ExceptionalProduct_coeff_41
  recurrence4ExceptionalProduct_coeff_42
  recurrence4ExceptionalProduct_coeff_43
  recurrence4ExceptionalProduct_coeff_44
  recurrence4ExceptionalProduct_coeff_45
  recurrence4ExceptionalProduct_coeff_46
  recurrence4ExceptionalProduct_coeff_47

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_48
  recurrence4ExceptionalProduct_coeff_49
  recurrence4ExceptionalProduct_coeff_5
  recurrence4ExceptionalProduct_coeff_50
  recurrence4ExceptionalProduct_coeff_51
  recurrence4ExceptionalProduct_coeff_52
  recurrence4ExceptionalProduct_coeff_53
  recurrence4ExceptionalProduct_coeff_54
  recurrence4ExceptionalProduct_coeff_55
  recurrence4ExceptionalProduct_coeff_56
  recurrence4ExceptionalProduct_coeff_57
  recurrence4ExceptionalProduct_coeff_58
  recurrence4ExceptionalProduct_coeff_59
  recurrence4ExceptionalProduct_coeff_6
  recurrence4ExceptionalProduct_coeff_60
  recurrence4ExceptionalProduct_coeff_61
  recurrence4ExceptionalProduct_coeff_62
  recurrence4ExceptionalProduct_coeff_63
  recurrence4ExceptionalProduct_coeff_64
  recurrence4ExceptionalProduct_coeff_65
  recurrence4ExceptionalProduct_coeff_66
  recurrence4ExceptionalProduct_coeff_67
  recurrence4ExceptionalProduct_coeff_68
  recurrence4ExceptionalProduct_coeff_69
  recurrence4ExceptionalProduct_coeff_7
  recurrence4ExceptionalProduct_coeff_70
  recurrence4ExceptionalProduct_coeff_71
  recurrence4ExceptionalProduct_coeff_72
  recurrence4ExceptionalProduct_coeff_73
  recurrence4ExceptionalProduct_coeff_74
  recurrence4ExceptionalProduct_coeff_75
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_8
  recurrence4ExceptionalProduct_coeff_80
  recurrence4ExceptionalProduct_coeff_81
  recurrence4ExceptionalProduct_coeff_82
  recurrence4ExceptionalProduct_coeff_83
  recurrence4ExceptionalProduct_coeff_84
  recurrence4ExceptionalProduct_coeff_85
  recurrence4ExceptionalProduct_coeff_86
  recurrence4ExceptionalProduct_coeff_87
  recurrence4ExceptionalProduct_coeff_88
  recurrence4ExceptionalProduct_coeff_89
  recurrence4ExceptionalProduct_coeff_9
  recurrence4ExceptionalProduct_coeff_90
  recurrence4ExceptionalProduct_coeff_91
  recurrence4ExceptionalProduct_coeff_92
  recurrence4ExceptionalProduct_coeff_93
  recurrence4ExceptionalProduct_coeff_94
  recurrence4ExceptionalProduct_coeff_95
  recurrence4ExceptionalProduct_coeff_96
  recurrence4ExceptionalProduct_coeff_97
  recurrence4ExceptionalProduct_coeff_98
  recurrence4ExceptionalProduct_coeff_99

private theorem recurrence4Scalar0Exceptional_coeff_0_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (x) *
        remainder6Coefficient0.coeff (0 - (x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < x
  · rw [recurrence4ExceptionalProduct_coeff_high (x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (0 - (x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_0 :
    recurrence4Scalar0Exceptional.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_0_suffix_zero]

private theorem recurrence4Scalar0Exceptional_coeff_1_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (1 + x) *
        remainder6Coefficient0.coeff (1 - (1 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 1 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (1 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (1 - (1 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_1 :
    recurrence4Scalar0Exceptional.coeff 1 =
      (-520207759061720837503698646314245381652480 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_1_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_2_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (2 + x) *
        remainder6Coefficient0.coeff (2 - (2 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 2 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (2 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (2 - (2 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_2 :
    recurrence4Scalar0Exceptional.coeff 2 =
      (-80176542757117106762179335791982722411384832 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_2_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_3_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (3 + x) *
        remainder6Coefficient0.coeff (3 - (3 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 3 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (3 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (3 - (3 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_3 :
    recurrence4Scalar0Exceptional.coeff 3 =
      (7961147542114361054198652697380472650249405126144 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_3_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_4_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (4 + x) *
        remainder6Coefficient0.coeff (4 - (4 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 4 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (4 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (4 - (4 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_4 :
    recurrence4Scalar0Exceptional.coeff 4 =
      (-12801194048176919542111208667830225225028952357272512 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_4_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_5_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (5 + x) *
        remainder6Coefficient0.coeff (5 - (5 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 5 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (5 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (5 - (5 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_5 :
    recurrence4Scalar0Exceptional.coeff 5 =
      (-5520403742575209328650660587654629536331870853915396544 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_5_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_6_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (6 + x) *
        remainder6Coefficient0.coeff (6 - (6 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 6 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (6 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (6 - (6 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_6 :
    recurrence4Scalar0Exceptional.coeff 6 =
      (33530218742111736651421207990495574509455974168370039199120 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_6_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_7_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (7 + x) *
        remainder6Coefficient0.coeff (7 - (7 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 7 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (7 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (7 - (7 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_7 :
    recurrence4Scalar0Exceptional.coeff 7 =
      (-50199140861999302147275019955366394763475201792088084165846432 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_7_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_8_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (8 + x) *
        remainder6Coefficient0.coeff (8 - (8 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 8 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (8 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (8 - (8 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_8 :
    recurrence4Scalar0Exceptional.coeff 8 =
      (26514014125175591585847043581688762618568900223235024741260478128 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_8_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_9_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (9 + x) *
        remainder6Coefficient0.coeff (9 - (9 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 9 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (9 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (9 - (9 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_9 :
    recurrence4Scalar0Exceptional.coeff 9 =
      (38078434605379574503690368753091197852505409235973521824433340358288 : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_9_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_10_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (10 + x) *
        remainder6Coefficient0.coeff (10 - (10 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 10 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (10 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (10 - (10 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_10 :
    recurrence4Scalar0Exceptional.coeff 10 =
      -((7 * 10 ^ 70 +
        8088378031705371418900235995026675380881422563199849231252590033139404) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_10_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_11_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (11 + x) *
        remainder6Coefficient0.coeff (11 - (11 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 11 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (11 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (11 - (11 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_11 :
    recurrence4Scalar0Exceptional.coeff 11 =
      ((5889 * 10 ^ 70 +
        7590974963725579656367875526549456456417606980729726296870141325907372) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_11_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_12_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (12 + x) *
        remainder6Coefficient0.coeff (12 - (12 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 12 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (12 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (12 - (12 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_12 :
    recurrence4Scalar0Exceptional.coeff 12 =
      -((1867539 * 10 ^ 70 +
        2879740424231012241855419224200156981258868587951461576389814211313404) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_12_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_13_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (13 + x) *
        remainder6Coefficient0.coeff (13 - (13 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 13 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (13 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (13 - (13 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_13 :
    recurrence4Scalar0Exceptional.coeff 13 =
      -((381161618 * 10 ^ 70 +
        4073194077384950599684051376179751211805845382607313557055410729404252) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_13_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_14_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (14 + x) *
        remainder6Coefficient0.coeff (14 - (14 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 14 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (14 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (14 - (14 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_14 :
    recurrence4Scalar0Exceptional.coeff 14 =
      ((682788897301 * 10 ^ 70 +
        7256503094986888669003509766355207939527316868446153739773097347506700) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_14_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_15_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (15 + x) *
        remainder6Coefficient0.coeff (15 - (15 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 15 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (15 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (15 - (15 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_15 :
    recurrence4Scalar0Exceptional.coeff 15 =
      -((351393870647453 * 10 ^ 70 +
        9731086702925604070396315386998651738576175110177623566247188279685979) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_15_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_16_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (16 + x) *
        remainder6Coefficient0.coeff (16 - (16 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 16 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (16 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (16 - (16 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_16 :
    recurrence4Scalar0Exceptional.coeff 16 =
      ((107351713221657427 * 10 ^ 70 +
        6791535953583532252222833335777432987538157416510590889059539883377356) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_16_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_17_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (17 + x) *
        remainder6Coefficient0.coeff (17 - (17 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 17 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (17 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (17 - (17 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_17 :
    recurrence4Scalar0Exceptional.coeff 17 =
      -((21152975201580741871 * 10 ^ 70 +
        5814413149391047597812881034011418207508091282804225203184509557239954) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_17_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_18_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (18 + x) *
        remainder6Coefficient0.coeff (18 - (18 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 18 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (18 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (18 - (18 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_18 :
    recurrence4Scalar0Exceptional.coeff 18 =
      ((2763658319666791215866 * 10 ^ 70 +
        0505470502987526204821592027221924650250444710353239113750519708458024) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_18_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_19_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (19 + x) *
        remainder6Coefficient0.coeff (19 - (19 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 19 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (19 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (19 - (19 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_19 :
    recurrence4Scalar0Exceptional.coeff 19 =
      -((435600652392651983545068 * 10 ^ 70 +
        1231427253586183897503899490209229936263324109676094043975284478192051) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_19_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_20_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (20 + x) *
        remainder6Coefficient0.coeff (20 - (20 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 20 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (20 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (20 - (20 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_20 :
    recurrence4Scalar0Exceptional.coeff 20 =
      ((206548350768903331309212392 * 10 ^ 70 +
        1540405068086424849641222053720812534040004973765836898078274257708408) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_20_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_21_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (21 + x) *
        remainder6Coefficient0.coeff (21 - (21 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 21 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (21 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (21 - (21 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_21 :
    recurrence4Scalar0Exceptional.coeff 21 =
      -((98756117069683014351829614771 * 10 ^ 70 +
        4652716636665620078771253917969533505863432497185873739913974264137868) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_21_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_22_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (22 + x) *
        remainder6Coefficient0.coeff (22 - (22 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 22 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (22 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (22 - (22 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_22 :
    recurrence4Scalar0Exceptional.coeff 22 =
      ((34540428351588007439799560400830 * 10 ^ 70 +
        4565933162273888186926005429663181548059227097989813910375075864615717) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_22_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_23_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (23 + x) *
        remainder6Coefficient0.coeff (23 - (23 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 23 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (23 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (23 - (23 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_23 :
    recurrence4Scalar0Exceptional.coeff 23 =
      -((9438920235686930112885462199844789 * 10 ^ 70 +
        6117270026551532148116822382131761282521867823790160420977373026027136) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_23_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_24_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (24 + x) *
        remainder6Coefficient0.coeff (24 - (24 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 24 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (24 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (24 - (24 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_24 :
    recurrence4Scalar0Exceptional.coeff 24 =
      ((2153288870762470831329941345106312292 * 10 ^ 70 +
        3085715737107917926510752902377602021320668666822484905035332168767689) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_24_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_25_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (25 + x) *
        remainder6Coefficient0.coeff (25 - (25 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 25 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (25 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (25 - (25 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_25 :
    recurrence4Scalar0Exceptional.coeff 25 =
      -((436223623285231518760921764692154270836 * 10 ^ 70 +
        1235014854461778983534287337401935237387029216188977989745802552548425) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_25_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_26_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (26 + x) *
        remainder6Coefficient0.coeff (26 - (26 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 26 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (26 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (26 - (26 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_26 :
    recurrence4Scalar0Exceptional.coeff 26 =
      ((85308589667264456296586121640632088598884 * 10 ^ 70 +
        1722717205059666015790729762084669652993052791899557007433725880767302) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_26_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_27_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (27 + x) *
        remainder6Coefficient0.coeff (27 - (27 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 27 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (27 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (27 - (27 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_27 :
    recurrence4Scalar0Exceptional.coeff 27 =
      -((17864212162385331807100530429318875157818467 * 10 ^ 70 +
        3283890167782426384799810941226317898482693615806379191793766138297223) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_27_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_28_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (28 + x) *
        remainder6Coefficient0.coeff (28 - (28 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 28 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (28 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (28 - (28 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_28 :
    recurrence4Scalar0Exceptional.coeff 28 =
      ((4216484542978621509166777994940112718759735888 * 10 ^ 70 +
        2294223562647749604649028120019752731554972206464968465200835196129576) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_28_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_29_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (29 + x) *
        remainder6Coefficient0.coeff (29 - (29 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 29 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (29 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (29 - (29 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_29 :
    recurrence4Scalar0Exceptional.coeff 29 =
      -((1065068941892500341353103726367076112096551000644 * 10 ^ 70 +
        0882197606846034690695071686687109022605781378461883331404172922766948) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_29_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_30_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (30 + x) *
        remainder6Coefficient0.coeff (30 - (30 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 30 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (30 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (30 - (30 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_30 :
    recurrence4Scalar0Exceptional.coeff 30 =
      ((264891751482229119342980745841791758126832759908554 * 10 ^ 70 +
        9287536256857217037211552328557206757728444370818568023708990457933809) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_30_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_31_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (31 + x) *
        remainder6Coefficient0.coeff (31 - (31 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 31 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (31 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (31 - (31 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_31 :
    recurrence4Scalar0Exceptional.coeff 31 =
      -((61671945333902239425216298430576299217682844338557292 * 10 ^ 70 +
        1059082308721783497459510537646976140912087143172215027308962945497609) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_31_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_32_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (32 + x) *
        remainder6Coefficient0.coeff (32 - (32 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 32 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (32 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (32 - (32 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_32 :
    recurrence4Scalar0Exceptional.coeff 32 =
      ((13193424409608397521643211985922134701596282123832087685 * 10 ^ 70 +
        0940504341718331289283167590140660497867383068786505732287713362339040) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar0Exceptional_coeff_32_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_33_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (33 + x) *
        remainder6Coefficient0.coeff (33 - (33 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 33 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (33 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (33 - (33 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_33 :
    recurrence4Scalar0Exceptional.coeff 33 =
      -((2585334375682443882452108021140869923494642384845197120343 * 10 ^ 70 +
        7062822890168270781409448429452878240331058129682807028382060403126172) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (33 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_33_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_34_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (34 + x) *
        remainder6Coefficient0.coeff (34 - (34 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 34 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (34 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (34 - (34 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_34 :
    recurrence4Scalar0Exceptional.coeff 34 =
      ((465191423219745058396978941301826754598551312441439111247721 * 10 ^ 70 +
        3012880261249524398842066415079375136277838332391686190790776392888427) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (34 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_34_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_35_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (35 + x) *
        remainder6Coefficient0.coeff (35 - (35 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 35 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (35 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (35 - (35 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_35 :
    recurrence4Scalar0Exceptional.coeff 35 =
      -((77162201276148448092476666530483850562306014855252513403936333 * 10 ^ 70 +
        4587997893295084603846624871916951664945041167617786699263657340784056) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (35 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_35_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_36_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (36 + x) *
        remainder6Coefficient0.coeff (36 - (36 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 36 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (36 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (36 - (36 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_36 :
    recurrence4Scalar0Exceptional.coeff 36 =
      ((11845125820841697184480625823314288148460571398183830938961646839 * 10 ^ 70 +
        5737356756341130057565928563678682852855818171196995738263581012591045) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (36 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_36_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_37_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (37 + x) *
        remainder6Coefficient0.coeff (37 - (37 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 37 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (37 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (37 - (37 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_37 :
    recurrence4Scalar0Exceptional.coeff 37 =
      -((1688735341369468278219145111751542790942885963645757019385538129571 * 10 ^ 70 +
        5303962892000046369429198217584784601085316740475152078947039207746922) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (37 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_37_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_38_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (38 + x) *
        remainder6Coefficient0.coeff (38 - (38 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 38 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (38 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (38 - (38 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_38 :
    recurrence4Scalar0Exceptional.coeff 38 =
      ((224281521827640109383663902111286772731220405225302316452270274376065 * 10 ^ 70 +
        5348208267165183107536418196800062562222964419258318163227418837037896) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (38 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_38_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_39_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (39 + x) *
        remainder6Coefficient0.coeff (39 - (39 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 39 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (39 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (39 - (39 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_39 :
    recurrence4Scalar0Exceptional.coeff 39 =
      -(((2 * 10 ^ 70 +
        7821665225734128729565739333494579504811007389273236996895746104913617) * 10 ^ 70 +
        7526918627345612431375257452061433861304886753639630383970078626040770) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (39 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_39_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_40_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (40 + x) *
        remainder6Coefficient0.coeff (40 - (40 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 40 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (40 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (40 - (40 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_40 :
    recurrence4Scalar0Exceptional.coeff 40 =
      (((323 * 10 ^ 70 +
        1001619914652702783941897820370995271466392053862206061267599325030123) * 10 ^ 70 +
        1110233522375455859515763069718470803154730798542086753661648534684327) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (40 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_40_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_41_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (41 + x) *
        remainder6Coefficient0.coeff (41 - (41 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 41 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (41 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (41 - (41 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_41 :
    recurrence4Scalar0Exceptional.coeff 41 =
      -(((35200 * 10 ^ 70 +
        7111257103052931089307842289539771255790513090181890897051885411397996) * 10 ^ 70 +
        4731099370715565099685789332407522107678893658479843801985080622064380) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (41 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_41_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_42_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (42 + x) *
        remainder6Coefficient0.coeff (42 - (42 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 42 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (42 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (42 - (42 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_42 :
    recurrence4Scalar0Exceptional.coeff 42 =
      (((3604408 * 10 ^ 70 +
        9503123989017289245252357649343190634364047873430895822778896381411033) * 10 ^ 70 +
        1988267641841498199831558464241421904070751479122103516085301780930643) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (42 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_42_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_43_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (43 + x) *
        remainder6Coefficient0.coeff (43 - (43 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 43 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (43 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (43 - (43 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_43 :
    recurrence4Scalar0Exceptional.coeff 43 =
      -(((347474387 * 10 ^ 70 +
        4532705621303426310452548451302698937067204971918335670218603025552747) * 10 ^ 70 +
        0540983224264275163645803315248669599550716439772649932423004141124464) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (43 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_43_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_44_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (44 + x) *
        remainder6Coefficient0.coeff (44 - (44 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 44 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (44 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (44 - (44 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_44 :
    recurrence4Scalar0Exceptional.coeff 44 =
      (((31586215566 * 10 ^ 70 +
        5331071085941592412027978768100555710232040857022442025168349735208228) * 10 ^ 70 +
        7897726917879504057829043079033565969814048380847704464778395917006085) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (44 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_44_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_45_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (45 + x) *
        remainder6Coefficient0.coeff (45 - (45 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 45 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (45 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (45 - (45 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_45 :
    recurrence4Scalar0Exceptional.coeff 45 =
      -(((2711376670588 * 10 ^ 70 +
        7766674970859664948940897859816475138180093593689320879242537774980887) * 10 ^ 70 +
        9863618510994620105887003279107803583391914658043449105030048604753037) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (45 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_45_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_46_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (46 + x) *
        remainder6Coefficient0.coeff (46 - (46 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 46 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (46 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (46 - (46 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_46 :
    recurrence4Scalar0Exceptional.coeff 46 =
      (((220084480517894 * 10 ^ 70 +
        3240514343069003768699182103275080921562968747145442090086120250848523) * 10 ^ 70 +
        8876558758420633553153998047561005620373715443173810984161798492444560) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (46 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_46_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_47_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (47 + x) *
        remainder6Coefficient0.coeff (47 - (47 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 47 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (47 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (47 - (47 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_47 :
    recurrence4Scalar0Exceptional.coeff 47 =
      -(((16914140785099865 * 10 ^ 70 +
        6151500345344068458133946728711418940517545636636622559484648318464730) * 10 ^ 70 +
        7388428794918226742029287863799383890880238483454400940569244962349036) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (47 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_47_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_48_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (48 + x) *
        remainder6Coefficient0.coeff (48 - (48 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 48 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (48 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (48 - (48 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_48 :
    recurrence4Scalar0Exceptional.coeff 48 =
      (((1232233872464748121 * 10 ^ 70 +
        2355327385249283458514122012907148960961982410728404998257830907688867) * 10 ^ 70 +
        1281065424515729018243549248747063205754378504735424454097465058873613) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (48 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_48_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_49_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (49 + x) *
        remainder6Coefficient0.coeff (49 - (49 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 49 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (49 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (49 - (49 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_49 :
    recurrence4Scalar0Exceptional.coeff 49 =
      -(((85194637194791108494 * 10 ^ 70 +
        5374186753317969288665821514387011187066674985014986429022753035137463) * 10 ^ 70 +
        4705247031995855424673632632151772250937697646374430432805783024281442) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (49 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_49_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_50_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (50 + x) *
        remainder6Coefficient0.coeff (50 - (50 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 50 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (50 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (50 - (50 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_50 :
    recurrence4Scalar0Exceptional.coeff 50 =
      (((5595963595861903506149 * 10 ^ 70 +
        6808095799388765994557535291353526754942055208692736466800962906159422) * 10 ^ 70 +
        0403683556859317261472678533739141468831460051114365803508547861833440) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (50 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_50_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_51_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (51 + x) *
        remainder6Coefficient0.coeff (51 - (51 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 51 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (51 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (51 - (51 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_51 :
    recurrence4Scalar0Exceptional.coeff 51 =
      -(((349562920479708725967885 * 10 ^ 70 +
        5991566913408363993386527337672201553152925307229395136364161585589922) * 10 ^ 70 +
        8990049300172141455795008243656409395202809051938542229582294029605947) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (51 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_51_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_52_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (52 + x) *
        remainder6Coefficient0.coeff (52 - (52 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 52 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (52 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (52 - (52 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_52 :
    recurrence4Scalar0Exceptional.coeff 52 =
      (((20786761468580724511418346 * 10 ^ 70 +
        7195535166481780716556635336107797377550281392170000264871851536096751) * 10 ^ 70 +
        4680576152557908790081528083090120114046632555361084940619861743411449) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (52 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_52_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_53_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (53 + x) *
        remainder6Coefficient0.coeff (53 - (53 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 53 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (53 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (53 - (53 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_53 :
    recurrence4Scalar0Exceptional.coeff 53 =
      -(((1177776771419505277400289343 * 10 ^ 70 +
        6629065076235969295450068752143250011977851087683580513084095951293900) * 10 ^ 70 +
        5810142930056260124782951782022206374768375316799362029310259089033381) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (53 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_53_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_54_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (54 + x) *
        remainder6Coefficient0.coeff (54 - (54 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 54 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (54 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (54 - (54 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_54 :
    recurrence4Scalar0Exceptional.coeff 54 =
      (((63641376894588640449369544083 * 10 ^ 70 +
        6233935499525264677056820268775757338388195450736634485167825920823005) * 10 ^ 70 +
        4692658082364390204251028875065624884947695659645608539060907203151980) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (54 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_54_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_55_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (55 + x) *
        remainder6Coefficient0.coeff (55 - (55 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 55 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (55 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (55 - (55 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_55 :
    recurrence4Scalar0Exceptional.coeff 55 =
      -(((3282356358263433701131901728857 * 10 ^ 70 +
        6789180094513407835002980360750982940301969705232329676923919922570887) * 10 ^ 70 +
        6355028154140018215433888296221587540587720761135609495118356995384190) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (55 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_55_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_56_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (56 + x) *
        remainder6Coefficient0.coeff (56 - (56 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 56 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (56 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (56 - (56 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_56 :
    recurrence4Scalar0Exceptional.coeff 56 =
      (((161716819932414684983441521504609 * 10 ^ 70 +
        2996570670710797545929153329653867416826127896597711313268842039684150) * 10 ^ 70 +
        8901499206801120816282177242307270564395721878959645180161406592685808) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (56 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_56_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_57_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (57 + x) *
        remainder6Coefficient0.coeff (57 - (57 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 57 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (57 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (57 - (57 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_57 :
    recurrence4Scalar0Exceptional.coeff 57 =
      -(((7617058345935387686783732996418999 * 10 ^ 70 +
        0316720284892707678647552891132329412386414944867568145339427960046265) * 10 ^ 70 +
        1437104570630814274353950388088611068641043951110003413172192974681961) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (57 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_57_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_58_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (58 + x) *
        remainder6Coefficient0.coeff (58 - (58 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 58 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (58 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (58 - (58 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_58 :
    recurrence4Scalar0Exceptional.coeff 58 =
      (((343247870521302989136521601991284919 * 10 ^ 70 +
        3611121478402185809434309288329735465934390396877456337919248793432601) * 10 ^ 70 +
        2943338169451157828629522083581656871088931484628692969010955335942575) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (58 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_58_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_59_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (59 + x) *
        remainder6Coefficient0.coeff (59 - (59 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 59 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (59 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (59 - (59 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_59 :
    recurrence4Scalar0Exceptional.coeff 59 =
      -(((14809148933834455177826599277443376344 * 10 ^ 70 +
        3479128099772058016256568718552925683396174142038080346360038535826236) * 10 ^ 70 +
        9198694141909197938495721916606336872594397060888737929238834411613159) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (59 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_59_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_60_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (60 + x) *
        remainder6Coefficient0.coeff (60 - (60 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 60 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (60 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (60 - (60 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_60 :
    recurrence4Scalar0Exceptional.coeff 60 =
      (((612146416688732842009643733894807226954 * 10 ^ 70 +
        8612299626883818024616169473656866086395531611873493795183530882706730) * 10 ^ 70 +
        2875373824219128119295786553733903959739221502049559308836034824377101) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (60 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_60_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_61_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (61 + x) *
        remainder6Coefficient0.coeff (61 - (61 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 61 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (61 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (61 - (61 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_61 :
    recurrence4Scalar0Exceptional.coeff 61 =
      -(((24259034162506025664200675292035315660320 * 10 ^ 70 +
        6964623083375353139560878085741927073168040871360657540049424173586677) * 10 ^ 70 +
        6887331546545485136027519110276767610022988747254028900699363075124501) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (61 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_61_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_62_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (62 + x) *
        remainder6Coefficient0.coeff (62 - (62 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 62 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (62 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (62 - (62 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_62 :
    recurrence4Scalar0Exceptional.coeff 62 =
      (((922282649813951046883634269090954800067862 * 10 ^ 70 +
        6763171032819448189455867042740438600839141194371651994208860730948934) * 10 ^ 70 +
        9729337843416118362643494446385660185340618824563751410157684378180834) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (62 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_62_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_63_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (63 + x) *
        remainder6Coefficient0.coeff (63 - (63 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 63 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (63 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (63 - (63 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_63 :
    recurrence4Scalar0Exceptional.coeff 63 =
      -(((33658606320454981196020161826010052602980864 * 10 ^ 70 +
        5483338817762124619380023054311808468264023570198523347616084176195998) * 10 ^ 70 +
        3992369668439384291783119176372263288760507875835455360546481350890011) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (63 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_63_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_64_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (64 + x) *
        remainder6Coefficient0.coeff (64 - (64 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 64 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (64 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (64 - (64 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_64 :
    recurrence4Scalar0Exceptional.coeff 64 =
      (((1179856921726164767187212154188458853593581489 * 10 ^ 70 +
        5450831047937885355779156826262000549835364636546520067119068224845681) * 10 ^ 70 +
        6264522714952847168326550406504741017919300573242507772170366683638011) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (64 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_64_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_65_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (65 + x) *
        remainder6Coefficient0.coeff (65 - (65 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 65 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (65 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (65 - (65 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_65 :
    recurrence4Scalar0Exceptional.coeff 65 =
      -(((39747885475610179253634685263736703524895905778 * 10 ^ 70 +
        6982928377379042634257456995740231881704593454184418262739875479960631) * 10 ^ 70 +
        2688883127606174985901371451708507569652924637780635296964801617311590) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (65 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_65_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_66_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (66 + x) *
        remainder6Coefficient0.coeff (66 - (66 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 66 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (66 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (66 - (66 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_66 :
    recurrence4Scalar0Exceptional.coeff 66 =
      (((1287631817746898291629573669289252248064356498950 * 10 ^ 70 +
        4663456351236917916362730053671555386120405939352597944024666382851203) * 10 ^ 70 +
        5751475841919634922213302048673478641139717435309349670402142501349049) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (66 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_66_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_67_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (67 + x) *
        remainder6Coefficient0.coeff (67 - (67 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 67 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (67 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (67 - (67 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_67 :
    recurrence4Scalar0Exceptional.coeff 67 =
      -(((40132423759599084953651951389058069727417537013608 * 10 ^ 70 +
        3311747903974089186662195720248184441068409589585848256605134756352373) * 10 ^ 70 +
        1872788753036388123595121841494081939881522556296188402577441034456634) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (67 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_67_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_68_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (68 + x) *
        remainder6Coefficient0.coeff (68 - (68 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 68 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (68 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (68 - (68 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_68 :
    recurrence4Scalar0Exceptional.coeff 68 =
      (((1204065100480281950768999922628772473848259425999441 * 10 ^ 70 +
        7624855348512564865472950550516497257114683467290818937060116720751264) * 10 ^ 70 +
        3110562644208748047486866207127752633768339757954177202211280547383828) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (68 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_68_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_69_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (69 + x) *
        remainder6Coefficient0.coeff (69 - (69 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 69 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (69 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (69 - (69 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_69 :
    recurrence4Scalar0Exceptional.coeff 69 =
      -(((34791441519606895734383357350966221917624607465329379 * 10 ^ 70 +
        5208399345411074918132201560243931464910740551911737857853998339398189) * 10 ^ 70 +
        6978434597575996957717463404048551297651823051813369783026462358885233) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (69 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_69_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_70_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (70 + x) *
        remainder6Coefficient0.coeff (70 - (70 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 70 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (70 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (70 - (70 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_70 :
    recurrence4Scalar0Exceptional.coeff 70 =
      (((968661644964157465484115125646143255981671034545294826 * 10 ^ 70 +
        6599577115059319860691740005517191622773458948415896410805368969619617) * 10 ^ 70 +
        2996860021013661197325972142043059092801493166616641692613603157094009) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (70 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_70_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_71_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (71 + x) *
        remainder6Coefficient0.coeff (71 - (71 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 71 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (71 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (71 - (71 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_71 :
    recurrence4Scalar0Exceptional.coeff 71 =
      -(((25998658796832925715278496829716559037309868522699526249 * 10 ^ 70 +
        0064648396431940170887554479455087268721262741144066897347132783007490) * 10 ^ 70 +
        8089397696064933260918279633831720816391780266833584764670637165673570) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (71 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_71_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_72_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (72 + x) *
        remainder6Coefficient0.coeff (72 - (72 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 72 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (72 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (72 - (72 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_72 :
    recurrence4Scalar0Exceptional.coeff 72 =
      (((672982317371067603325056585667352433543750126799784420137 * 10 ^ 70 +
        3282804690160885803660932644984406292656635374120236658011768890557715) * 10 ^ 70 +
        3413932151877209648661299354708959482036595711215705471810819400341061) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (72 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_72_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_73_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (73 + x) *
        remainder6Coefficient0.coeff (73 - (73 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 73 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (73 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (73 - (73 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_73 :
    recurrence4Scalar0Exceptional.coeff 73 =
      -(((16808070990632138278344584469286408240073670451577045822331 * 10 ^ 70 +
        8999035033098124448105301266742204265499173426264107587134278923039215) * 10 ^ 70 +
        5055662687292603469598781402547918656455094401034623988849143737596370) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (73 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_73_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_74_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (74 + x) *
        remainder6Coefficient0.coeff (74 - (74 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 74 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (74 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (74 - (74 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_74 :
    recurrence4Scalar0Exceptional.coeff 74 =
      (((405204554204169743737263309349606827256694291334622046984371 * 10 ^ 70 +
        5215844235902207773368946641431006715795364071290144464181802162875384) * 10 ^ 70 +
        2215448018198927764156514469846700959068790612247262995885009098318425) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (74 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_74_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_75_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (75 + x) *
        remainder6Coefficient0.coeff (75 - (75 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 75 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (75 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (75 - (75 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_75 :
    recurrence4Scalar0Exceptional.coeff 75 =
      -(((9432935662313614019035721919410545651279849026654361087786420 * 10 ^ 70 +
        3366865941747471045749024105224935820119996422440907923044985836926568) * 10 ^ 70 +
        3325433954624746727541600224178570132301437802911292572471311684640569) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (75 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_75_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_76_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (76 + x) *
        remainder6Coefficient0.coeff (76 - (76 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 76 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (76 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (76 - (76 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_76 :
    recurrence4Scalar0Exceptional.coeff 76 =
      (((212130284673053924663427272551830532463549957757963797071454735 * 10 ^ 70 +
        9252845257173806445539313067880862239549892494538560302265286060390626) * 10 ^ 70 +
        7397420758848436045744399389527715694514737541601093807472796140888211) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (76 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_76_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_77_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (77 + x) *
        remainder6Coefficient0.coeff (77 - (77 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 77 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (77 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (77 - (77 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_77 :
    recurrence4Scalar0Exceptional.coeff 77 =
      -(((4610013120870488436566814875599416708853077248448451181870519639 * 10 ^ 70 +
        2422009524075026971274929150393538310665071934393110087869280916661568) * 10 ^ 70 +
        1476965544923806789744845376242790957550475281370358637087038359536915) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (77 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_77_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_78_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (78 + x) *
        remainder6Coefficient0.coeff (78 - (78 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 78 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (78 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (78 - (78 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_78 :
    recurrence4Scalar0Exceptional.coeff 78 =
      (((96849879236899181380831385389296606994785096059336310145920729811 * 10 ^ 70 +
        9521897975011486413573789532501069553333160236592249915057376599204736) * 10 ^ 70 +
        7770085344482570576971365826146514125896218097437632295877216252714787) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (78 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_78_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_79_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (79 + x) *
        remainder6Coefficient0.coeff (79 - (79 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 79 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (79 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (79 - (79 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_79 :
    recurrence4Scalar0Exceptional.coeff 79 =
      -(((1967616656153485874728920987866130491869060370208244566584389578925 * 10 ^ 70 +
        7748216144788349606782610331570203065342775299920644763086871763044885) * 10 ^ 70 +
        7625057696493482521739911687784466787490547894709000277127187090224476) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (79 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_79_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_80_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (80 + x) *
        remainder6Coefficient0.coeff (80 - (80 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 80 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (80 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (80 - (80 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_80 :
    recurrence4Scalar0Exceptional.coeff 80 =
      (((38669332611927934537202811088931894592266264206819527923180336663485 * 10 ^ 70 +
        6223560029458379792713502558410174027587243419533918536180679290028192) * 10 ^ 70 +
        3953563540934243300042456027851479898434122053482223085202804141696068) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (80 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_80_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_81_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (81 + x) *
        remainder6Coefficient0.coeff (81 - (81 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 81 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (81 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (81 - (81 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_81 :
    recurrence4Scalar0Exceptional.coeff 81 =
      -(((735378776984603477060225367470583534458945090309641771631133726954648 * 10 ^ 70 +
        0356605930414601687451041850302701042162468636093491890318894048550890) * 10 ^ 70 +
        8185046335344577479018789131017531353597307468315986852620735604111256) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (81 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_81_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_82_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (82 + x) *
        remainder6Coefficient0.coeff (82 - (82 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 82 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (82 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (82 - (82 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_82 :
    recurrence4Scalar0Exceptional.coeff 82 =
      ((((1 * 10 ^ 70 +
        3536307263594965893477809174490980976754265450736500279567945553418672) * 10 ^ 70 +
        4389027919848663167573947522069923561045750651759731303035760893452130) * 10 ^ 70 +
        8437032498430596456425382015215177733476896626219987148193306163187014) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (82 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_82_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_83_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (83 + x) *
        remainder6Coefficient0.coeff (83 - (83 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 83 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (83 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (83 - (83 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_83 :
    recurrence4Scalar0Exceptional.coeff 83 =
      -((((24 * 10 ^ 70 +
        1242219115969500515001054272428742902646905284179114294206075167855923) * 10 ^ 70 +
        8147505107129651909088850644500127658576287416518973475585828275586106) * 10 ^ 70 +
        9905025877270437828777313146024611134875993895409279057765523121936018) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (83 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_83_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_84_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (84 + x) *
        remainder6Coefficient0.coeff (84 - (84 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 84 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (84 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (84 - (84 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_84 :
    recurrence4Scalar0Exceptional.coeff 84 =
      ((((416 * 10 ^ 70 +
        3727704131541538608131814196223466660631496878586673010441409791545904) * 10 ^ 70 +
        1694519605617182085187712494729726147070582806486864620993351038399167) * 10 ^ 70 +
        8608486299112154835011591106397370948502512028438969656289704820234455) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (84 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_84_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_85_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (85 + x) *
        remainder6Coefficient0.coeff (85 - (85 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 85 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (85 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (85 - (85 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_85 :
    recurrence4Scalar0Exceptional.coeff 85 =
      -((((6961 * 10 ^ 70 +
        3168881799959264884877177433386500290203659217099271829462673171826427) * 10 ^ 70 +
        2093440955577691540651321335275753206335230064152803874794591903136800) * 10 ^ 70 +
        4574049415038506995911783208179519732577622788067721857889448440405340) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (85 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_85_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_86_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (86 + x) *
        remainder6Coefficient0.coeff (86 - (86 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 86 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (86 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (86 - (86 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_86 :
    recurrence4Scalar0Exceptional.coeff 86 =
      ((((112765 * 10 ^ 70 +
        6055090280336262157088035206282240914650059840335530891014649049073119) * 10 ^ 70 +
        6279400634252318135703328908511837922681529444196558658154552772563119) * 10 ^ 70 +
        7166000288377332299226165565700195145516100550527581571563119535330703) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (86 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_86_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_87_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (87 + x) *
        remainder6Coefficient0.coeff (87 - (87 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 87 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (87 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (87 - (87 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_87 :
    recurrence4Scalar0Exceptional.coeff 87 =
      -((((1770213 * 10 ^ 70 +
        3161947243527126430636690760590288102815255477853759196419070641985235) * 10 ^ 70 +
        3877398509296563667836092701180880555149134997689712039651088106301782) * 10 ^ 70 +
        5449918561297660266590206525589829437723565829505953193920850252782397) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (87 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_87_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_88_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (88 + x) *
        remainder6Coefficient0.coeff (88 - (88 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 88 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (88 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (88 - (88 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_88 :
    recurrence4Scalar0Exceptional.coeff 88 =
      ((((26934978 * 10 ^ 70 +
        2386524976420147020760559352616430788069356453416539187818175627354666) * 10 ^ 70 +
        4893762331703429100262660023861036670436294965193812418002005428690326) * 10 ^ 70 +
        0859665843240246453272511807755953663522857348593634722292054148588235) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (88 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_88_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_89_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (89 + x) *
        remainder6Coefficient0.coeff (89 - (89 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 89 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (89 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (89 - (89 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_89 :
    recurrence4Scalar0Exceptional.coeff 89 =
      -((((397299728 * 10 ^ 70 +
        3677170128860503635320953500638313114714858997806259563541985315640884) * 10 ^ 70 +
        2812420720639550665607718187460785953930628548727507522671421357612555) * 10 ^ 70 +
        8756586910966363869351497033007373023929082467278719926770403801864128) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (89 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_89_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_90_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (90 + x) *
        remainder6Coefficient0.coeff (90 - (90 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 90 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (90 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (90 - (90 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_90 :
    recurrence4Scalar0Exceptional.coeff 90 =
      ((((5681831403 * 10 ^ 70 +
        7299184380684803455319915747143421359087270636330096337897254851344128) * 10 ^ 70 +
        1308046449354605939391451482443775475334553979679904693015391203127998) * 10 ^ 70 +
        1256825596045694229392467091548893649874821761761476468503132291735330) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (90 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_90_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_91_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (91 + x) *
        remainder6Coefficient0.coeff (91 - (91 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 91 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (91 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (91 - (91 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_91 :
    recurrence4Scalar0Exceptional.coeff 91 =
      -((((78790327383 * 10 ^ 70 +
        6088603922644461226631683964202766569407667765413420572121127667838606) * 10 ^ 70 +
        1047427632650473847383542486981042920251358292727635252625434696647332) * 10 ^ 70 +
        4937798376078658394238861470176950193243478347297760186322058379433132) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (91 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_91_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_92_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (92 + x) *
        remainder6Coefficient0.coeff (92 - (92 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 92 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (92 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (92 - (92 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_92 :
    recurrence4Scalar0Exceptional.coeff 92 =
      ((((1059509703603 * 10 ^ 70 +
        8823839970425373440611908096473720481669628231325177886900789324148446) * 10 ^ 70 +
        6958489043299946445548728454815256207804511110718963338613906408843625) * 10 ^ 70 +
        6625554186685698484983103881793601267383660130453749664785918813705865) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (92 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_92_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_93_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (93 + x) *
        remainder6Coefficient0.coeff (93 - (93 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 93 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (93 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (93 - (93 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_93 :
    recurrence4Scalar0Exceptional.coeff 93 =
      -((((13816650056361 * 10 ^ 70 +
        8475785929040728001892145828595337106139999721104879161435318045803002) * 10 ^ 70 +
        8143690042589107310202462100166178741019260639084287177137683650776883) * 10 ^ 70 +
        6941372245316781233322896863799810151341708815742968210780529251595100) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (93 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_93_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_94_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (94 + x) *
        remainder6Coefficient0.coeff (94 - (94 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 94 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (94 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (94 - (94 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_94 :
    recurrence4Scalar0Exceptional.coeff 94 =
      ((((174730219304198 * 10 ^ 70 +
        5318175276874235816677783225718939773915871787513521583965877298203009) * 10 ^ 70 +
        0247098058594507938653828660623263672190524173066710762284380704354771) * 10 ^ 70 +
        2342226459921431109059018076041487643148837156033197494519440145728053) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (94 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_94_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_95_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (95 + x) *
        remainder6Coefficient0.coeff (95 - (95 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 95 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (95 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (95 - (95 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_95 :
    recurrence4Scalar0Exceptional.coeff 95 =
      -((((2142807948716539 * 10 ^ 70 +
        4987917658789487813171011416563218868504117679983011803985016674470906) * 10 ^ 70 +
        5450245548138692473119849914962254322530385281650562212139966003888330) * 10 ^ 70 +
        5435927280131862879558922072765906015783510022465237290424010041766756) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (95 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_95_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_96_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (96 + x) *
        remainder6Coefficient0.coeff (96 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 96 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (96 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (96 - (96 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_96 :
    recurrence4Scalar0Exceptional.coeff 96 =
      ((((25480543210882048 * 10 ^ 70 +
        9844565635753006916660873467685634883842589664438801187333431900381648) * 10 ^ 70 +
        7327602255907894400880604392501143531801580507282767795032198248536139) * 10 ^ 70 +
        8088815523378779545336678798687455817243025075736128063695556711266013) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (96 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_96_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_97_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (97 + x) *
        remainder6Coefficient0.coeff (97 - (97 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 97 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (97 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (97 - (97 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_97 :
    recurrence4Scalar0Exceptional.coeff 97 =
      -((((293750285538612148 * 10 ^ 70 +
        1275243402554544345428553577347131315884336019491515359126047866600862) * 10 ^ 70 +
        6510924290348581423481629653661064746662914103943143278112880831692195) * 10 ^ 70 +
        0720862932896095321951272756399800824014718568238443918548188737970594) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (97 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_97_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_98_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (98 + x) *
        remainder6Coefficient0.coeff (98 - (98 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 98 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (98 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (98 - (98 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_98 :
    recurrence4Scalar0Exceptional.coeff 98 =
      ((((3282423729833663093 * 10 ^ 70 +
        6817553583411474489366491298136933918057261346446418424527842427935005) * 10 ^ 70 +
        9025713864895426727557765351610834291363220939134289223207306926097185) * 10 ^ 70 +
        7470980432274350220162032988800500278145749466922769976670097291017460) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (98 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_98_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_99_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (99 + x) *
        remainder6Coefficient0.coeff (99 - (99 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 99 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (99 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (99 - (99 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_99 :
    recurrence4Scalar0Exceptional.coeff 99 =
      -((((35540382744495244696 * 10 ^ 70 +
        6562119442606343348137528411768238170024089908586771896861825396274282) * 10 ^ 70 +
        8673613107809808056936709638505374649164728831353729425955063535227634) * 10 ^ 70 +
        2086150186955854649054281148656092546845088063792041287796127893395764) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (99 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_99_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_100_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (100 + x) *
        remainder6Coefficient0.coeff (100 - (100 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 100 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (100 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (100 - (100 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_100 :
    recurrence4Scalar0Exceptional.coeff 100 =
      ((((372715892401984242075 * 10 ^ 70 +
        8429261952142882906118956581339186667371668741574650957651557313011000) * 10 ^ 70 +
        7794612402182099051400189034907611249203003645640410426745533557114726) * 10 ^ 70 +
        4880095863481798298967450683613472811661711331027766789834986769084619) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (100 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_100_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_101_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (101 + x) *
        remainder6Coefficient0.coeff (101 - (101 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 101 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (101 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (101 - (101 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_101 :
    recurrence4Scalar0Exceptional.coeff 101 =
      -((((3783729179481727841307 * 10 ^ 70 +
        2559954668079188906434934362088808993312773745825685239525149825226251) * 10 ^ 70 +
        6797466998794423631219343614742042493135518341594253027828531730562655) * 10 ^ 70 +
        0602725882124197207354831406802893083516639746592159088740544983761759) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (101 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_101_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_102_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (102 + x) *
        remainder6Coefficient0.coeff (102 - (102 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 102 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (102 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (102 - (102 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_102 :
    recurrence4Scalar0Exceptional.coeff 102 =
      ((((37156124862885503376308 * 10 ^ 70 +
        8796664271934157767711666528156920706896884029276891076939420552325452) * 10 ^ 70 +
        8439555287915180931765371216910566245175283283018240692003439400197866) * 10 ^ 70 +
        3160288606626936631860806538538784022214659110500985380917517513865012) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (102 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_102_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_103_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (103 + x) *
        remainder6Coefficient0.coeff (103 - (103 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 103 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (103 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (103 - (103 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_103 :
    recurrence4Scalar0Exceptional.coeff 103 =
      -((((352607150493247252920850 * 10 ^ 70 +
        1447091214618415214952289050023998172965156114725066795876584150693197) * 10 ^ 70 +
        0093046615360404156899910454185776488694633920522062331881040655682147) * 10 ^ 70 +
        5090841885494725549710455126560359274243824314371606150835289339842230) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (103 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_103_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_104_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (104 + x) *
        remainder6Coefficient0.coeff (104 - (104 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 104 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (104 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (104 - (104 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_104 :
    recurrence4Scalar0Exceptional.coeff 104 =
      ((((3229607952634835812903987 * 10 ^ 70 +
        5851798557713312222060654296964791503639579216822535550514705381016087) * 10 ^ 70 +
        9481862520894264857867090368037430877430668570260131919552529893794378) * 10 ^ 70 +
        4102115400868155176870425251011678691074439913273868839300431491888118) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (104 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_104_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_105_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (105 + x) *
        remainder6Coefficient0.coeff (105 - (105 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 105 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (105 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (105 - (105 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_105 :
    recurrence4Scalar0Exceptional.coeff 105 =
      -((((28501490367949245360194402 * 10 ^ 70 +
        8786455355441359046344088395258637800446691563654840547770519126146838) * 10 ^ 70 +
        0357570788556652342111755697835705705390194817759138295340784827477631) * 10 ^ 70 +
        4326758495357137252283367413268868119016630641427629912850563926565939) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (105 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_105_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (106 + x) *
        remainder6Coefficient0.coeff (106 - (106 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 106 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (106 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (106 - (106 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_106 :
    recurrence4Scalar0Exceptional.coeff 106 =
      ((((241789390327924739115518945 * 10 ^ 70 +
        7158377241116502502547939754194844817034303732201492154612333577494887) * 10 ^ 70 +
        7854418728466668731913218011673725682499154392108218949599254143914473) * 10 ^ 70 +
        6726595375996686316439186783993043320853040558009463669720849508563692) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (106 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_106_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (107 + x) *
        remainder6Coefficient0.coeff (107 - (107 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 107 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (107 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (107 - (107 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_107 :
    recurrence4Scalar0Exceptional.coeff 107 =
      -((((1965391835784696744010144418 * 10 ^ 70 +
        2509295752930540630173609203043113720482364115309984220796408534492383) * 10 ^ 70 +
        7088342026991310542157085117568940733348395245450433696795586921873484) * 10 ^ 70 +
        9763791996980091765092639124521177453345570456874720088445650123264994) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (107 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_107_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (108 + x) *
        remainder6Coefficient0.coeff (108 - (108 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 108 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (108 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (108 - (108 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_108 :
    recurrence4Scalar0Exceptional.coeff 108 =
      ((((15235510509168482715957695858 * 10 ^ 70 +
        7961402247601087063805844981448230331819986376181000798001421946650850) * 10 ^ 70 +
        6613054694199652635756312796655342467454221048548701969191345127790709) * 10 ^ 70 +
        0619770248910409160276086571925568327180254791007520696873530503080636) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (108 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_108_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (109 + x) *
        remainder6Coefficient0.coeff (109 - (109 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 109 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (109 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (109 - (109 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_109 :
    recurrence4Scalar0Exceptional.coeff 109 =
      -((((111824699928951516694205900266 * 10 ^ 70 +
        5991952870884775448130029844469344032817912110705853333199394300427389) * 10 ^ 70 +
        1945027193406469208876462246583496783977500259821725725705677682240241) * 10 ^ 70 +
        3463720020328087031097013244967646072546403697486005012022351644151429) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (109 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_109_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (110 + x) *
        remainder6Coefficient0.coeff (110 - (110 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 110 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (110 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (110 - (110 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_110 :
    recurrence4Scalar0Exceptional.coeff 110 =
      ((((768028592654375804521131554802 * 10 ^ 70 +
        5851925731200093435220460027268696054064089780754538406412265551386613) * 10 ^ 70 +
        0105740507946638771069894682856081609517816947457388231657700368592209) * 10 ^ 70 +
        6709087946766390839890217995694276541961230162854118598318848351911244) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (110 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_110_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (111 + x) *
        remainder6Coefficient0.coeff (111 - (111 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 111 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (111 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (111 - (111 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_111 :
    recurrence4Scalar0Exceptional.coeff 111 =
      -((((4831613589295661986855633468580 * 10 ^ 70 +
        1384930488231263723522129270120711907972339568587565661591425060472815) * 10 ^ 70 +
        9666679787766918141243993386013503139821087583516974752299072272427621) * 10 ^ 70 +
        0351438733570172088911849285299518328426268131207486535742230220528253) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (111 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_111_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (112 + x) *
        remainder6Coefficient0.coeff (112 - (112 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 112 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (112 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (112 - (112 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_112 :
    recurrence4Scalar0Exceptional.coeff 112 =
      ((((26596768393926822091163385874456 * 10 ^ 70 +
        1019677032610479626156413409950847835218063468280060457555755038119848) * 10 ^ 70 +
        6950565866670826582553068991727339381641626022811879330650299289274982) * 10 ^ 70 +
        5545265254808518672377036612056985538851491504202395814449304032691828) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (112 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_112_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (113 + x) *
        remainder6Coefficient0.coeff (113 - (113 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 113 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (113 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (113 - (113 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_113 :
    recurrence4Scalar0Exceptional.coeff 113 =
      -((((112192436218739719722912748473773 * 10 ^ 70 +
        2846547453316241049587459397776448693092373004177961095578587665308563) * 10 ^ 70 +
        3620390723942333126395075289284314823343817718626419932607482642332513) * 10 ^ 70 +
        4291356396904041231878820923238878858843190510706261982386965530153549) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (113 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_113_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (114 + x) *
        remainder6Coefficient0.coeff (114 - (114 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 114 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (114 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (114 - (114 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_114 :
    recurrence4Scalar0Exceptional.coeff 114 =
      ((((129830451566675705586183234476143 * 10 ^ 70 +
        8084908741751382511001701376357139965354923573823076073933475262216880) * 10 ^ 70 +
        7093243239708285649524800018607743145094276302523627512855281750158880) * 10 ^ 70 +
        3591470339453336217920509422824452961102383054700604851033552252276122) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (114 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_114_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (115 + x) *
        remainder6Coefficient0.coeff (115 - (115 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 115 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (115 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (115 - (115 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_115 :
    recurrence4Scalar0Exceptional.coeff 115 =
      ((((4295781404109469310786234819995142 * 10 ^ 70 +
        8022637663909189558908533102245111368830830866928945120841598338983050) * 10 ^ 70 +
        9488489697784643668613354561538957894476467149918638450390554450407619) * 10 ^ 70 +
        9278090854457574557400073134693862253976376745184777549383432341676447) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (115 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_115_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (116 + x) *
        remainder6Coefficient0.coeff (116 - (116 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 116 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (116 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (116 - (116 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_116 :
    recurrence4Scalar0Exceptional.coeff 116 =
      -((((67424883314271379303480714555217269 * 10 ^ 70 +
        7811095950883412587160629257378452339325770800710353784665226171841787) * 10 ^ 70 +
        0436196599326751900643671764948040520737894881315877806549307623040208) * 10 ^ 70 +
        6357365129466139182810489265394316306926751229962697816186870380169690) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (116 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_116_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (117 + x) *
        remainder6Coefficient0.coeff (117 - (117 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 117 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (117 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (117 - (117 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_117 :
    recurrence4Scalar0Exceptional.coeff 117 =
      ((((712213164582673621460353345552425877 * 10 ^ 70 +
        1370711402694969554595439443910851069119927587559772476019066892485851) * 10 ^ 70 +
        6348227688776855468175323451407190671857406209090199922620302795220272) * 10 ^ 70 +
        6942257384248255091775936624660310726798485936080351884100874320501352) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (117 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_117_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (118 + x) *
        remainder6Coefficient0.coeff (118 - (118 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 118 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (118 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (118 - (118 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_118 :
    recurrence4Scalar0Exceptional.coeff 118 =
      -((((6323601188259209558319489141635302328 * 10 ^ 70 +
        5249902433332180200711767789738209908460509548219933171545894075513271) * 10 ^ 70 +
        7476001143196434226590249238353615665141079826541132992783155236054221) * 10 ^ 70 +
        4506762513614230362717543004316312556450182220008299643850853423086629) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (118 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_118_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (119 + x) *
        remainder6Coefficient0.coeff (119 - (119 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 119 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (119 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (119 - (119 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_119 :
    recurrence4Scalar0Exceptional.coeff 119 =
      ((((50066533829516523674725384057966274998 * 10 ^ 70 +
        0087616426274033399413460100611001894445990868191493606101349187274127) * 10 ^ 70 +
        0147393732554147327671060830631794078467997345379489503770283882061574) * 10 ^ 70 +
        3519517575685327654927993721530124260712087592338837967136374637021597) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (119 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_119_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (120 + x) *
        remainder6Coefficient0.coeff (120 - (120 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 120 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (120 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (120 - (120 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_120 :
    recurrence4Scalar0Exceptional.coeff 120 =
      -((((360776698124688996258269305582637750082 * 10 ^ 70 +
        3482400835532390798443206982494125045168838912364578845912741063358584) * 10 ^ 70 +
        9238825531632210455268883763045029345726546300957666988380031800865503) * 10 ^ 70 +
        4455877452707439965967490137632297351335082819834789847934735295434139) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (120 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_120_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (121 + x) *
        remainder6Coefficient0.coeff (121 - (121 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 121 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (121 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (121 - (121 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_121 :
    recurrence4Scalar0Exceptional.coeff 121 =
      ((((2374390287781706921075971808500992056485 * 10 ^ 70 +
        4058052996040155257120539283141795409389802736476525108542060845429497) * 10 ^ 70 +
        9251209275288514986273193468739336201205168126158461571350469296145465) * 10 ^ 70 +
        5692588086558720777061654069769509915963071492409754005434648186210733) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (121 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_121_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (122 + x) *
        remainder6Coefficient0.coeff (122 - (122 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 122 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (122 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (122 - (122 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_122 :
    recurrence4Scalar0Exceptional.coeff 122 =
      -((((14124447569043168866990623492200490462450 * 10 ^ 70 +
        5955606776241445406043304993015608240513341873697089143366835471639742) * 10 ^ 70 +
        7267700081615312182541813156904145022942682651200714806454311790001022) * 10 ^ 70 +
        6550175298794310546526533449706733848745397980837696561272510257061400) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (122 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_122_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (123 + x) *
        remainder6Coefficient0.coeff (123 - (123 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 123 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (123 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (123 - (123 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_123 :
    recurrence4Scalar0Exceptional.coeff 123 =
      ((((73486858801738925546100302321972151224277 * 10 ^ 70 +
        0987950990933963976074683512701835940446030882266435785326349420735549) * 10 ^ 70 +
        5322104547078173585811701266458974835309025984501967774253515596086913) * 10 ^ 70 +
        7208828293920990153552781088115281327379420606423165605877432529172440) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (123 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_123_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (124 + x) *
        remainder6Coefficient0.coeff (124 - (124 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 124 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (124 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (124 - (124 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_124 :
    recurrence4Scalar0Exceptional.coeff 124 =
      -((((303222855015890395313669761005235369770021 * 10 ^ 70 +
        5802150914556613367975872298174288506437985738970762759229566011493614) * 10 ^ 70 +
        3540301556179995468385131446437005679846667076097432503209397583393165) * 10 ^ 70 +
        9135262878772429765922293036355608797220228184443771307661055997403404) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (124 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_124_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (125 + x) *
        remainder6Coefficient0.coeff (125 - (125 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 125 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (125 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (125 - (125 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_125 :
    recurrence4Scalar0Exceptional.coeff 125 =
      ((((586049129419783155388518958685694367104244 * 10 ^ 70 +
        3533770374745641602175741347259439464064932504582764742331532928945328) * 10 ^ 70 +
        7392419167667109967819621600822588144607591876216770356216720499785180) * 10 ^ 70 +
        2073241145477291982370561848388079944356495683412358923546431514860052) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (125 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_125_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (126 + x) *
        remainder6Coefficient0.coeff (126 - (126 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 126 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (126 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (126 - (126 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_126 :
    recurrence4Scalar0Exceptional.coeff 126 =
      ((((5854614422990901999008605019678060888581415 * 10 ^ 70 +
        7440984952089541695801509324737659921420839955591693469309183817433240) * 10 ^ 70 +
        9417102650187271918543593521398293193080216587532950228830037015503669) * 10 ^ 70 +
        2916744681250076818614303962140393958726327369987189086544605302219883) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (126 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_126_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (127 + x) *
        remainder6Coefficient0.coeff (127 - (127 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 127 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (127 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (127 - (127 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_127 :
    recurrence4Scalar0Exceptional.coeff 127 =
      -((((98062645773399749666681335572290856445411832 * 10 ^ 70 +
        1894866211644475167319895497636390991816616398499893167630620780288729) * 10 ^ 70 +
        8147067064608444954913493928469431807751433277297781728841602655902637) * 10 ^ 70 +
        5168617078766034265370057518980462855462545812416558983165253798374295) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (127 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_127_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (128 + x) *
        remainder6Coefficient0.coeff (128 - (128 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 128 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (128 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (128 - (128 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_128 :
    recurrence4Scalar0Exceptional.coeff 128 =
      ((((964673377836400922001744577567009447401864019 * 10 ^ 70 +
        5010732503616128328911491110291008541331131606034053289045259858391018) * 10 ^ 70 +
        2698710673396062137407522417569397785935896660716382519333846251428752) * 10 ^ 70 +
        6741299053579158649733716726886402475292943061636495484180370600244110) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (128 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_128_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (129 + x) *
        remainder6Coefficient0.coeff (129 - (129 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 129 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (129 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (129 - (129 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_129 :
    recurrence4Scalar0Exceptional.coeff 129 =
      -((((7754987334831978520384431672443153221754401519 * 10 ^ 70 +
        3106581684212852912976168719749477450942032529446301617913719529054892) * 10 ^ 70 +
        4638935580003540506681288294685555529579976443479557466701035932222591) * 10 ^ 70 +
        0687711606289562057012236613347923840005899396297304804044340911496398) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (129 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_129_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (130 + x) *
        remainder6Coefficient0.coeff (130 - (130 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 130 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (130 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (130 - (130 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_130 :
    recurrence4Scalar0Exceptional.coeff 130 =
      ((((54936592268357319392267703787173867491454015841 * 10 ^ 70 +
        1846738281050404952037582902225398472840763053791371550764644556250944) * 10 ^ 70 +
        0217817006279680840356014090537143340594896025438509579274481216614166) * 10 ^ 70 +
        7946004066831852197181292112445642821831509656823307467628062403704879) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (130 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_130_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (131 + x) *
        remainder6Coefficient0.coeff (131 - (131 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 131 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (131 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (131 - (131 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_131 :
    recurrence4Scalar0Exceptional.coeff 131 =
      -((((351669303407664844566279730770298308659257559030 * 10 ^ 70 +
        6890570089498583624764945371181598188361531175279249348106939344039958) * 10 ^ 70 +
        1759429564636880810091014342034632630748918917005602264850778668511935) * 10 ^ 70 +
        2427262797483878480181791336896380147977230246008857214224561460058717) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (131 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_131_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (132 + x) *
        remainder6Coefficient0.coeff (132 - (132 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 132 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (132 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (132 - (132 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_132 :
    recurrence4Scalar0Exceptional.coeff 132 =
      ((((2043474870696770445667799518938812475295278530130 * 10 ^ 70 +
        4143950109862039443331165386677297835719684782985048597483760697508845) * 10 ^ 70 +
        2209191597066592333254296367839668485454359249290084738223867806421376) * 10 ^ 70 +
        7234768267210329271985516829708706163536948077706059899725379582823979) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (132 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_132_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (133 + x) *
        remainder6Coefficient0.coeff (133 - (133 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 133 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (133 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (133 - (133 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_133 :
    recurrence4Scalar0Exceptional.coeff 133 =
      -((((10648102131117939252609013291874003164246494267762 * 10 ^ 70 +
        7590098811878349405974419213270676119843575067785825303257965945743673) * 10 ^ 70 +
        1044331773444293739791017961671167039608659909208799941710236629709308) * 10 ^ 70 +
        6954773088556637487391932931528642620252602576986970450196768220288237) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (133 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_133_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (134 + x) *
        remainder6Coefficient0.coeff (134 - (134 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 134 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (134 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (134 - (134 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_134 :
    recurrence4Scalar0Exceptional.coeff 134 =
      ((((47763096393046966685884359799814303642657786001592 * 10 ^ 70 +
        8969391716348441645893971542678961174336093218513802036406374016560620) * 10 ^ 70 +
        4350975209801212652274802898295335107526191653058730973992086658106575) * 10 ^ 70 +
        4540988790572020404497411278417854065338601659974611843026244911992664) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (134 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_134_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (135 + x) *
        remainder6Coefficient0.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 135 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (135 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (135 - (135 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_135 :
    recurrence4Scalar0Exceptional.coeff 135 =
      -((((161213524782424362703085321835058623602274352724574 * 10 ^ 70 +
        2035172578985495423137310262837074819517151646093489613887429078636547) * 10 ^ 70 +
        7152759762296390008171945726647926754290658489403133123555170033692409) * 10 ^ 70 +
        9643055830729231472224868240706527329729266233214433577879622563623639) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (135 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_135_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (136 + x) *
        remainder6Coefficient0.coeff (136 - (136 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 136 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (136 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (136 - (136 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_136 :
    recurrence4Scalar0Exceptional.coeff 136 =
      ((((125612065636566058455422828800565949800781729773626 * 10 ^ 70 +
        0561971946041638789472202416207121329764902925838425566076956989682001) * 10 ^ 70 +
        8428290278427726168577671208517658108898359706473905382759377567938219) * 10 ^ 70 +
        1501810930649171631930653670260744872987299057504557721999156359208658) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (136 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_136_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (137 + x) *
        remainder6Coefficient0.coeff (137 - (137 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 137 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (137 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (137 - (137 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_137 :
    recurrence4Scalar0Exceptional.coeff 137 =
      ((((4283043648719447761357491637727189374419294741592820 * 10 ^ 70 +
        5190717051403148626409132978489132754983579003383865106621292461963104) * 10 ^ 70 +
        1757924924997234811796612569449626211029456565197851607371582990621439) * 10 ^ 70 +
        1579824231569839522145711644368614748107973684569481207164147503747248) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (137 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_137_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (138 + x) *
        remainder6Coefficient0.coeff (138 - (138 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 138 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (138 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (138 - (138 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_138 :
    recurrence4Scalar0Exceptional.coeff 138 =
      -((((52673895886521179602344910122713018640239807223161501 * 10 ^ 70 +
        6418882031356429437537339609453848063534017363359103672390919496261302) * 10 ^ 70 +
        8100573480863198401916963210974373935702092280881860423029212237649237) * 10 ^ 70 +
        9966422519753780600711132895205204096606135519432203450536351070942028) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (138 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_138_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (139 + x) *
        remainder6Coefficient0.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 139 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (139 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (139 - (139 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_139 :
    recurrence4Scalar0Exceptional.coeff 139 =
      ((((442848551413180929781468438597108472926345456878182482 * 10 ^ 70 +
        4875956425569666669032559642940653775883157046159689282525210035927450) * 10 ^ 70 +
        8923929796994872616205845422046698817957026632311736263518782996378303) * 10 ^ 70 +
        6332992697002331195204366922412935776799566650093243352246319806516571) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (139 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (140 + x) *
        remainder6Coefficient0.coeff (140 - (140 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 140 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (140 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (140 - (140 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_140 :
    recurrence4Scalar0Exceptional.coeff 140 =
      -((((3145915483574172278958642503879437363342841808090823514 * 10 ^ 70 +
        7001964527301286217810584613729038236187572130773429798742276857920443) * 10 ^ 70 +
        6753101120747353083684449888716279428922482041906223752198930922066380) * 10 ^ 70 +
        6112948334945032640158123660753266550849215595471099592530924167599072) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (140 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (141 + x) *
        remainder6Coefficient0.coeff (141 - (141 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 141 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (141 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (141 - (141 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_141 :
    recurrence4Scalar0Exceptional.coeff 141 =
      ((((20029807525468573673095854505877717499383366485728590038 * 10 ^ 70 +
        1951473618203195954202257884779359126917426970781082719640939805246985) * 10 ^ 70 +
        8487889932136423594364223749323191249898593722196039306091666634851089) * 10 ^ 70 +
        7770960312030406472109287928376568861219462646726106298666225909029108) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (141 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (142 + x) *
        remainder6Coefficient0.coeff (142 - (142 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 142 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (142 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (142 - (142 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_142 :
    recurrence4Scalar0Exceptional.coeff 142 =
      -((((116872711540229834420293128828853277794078154853294128955 * 10 ^ 70 +
        0120564395675232979208437153386537797630504793970856960917043736423755) * 10 ^ 70 +
        6732589832860876932307656518834812079128034820696499166789963799394623) * 10 ^ 70 +
        5086504329710150389535734133440007310084986016584067574962692524337215) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (142 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (143 + x) *
        remainder6Coefficient0.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 143 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (143 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (143 - (143 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_143 :
    recurrence4Scalar0Exceptional.coeff 143 =
      ((((629270593699390696506071980796419353092656636026443772054 * 10 ^ 70 +
        3566189280359871307372172225705326845890217099565010657729848871360371) * 10 ^ 70 +
        6297632568551388593807868537769178999876875592469933753962698064883223) * 10 ^ 70 +
        0359342042060080411817145644922521109789363351931658906647823136391673) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (143 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (144 + x) *
        remainder6Coefficient0.coeff (144 - (144 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 144 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (144 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (144 - (144 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_144 :
    recurrence4Scalar0Exceptional.coeff 144 =
      -((((3113876518362729966360085546451145380861417279957085850810 * 10 ^ 70 +
        6145208829062698832144870681378402950079596375135987765305563633568345) * 10 ^ 70 +
        4641308360483792885334536002421557566519898546216350988153836590561741) * 10 ^ 70 +
        9433632911767766266774319152402232717836794282746407351767504138453532) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (144 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (145 + x) *
        remainder6Coefficient0.coeff (145 - (145 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 145 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (145 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (145 - (145 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_145 :
    recurrence4Scalar0Exceptional.coeff 145 =
      ((((13906003788195898884993877312145735978448430249026364845098 * 10 ^ 70 +
        4757850078323162709893276741781579979646143950897022068881715027787201) * 10 ^ 70 +
        0828701428296131400498272619975530128280969387120579743611873323540685) * 10 ^ 70 +
        7695496543945508258143839733768900618832779620223259208270179451250226) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (145 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (146 + x) *
        remainder6Coefficient0.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 146 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (146 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (146 - (146 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_146 :
    recurrence4Scalar0Exceptional.coeff 146 =
      -((((53321778639349609961287241189123102540014629649399522039028 * 10 ^ 70 +
        8891680059861608691207636679954485307779522487762966551332525277795377) * 10 ^ 70 +
        8636309461250488692825104168330951223146752609353784940776180924924508) * 10 ^ 70 +
        8771915103389334599339321339255776611276276195592535087316935737816433) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (146 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (147 + x) *
        remainder6Coefficient0.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 147 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (147 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (147 - (147 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_147 :
    recurrence4Scalar0Exceptional.coeff 147 =
      ((((148145192193389347716013658010403925038102193913856346225680 * 10 ^ 70 +
        1560537361128273093550957520857430231110597135740125148388973571368776) * 10 ^ 70 +
        4885844824201729070653552994776399465017865099173426060353330206777405) * 10 ^ 70 +
        0308394708458831923331008385156745425828179760109259522168691370929740) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (147 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (148 + x) *
        remainder6Coefficient0.coeff (148 - (148 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 148 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (148 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (148 - (148 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_148 :
    recurrence4Scalar0Exceptional.coeff 148 =
      ((((8858747902837176838704712798569762352939469395143398933900 * 10 ^ 70 +
        8280211110271643345161436345777067009308801675654160697897882996975494) * 10 ^ 70 +
        5391089062755268912123088702627185643997978693510019839138322274597551) * 10 ^ 70 +
        2004744027546858163710666695318766797525951779013543454637971749299348) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (148 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (149 + x) *
        remainder6Coefficient0.coeff (149 - (149 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 149 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (149 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (149 - (149 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_149 :
    recurrence4Scalar0Exceptional.coeff 149 =
      -((((4345144879657225118539848697355361739566843503862784901319806 * 10 ^ 70 +
        6290233092450183977823466558858892762794997858703524869153001305553772) * 10 ^ 70 +
        7958764228324722811107379493810780552445447004037214627995881506038043) * 10 ^ 70 +
        6283078241518594093328971582140090614238811194460699091276407471825284) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (149 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (150 + x) *
        remainder6Coefficient0.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 150 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (150 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (150 - (150 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_150 :
    recurrence4Scalar0Exceptional.coeff 150 =
      ((((44534335499011274792604743045930267129177137180162788617543768 * 10 ^ 70 +
        0068069610850980754333242364965829710808966152439445759459382942848765) * 10 ^ 70 +
        3587747062143021056714337505715646503549474661910456187704152622063592) * 10 ^ 70 +
        6687547193123782501385249941110770090043206636563833858690009805391967) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (150 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (151 + x) *
        remainder6Coefficient0.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 151 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (151 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (151 - (151 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_151 :
    recurrence4Scalar0Exceptional.coeff 151 =
      -((((335290507815370934650229541441363389548201767353752431193511274 * 10 ^ 70 +
        8306408390490167899504338814505005517610757530137443914365720958254720) * 10 ^ 70 +
        8321693785495510927331645056637808657428971400375224215409584419013827) * 10 ^ 70 +
        2589903423515495271249578241483337757626799028038829833153017903784586) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (151 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (152 + x) *
        remainder6Coefficient0.coeff (152 - (152 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 152 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (152 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (152 - (152 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_152 :
    recurrence4Scalar0Exceptional.coeff 152 =
      ((((2193870983886661790925920221629841434854485026128524925417653166 * 10 ^ 70 +
        7951616129378018835180668424760967946164948388398977986403822231406428) * 10 ^ 70 +
        4278218557086371705572989465299262827144914496443897736870108071156127) * 10 ^ 70 +
        6603365652896664040322143849889522098513842774340936547471744760085657) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (152 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (153 + x) *
        remainder6Coefficient0.coeff (153 - (153 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 153 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (153 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (153 - (153 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_153 :
    recurrence4Scalar0Exceptional.coeff 153 =
      -((((13161394934085108466223315810808078006569805766675765052579229549 * 10 ^ 70 +
        8599850835324190702009663564515654147876901377560956015610992963537316) * 10 ^ 70 +
        1192062474865468266969381828545008690737200303939453725754437836583974) * 10 ^ 70 +
        7358075154952499031957517795312882758519055439669690988797088945318290) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (153 - x)) = _
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
  rw [recurrence4Scalar0Exceptional_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (154 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (154 + x) *
        remainder6Coefficient0.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 154 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (154 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (154 - (154 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_154 :
    recurrence4Scalar0Exceptional.coeff 154 =
      ((((74167697810815651415083232815949558049967740848435852090576524847 * 10 ^ 70 +
        9710610866411192545347358971086419433412805216419166331878955742923742) * 10 ^ 70 +
        7036100261718348202348963031742165944938472189454611249380504734036832) * 10 ^ 70 +
        0668144809474936176658558478923103239740517737175364850418028128142263) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (154 - x)) = _
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
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (155 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (155 + x) *
        remainder6Coefficient0.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 155 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (155 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (155 - (155 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_155 :
    recurrence4Scalar0Exceptional.coeff 155 =
      -((((397805529588867740913474872140290253186183076461235921392950154851 * 10 ^ 70 +
        2865092389462095592929729717041502436981139979076052254558232846865099) * 10 ^ 70 +
        4180435967559718269250144506155658490340117808682980166916676895978152) * 10 ^ 70 +
        3566218679380197345597127794297647713739655403252360592985889886749184) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (155 - x)) = _
  rw [show 156 = 2 +
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
  rw [recurrence4Scalar0Exceptional_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (156 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (156 + x) *
        remainder6Coefficient0.coeff (156 - (156 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 156 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (156 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (156 - (156 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_156 :
    recurrence4Scalar0Exceptional.coeff 156 =
      ((((2047206273230705790819385109938306737199141344915158681206307074166 * 10 ^ 70 +
        3506200099616538713024519091444996779112609511765131991602606171780174) * 10 ^ 70 +
        5607798394034262742331855681397184351129812077465801699308764837259409) * 10 ^ 70 +
        6373643341299680519837676877719150318213611105147442089123332408857412) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (156 - x)) = _
  rw [show 157 = 3 +
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
  rw [recurrence4Scalar0Exceptional_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (157 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (157 + x) *
        remainder6Coefficient0.coeff (157 - (157 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 157 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (157 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (157 - (157 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_157 :
    recurrence4Scalar0Exceptional.coeff 157 =
      -((((10162398113327776408312379863997450968344995430850942305630404562101 * 10 ^ 70 +
        7302727169540122690417075004432607153229204497165300767546030700740652) * 10 ^ 70 +
        1310912976492229977251095403762429857453200134409292489774953883902168) * 10 ^ 70 +
        1862437975728570097421106006652071620553497308604915514288582861314676) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (157 - x)) = _
  rw [show 158 = 4 +
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
  rw [recurrence4Scalar0Exceptional_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (158 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (158 + x) *
        remainder6Coefficient0.coeff (158 - (158 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 158 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (158 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (158 - (158 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_158 :
    recurrence4Scalar0Exceptional.coeff 158 =
      ((((48842167668840109419002202072065562814549164566763521347223340262143 * 10 ^ 70 +
        3791061348325837339739704496126071095545471719907404791145463423011695) * 10 ^ 70 +
        4972156574639744868971426985405984848218827951207711615655009547937820) * 10 ^ 70 +
        7555892063773609110152598959042519819085257053298977159749341957084843) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (158 - x)) = _
  rw [show 159 = 5 +
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
  rw [recurrence4Scalar0Exceptional_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (159 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (159 + x) *
        remainder6Coefficient0.coeff (159 - (159 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 159 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (159 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (159 - (159 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_159 :
    recurrence4Scalar0Exceptional.coeff 159 =
      -((((227901929488198334198612273911713756897984482569408746819611155251972 * 10 ^ 70 +
        7369001310465130014298550932208806868275839194721745052286337316227968) * 10 ^ 70 +
        6059376065421138377729242657593467567186865450497104381570004471979041) * 10 ^ 70 +
        9594723396884536294663173934180604559203152286181971012776371212920903) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (159 - x)) = _
  rw [show 160 = 6 +
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
  rw [recurrence4Scalar0Exceptional_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (160 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (160 + x) *
        remainder6Coefficient0.coeff (160 - (160 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 160 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (160 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (160 - (160 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_160 :
    recurrence4Scalar0Exceptional.coeff 160 =
      ((((1034575260172772363413031636265294649458159822056242723780325810137194 * 10 ^ 70 +
        3838575377344030497171939041073602174846864821622651235806862010984082) * 10 ^ 70 +
        0380497451877477990646187267024395383610135140299907813216697425683213) * 10 ^ 70 +
        2275991645400432229643842009823919049922568719079418839732081305998983) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (160 - x)) = _
  rw [show 161 = 7 +
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
  rw [recurrence4Scalar0Exceptional_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
