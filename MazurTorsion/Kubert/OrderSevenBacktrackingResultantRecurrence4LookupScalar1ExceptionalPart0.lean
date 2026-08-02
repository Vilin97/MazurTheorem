/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_1
  recurrence4C1_coeff_10
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_11
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_12
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_13
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_2
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21

attribute [local simp]
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_3
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_4
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_5
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_6
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_7
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_8

attribute [local simp]
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_9
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
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
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136

attribute [local simp]
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
  recurrence4ExceptionalProduct_coeff_48
  recurrence4ExceptionalProduct_coeff_49
  recurrence4ExceptionalProduct_coeff_5
  recurrence4ExceptionalProduct_coeff_50

attribute [local simp]
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

private theorem recurrence4Scalar1Exceptional_coeff_0_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (x) *
        remainder6Coefficient1.coeff (0 - (x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < x
  · rw [recurrence4ExceptionalProduct_coeff_high (x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (0 - (x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_0 :
    recurrence4Scalar1Exceptional.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_0_suffix_zero]

private theorem recurrence4Scalar1Exceptional_coeff_1_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (1 + x) *
        remainder6Coefficient1.coeff (1 - (1 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 1 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (1 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (1 - (1 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_1 :
    recurrence4Scalar1Exceptional.coeff 1 =
      (7863807291149679993597577870117009352646656 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_1_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_2_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (2 + x) *
        remainder6Coefficient1.coeff (2 - (2 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 2 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (2 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (2 - (2 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_2 :
    recurrence4Scalar1Exceptional.coeff 2 =
      (-65585369952137973030776642519053722462814502912 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_2_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_3_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (3 + x) *
        remainder6Coefficient1.coeff (3 - (3 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 3 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (3 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (3 - (3 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_3 :
    recurrence4Scalar1Exceptional.coeff 3 =
      (213602094035798907069872632148706090165475271664512 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_3_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_4_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (4 + x) *
        remainder6Coefficient1.coeff (4 - (4 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 4 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (4 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (4 - (4 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_4 :
    recurrence4Scalar1Exceptional.coeff 4 =
      (-256151286573907978714623159179340362693804423166735072 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_4_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_5_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (5 + x) *
        remainder6Coefficient1.coeff (5 - (5 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 5 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (5 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (5 - (5 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_5 :
    recurrence4Scalar1Exceptional.coeff 5 =
      (-303555327441912774450756825390853734758323020746029086688 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_5_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_6_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (6 + x) *
        remainder6Coefficient1.coeff (6 - (6 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 6 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (6 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (6 - (6 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_6 :
    recurrence4Scalar1Exceptional.coeff 6 =
      (1378264803633140828532305316462818952003048343155292463730376 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_6_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_7_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (7 + x) *
        remainder6Coefficient1.coeff (7 - (7 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 7 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (7 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (7 - (7 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_7 :
    recurrence4Scalar1Exceptional.coeff 7 =
      (-1575905859927531543220076487586939332447886986718618638727858392 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_7_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_8_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (8 + x) *
        remainder6Coefficient1.coeff (8 - (8 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 8 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (8 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (8 - (8 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_8 :
    recurrence4Scalar1Exceptional.coeff 8 =
      (-26139555887831090764656872400976619984019805101441023071622170952 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_8_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_9_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (9 + x) *
        remainder6Coefficient1.coeff (9 - (9 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 9 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (9 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (9 - (9 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_9 :
    recurrence4Scalar1Exceptional.coeff 9 =
      (1978977344706207232369306006416468317370727638608381741488084704973280 : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_9_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_10_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (10 + x) *
        remainder6Coefficient1.coeff (10 - (10 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 10 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (10 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (10 - (10 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_10 :
    recurrence4Scalar1Exceptional.coeff 10 =
      -((233 * 10 ^ 70 +
        1075246628308340418451622858589291699073123341198240320689315475539566) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_10_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_11_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (11 + x) *
        remainder6Coefficient1.coeff (11 - (11 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 11 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (11 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (11 - (11 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_11 :
    recurrence4Scalar1Exceptional.coeff 11 =
      ((124837 * 10 ^ 70 +
        4356957940182118916634972187170271130317807997925367316709388957035318) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_11_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_12_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (12 + x) *
        remainder6Coefficient1.coeff (12 - (12 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 12 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (12 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (12 - (12 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_12 :
    recurrence4Scalar1Exceptional.coeff 12 =
      -((17594161 * 10 ^ 70 +
        7833599236914993163371293564110919470093178202947381855999071567803266) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_12_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_13_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (13 + x) *
        remainder6Coefficient1.coeff (13 - (13 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 13 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (13 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (13 - (13 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_13 :
    recurrence4Scalar1Exceptional.coeff 13 =
      -((20962174070 * 10 ^ 70 +
        5126716174518197508737156731395451406747301665122054554191077477576056) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_13_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_14_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (14 + x) *
        remainder6Coefficient1.coeff (14 - (14 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 14 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (14 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (14 - (14 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_14 :
    recurrence4Scalar1Exceptional.coeff 14 =
      ((17081055767507 * 10 ^ 70 +
        1612717017700678145021420565016134295339501346198481801644765215427616) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_14_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_15_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (15 + x) *
        remainder6Coefficient1.coeff (15 - (15 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 15 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (15 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (15 - (15 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_15 :
    recurrence4Scalar1Exceptional.coeff 15 =
      -((6810343231232760 * 10 ^ 70 +
        4871704089947933006248303479387852355424606786069464410826210068200649) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_15_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_16_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (16 + x) *
        remainder6Coefficient1.coeff (16 - (16 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 16 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (16 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (16 - (16 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_16 :
    recurrence4Scalar1Exceptional.coeff 16 =
      ((1701847712569801238 * 10 ^ 70 +
        9832348406565502158000744883386647948175515919411295581806096008993133) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_16_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_17_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (17 + x) *
        remainder6Coefficient1.coeff (17 - (17 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 17 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (17 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (17 - (17 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_17 :
    recurrence4Scalar1Exceptional.coeff 17 =
      -((274374260437772883497 * 10 ^ 70 +
        9898965211923329604771281255821489825245386412665049816233113987192014) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_17_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_18_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (18 + x) *
        remainder6Coefficient1.coeff (18 - (18 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 18 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (18 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (18 - (18 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_18 :
    recurrence4Scalar1Exceptional.coeff 18 =
      ((32870854569160369076566 * 10 ^ 70 +
        1298510137545937208406095291512276291865996621953682964453276815568636) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_18_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_19_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (19 + x) *
        remainder6Coefficient1.coeff (19 - (19 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 19 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (19 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (19 - (19 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_19 :
    recurrence4Scalar1Exceptional.coeff 19 =
      -((8908654785596230946301143 * 10 ^ 70 +
        9778371287913298509238266615580635846180851590847232902993158440572000) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_19_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_20_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (20 + x) *
        remainder6Coefficient1.coeff (20 - (20 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 20 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (20 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (20 - (20 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_20 :
    recurrence4Scalar1Exceptional.coeff 20 =
      ((4800951679070295036277750725 * 10 ^ 70 +
        6690176673189811299666575179213611981102202816730849660583377496748960) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_20_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_21_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (21 + x) *
        remainder6Coefficient1.coeff (21 - (21 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 21 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (21 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (21 - (21 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_21 :
    recurrence4Scalar1Exceptional.coeff 21 =
      -((1989241067819580173265318028742 * 10 ^ 70 +
        4804642198455257505709923852933464777368141685181855045385656840726215) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_21_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_22_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (22 + x) *
        remainder6Coefficient1.coeff (22 - (22 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 22 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (22 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (22 - (22 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_22 :
    recurrence4Scalar1Exceptional.coeff 22 =
      ((616449352562833567046707378832874 * 10 ^ 70 +
        3291440784151618602043024258581566985391248565820001228881270455829677) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_22_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_23_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (23 + x) *
        remainder6Coefficient1.coeff (23 - (23 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 23 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (23 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (23 - (23 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_23 :
    recurrence4Scalar1Exceptional.coeff 23 =
      -((154001295385416132317482297609589440 * 10 ^ 70 +
        1742041679183364931097376073477264348555835576176507661197482742627827) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_23_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_24_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (24 + x) *
        remainder6Coefficient1.coeff (24 - (24 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 24 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (24 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (24 - (24 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_24 :
    recurrence4Scalar1Exceptional.coeff 24 =
      ((32983059285868508708905072363615612974 * 10 ^ 70 +
        0893922724387833512248483992447538707629187298664034991184804205835289) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_24_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_25_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (25 + x) *
        remainder6Coefficient1.coeff (25 - (25 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 25 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (25 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (25 - (25 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_25 :
    recurrence4Scalar1Exceptional.coeff 25 =
      -((6488868849789877748964233978832103233484 * 10 ^ 70 +
        7110894102659122180981788236523060847318517429180942689191717842183981) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_25_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_26_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (26 + x) *
        remainder6Coefficient1.coeff (26 - (26 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 26 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (26 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (26 - (26 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_26 :
    recurrence4Scalar1Exceptional.coeff 26 =
      ((1292426268308749843054185548531900352803760 * 10 ^ 70 +
        1204205835358125692753795899911942971026177127138643927146870934746054) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_26_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_27_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (27 + x) *
        remainder6Coefficient1.coeff (27 - (27 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 27 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (27 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (27 - (27 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_27 :
    recurrence4Scalar1Exceptional.coeff 27 =
      -((285873960136211531002426301884838870988012122 * 10 ^ 70 +
        3771114510142434305414938326822543241151657826332412004618058756705222) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_27_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_28_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (28 + x) *
        remainder6Coefficient1.coeff (28 - (28 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 28 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (28 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (28 - (28 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_28 :
    recurrence4Scalar1Exceptional.coeff 28 =
      ((70386572134203829754294546380670392434318026573 * 10 ^ 70 +
        2776587248909554081951449213224643718625551754308585801624792791137131) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_28_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_29_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (29 + x) *
        remainder6Coefficient1.coeff (29 - (29 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 29 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (29 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (29 - (29 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_29 :
    recurrence4Scalar1Exceptional.coeff 29 =
      -((17822907461918602551435218102674656569555286172712 * 10 ^ 70 +
        2200563209446191517575124689138528436851944336273460119204300275003724) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_29_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_30_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (30 + x) *
        remainder6Coefficient1.coeff (30 - (30 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 30 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (30 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (30 - (30 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_30 :
    recurrence4Scalar1Exceptional.coeff 30 =
      ((4319791061385120746193295905246352956009376811309355 * 10 ^ 70 +
        8189190226529499578893947018229622595948374584112656511462566465251215) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_30_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_31_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (31 + x) *
        remainder6Coefficient1.coeff (31 - (31 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 31 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (31 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (31 - (31 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_31 :
    recurrence4Scalar1Exceptional.coeff 31 =
      -((968781106815575974883934766570233146248277897905745849 * 10 ^ 70 +
        6356069000344210583794560707234395351648847368274212303534902894838149) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_31_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_32_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (32 + x) *
        remainder6Coefficient1.coeff (32 - (32 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 32 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (32 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (32 - (32 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_32 :
    recurrence4Scalar1Exceptional.coeff 32 =
      ((199082504618260879576988298563807033939604454765118554424 * 10 ^ 70 +
        2916391753515782914497142819394876895933287671335326019677791669015398) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  rw [recurrence4Scalar1Exceptional_coeff_32_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_33_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (33 + x) *
        remainder6Coefficient1.coeff (33 - (33 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 33 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (33 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (33 - (33 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_33 :
    recurrence4Scalar1Exceptional.coeff 33 =
      -((37497228718455318160455356795505336866799084004903561082970 * 10 ^ 70 +
        2977806339127571460717384186074858645942981275512912219954979436577318) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (33 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_33_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_34_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (34 + x) *
        remainder6Coefficient1.coeff (34 - (34 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 34 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (34 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (34 - (34 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_34 :
    recurrence4Scalar1Exceptional.coeff 34 =
      ((6495682768542936505778210173262730857167848198803933954000304 * 10 ^ 70 +
        0142842581847583142120057912482783609667783767884776037086782730212256) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (34 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_34_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_35_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (35 + x) *
        remainder6Coefficient1.coeff (35 - (35 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 35 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (35 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (35 - (35 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_35 :
    recurrence4Scalar1Exceptional.coeff 35 =
      -((1039114900641161191081543485019313300918061394027819801400208169 * 10 ^ 70 +
        1147551470713519166024779503590421926694995320107809601425850543984497) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (35 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_35_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_36_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (36 + x) *
        remainder6Coefficient1.coeff (36 - (36 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 36 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (36 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (36 - (36 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_36 :
    recurrence4Scalar1Exceptional.coeff 36 =
      ((154082107180924690663319281581684249372838719872292737544659547525 * 10 ^ 70 +
        8892396814715015043895085859336283360946307903906526968573042672033704) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (36 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_36_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_37_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (37 + x) *
        remainder6Coefficient1.coeff (37 - (37 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 37 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (37 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (37 - (37 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_37 :
    recurrence4Scalar1Exceptional.coeff 37 =
      -((21248344628030394278381239279568132519367621506581149331729604570842 * 10 ^ 70 +
        6521116074524073787395822185706459846509440102737940893500336658085384) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (37 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_37_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_38_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (38 + x) *
        remainder6Coefficient1.coeff (38 - (38 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 38 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (38 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (38 - (38 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_38 :
    recurrence4Scalar1Exceptional.coeff 38 =
      ((2732896445904859320498357016775374729239234554756363304899142436102485 * 10 ^ 70 +
        1311179944396891228395392344293055128440815669340612113663763428781710) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (38 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_38_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_39_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (39 + x) *
        remainder6Coefficient1.coeff (39 - (39 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 39 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (39 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (39 - (39 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_39 :
    recurrence4Scalar1Exceptional.coeff 39 =
      -(((32 * 10 ^ 70 +
        8644988984690878438945199251642656782786259446135390547693542597711000) * 10 ^ 70 +
        9011391457562091824469172578361138277113400085923435966513851156301789) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (39 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_39_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_40_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (40 + x) *
        remainder6Coefficient1.coeff (40 - (40 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 40 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (40 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (40 - (40 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_40 :
    recurrence4Scalar1Exceptional.coeff 40 =
      (((3703 * 10 ^ 70 +
        3118572477080367205568113935429242224775797910982085256554078200700355) * 10 ^ 70 +
        1389752758235591581421355556826929846563501314919097320952790170263478) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (40 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_40_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_41_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (41 + x) *
        remainder6Coefficient1.coeff (41 - (41 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 41 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (41 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (41 - (41 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_41 :
    recurrence4Scalar1Exceptional.coeff 41 =
      -(((391802 * 10 ^ 70 +
        2496329916344250781581464989889396677801185073372067538050481332936531) * 10 ^ 70 +
        3092286210823749130743446392764975979740803701352152180118251102828699) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (41 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_41_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_42_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (42 + x) *
        remainder6Coefficient1.coeff (42 - (42 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 42 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (42 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (42 - (42 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_42 :
    recurrence4Scalar1Exceptional.coeff 42 =
      (((38988056 * 10 ^ 70 +
        8944889159741779150248159170364745418985283302702281482429235342590217) * 10 ^ 70 +
        4279796273054589963968591336013089294542248153757244351420117512112182) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (42 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_42_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_43_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (43 + x) *
        remainder6Coefficient1.coeff (43 - (43 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 43 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (43 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (43 - (43 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_43 :
    recurrence4Scalar1Exceptional.coeff 43 =
      -(((3655061075 * 10 ^ 70 +
        5366566601565494226092043146008095397740600483017154670927383941112171) * 10 ^ 70 +
        6147294419128753371955463396269774197451594377304895741380093618843890) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (43 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_43_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_44_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (44 + x) *
        remainder6Coefficient1.coeff (44 - (44 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 44 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (44 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (44 - (44 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_44 :
    recurrence4Scalar1Exceptional.coeff 44 =
      (((323305490739 * 10 ^ 70 +
        5235127238876871086358256936065905540702285244840855106663378521717148) * 10 ^ 70 +
        7314294385404638417292807271514304587746536360096261806380284793092229) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (44 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_44_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_45_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (45 + x) *
        remainder6Coefficient1.coeff (45 - (45 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 45 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (45 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (45 - (45 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_45 :
    recurrence4Scalar1Exceptional.coeff 45 =
      -(((27020832860843 * 10 ^ 70 +
        4770867196386470742786058474587465594534705873435581662359657214460977) * 10 ^ 70 +
        1461400779562300046905005623159362148276169677652822340639558678899563) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (45 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_45_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_46_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (46 + x) *
        remainder6Coefficient1.coeff (46 - (46 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 46 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (46 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (46 - (46 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_46 :
    recurrence4Scalar1Exceptional.coeff 46 =
      (((2136605757421683 * 10 ^ 70 +
        5285900758988574717070283546812035888974547475565588984263519219638256) * 10 ^ 70 +
        2655233600450885632365705340141897690082733803936475370678153398048337) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (46 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_46_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_47_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (47 + x) *
        remainder6Coefficient1.coeff (47 - (47 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 47 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (47 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (47 - (47 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_47 :
    recurrence4Scalar1Exceptional.coeff 47 =
      -(((160040054949147706 * 10 ^ 70 +
        9379572644910317707359745980453413356091802360532670992544335276972669) * 10 ^ 70 +
        5128603314847450390364160052651393008042919983095981473299184394763590) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (47 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_47_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_48_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (48 + x) *
        remainder6Coefficient1.coeff (48 - (48 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 48 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (48 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (48 - (48 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_48 :
    recurrence4Scalar1Exceptional.coeff 48 =
      (((11368938720987585395 * 10 ^ 70 +
        1225452825561878214781150988808698395017459667365417167518322872089133) * 10 ^ 70 +
        3151110959141522200430876761206712650762789750613552648591074202720739) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (48 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_48_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_49_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (49 + x) *
        remainder6Coefficient1.coeff (49 - (49 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 49 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (49 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (49 - (49 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_49 :
    recurrence4Scalar1Exceptional.coeff 49 =
      -(((766794936284072639538 * 10 ^ 70 +
        0801586565433115576615941290773292627049179537167271124946935749680078) * 10 ^ 70 +
        6070408571082797310545034255765749245806754694114026967348397679868666) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (49 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_49_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_50_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (50 + x) *
        remainder6Coefficient1.coeff (50 - (50 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 50 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (50 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (50 - (50 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_50 :
    recurrence4Scalar1Exceptional.coeff 50 =
      (((49154494377616152504927 * 10 ^ 70 +
        8980453004256929779175684834284916813445669967810389944275574815245356) * 10 ^ 70 +
        9183795444641403607742763729709461090813245569918303119101616870768456) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (50 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_50_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_51_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (51 + x) *
        remainder6Coefficient1.coeff (51 - (51 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 51 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (51 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (51 - (51 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_51 :
    recurrence4Scalar1Exceptional.coeff 51 =
      -(((2997824597280124221735815 * 10 ^ 70 +
        0615511128356967781985243934308125152765458913800602313582569719931977) * 10 ^ 70 +
        5998662036082062409559256968816051276971284604479606913376292805860821) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (51 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_51_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_52_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (52 + x) *
        remainder6Coefficient1.coeff (52 - (52 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 52 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (52 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (52 - (52 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_52 :
    recurrence4Scalar1Exceptional.coeff 52 =
      (((174109348805990031926198307 * 10 ^ 70 +
        2285559039589412806609460117486937869820128283560953266619442622131044) * 10 ^ 70 +
        8937129674773888748650801441703440969104870507015403477180802056945342) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (52 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_52_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_53_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (53 + x) *
        remainder6Coefficient1.coeff (53 - (53 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 53 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (53 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (53 - (53 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_53 :
    recurrence4Scalar1Exceptional.coeff 53 =
      -(((9638423155138111069093205457 * 10 ^ 70 +
        8180791784304761926701484823629337285908033950968217794282552235426923) * 10 ^ 70 +
        3105288558640268945591793545417296949074035789214615614692575829181024) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (53 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_53_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_54_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (54 + x) *
        remainder6Coefficient1.coeff (54 - (54 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 54 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (54 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (54 - (54 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_54 :
    recurrence4Scalar1Exceptional.coeff 54 =
      (((509021027838451927955027668274 * 10 ^ 70 +
        8161175990197717809863766361250179579810330355480034161692649000373495) * 10 ^ 70 +
        4079497837107236150087260537420032842295707074901017516546880002655344) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (54 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_54_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_55_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (55 + x) *
        remainder6Coefficient1.coeff (55 - (55 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 55 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (55 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (55 - (55 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_55 :
    recurrence4Scalar1Exceptional.coeff 55 =
      -(((25666877238560237333711314698755 * 10 ^ 70 +
        9160852792376251550752417634090228629791614947656092784065160577218481) * 10 ^ 70 +
        9475808664079396977628111756194097389124857273716620386304749624993445) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (55 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_55_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_56_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (56 + x) *
        remainder6Coefficient1.coeff (56 - (56 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 56 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (56 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (56 - (56 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_56 :
    recurrence4Scalar1Exceptional.coeff 56 =
      (((1236700947577113637778001820516076 * 10 ^ 70 +
        8351914787578840878091385769069274841151810011649812393859394752941336) * 10 ^ 70 +
        6776269050211775926716871276369774513124887661935763520400658724831409) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (56 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_56_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_57_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (57 + x) *
        remainder6Coefficient1.coeff (57 - (57 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 57 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (57 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (57 - (57 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_57 :
    recurrence4Scalar1Exceptional.coeff 57 =
      -(((56982761957411795576492164618990762 * 10 ^ 70 +
        3183561250298717164590231975680739042872253670885947444720545335081858) * 10 ^ 70 +
        8470566477659323673514177187936014948980378920242085910480103610899496) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (57 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_57_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_58_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (58 + x) *
        remainder6Coefficient1.coeff (58 - (58 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 58 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (58 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (58 - (58 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_58 :
    recurrence4Scalar1Exceptional.coeff 58 =
      (((2512633361955948334855965242182236942 * 10 ^ 70 +
        7373984417506897094992275786635788089416858522380767112187631499651045) * 10 ^ 70 +
        1368069818531071638878176182932826274766462776229525603961936056699272) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (58 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_58_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_59_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (59 + x) *
        remainder6Coefficient1.coeff (59 - (59 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 59 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (59 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (59 - (59 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_59 :
    recurrence4Scalar1Exceptional.coeff 59 =
      -(((106103308043393850912293101415762663249 * 10 ^ 70 +
        5077483910097564692829369264407069766391489187011803128800753498859962) * 10 ^ 70 +
        3241951939644752786247526739863231272913982901233298321200979519359993) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (59 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_59_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_60_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (60 + x) *
        remainder6Coefficient1.coeff (60 - (60 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 60 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (60 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (60 - (60 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_60 :
    recurrence4Scalar1Exceptional.coeff 60 =
      (((4293768482776802182058247236100805947305 * 10 ^ 70 +
        2023225264093825661233282465226044992966420431647170786144834226514318) * 10 ^ 70 +
        4269754468971834403968930667723872439168541054354791692965584262074731) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (60 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_60_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_61_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (61 + x) *
        remainder6Coefficient1.coeff (61 - (61 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 61 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (61 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (61 - (61 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_61 :
    recurrence4Scalar1Exceptional.coeff 61 =
      -(((166626064490886137500599762251817199775335 * 10 ^ 70 +
        0039855110486179190989465531539640601151378280704751078326267738672476) * 10 ^ 70 +
        8637957437993142470931854290848269585568647174397043847780731960540132) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (61 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_61_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_62_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (62 + x) *
        remainder6Coefficient1.coeff (62 - (62 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 62 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (62 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (62 - (62 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_62 :
    recurrence4Scalar1Exceptional.coeff 62 =
      (((6204633594154795762558327924390640260288666 * 10 ^ 70 +
        9805596186901671772705762997189876090008390416815910548058286476741870) * 10 ^ 70 +
        9217702215670533311039333677927351281826758881620795091305251411827398) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (62 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_62_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_63_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (63 + x) *
        remainder6Coefficient1.coeff (63 - (63 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 63 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (63 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (63 - (63 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_63 :
    recurrence4Scalar1Exceptional.coeff 63 =
      -(((221831173755962045281549683737933069920537460 * 10 ^ 70 +
        3519447347744503250552627329441775447720427475666481650590491124588927) * 10 ^ 70 +
        3199605184129226205154460447998353597865044331765685456508215379970703) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (63 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_63_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_64_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (64 + x) *
        remainder6Coefficient1.coeff (64 - (64 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 64 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (64 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (64 - (64 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_64 :
    recurrence4Scalar1Exceptional.coeff 64 =
      (((7619335871444050586990398615554221797644878959 * 10 ^ 70 +
        9215873737664162066885057593459889270077267983539175296625447670403391) * 10 ^ 70 +
        5644117698047456774150446472516959960984591883839931160489798659020296) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (64 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_64_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_65_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (65 + x) *
        remainder6Coefficient1.coeff (65 - (65 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 65 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (65 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (65 - (65 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_65 :
    recurrence4Scalar1Exceptional.coeff 65 =
      -(((251562308293422484009841305463416853336468590440 * 10 ^ 70 +
        2220231625674265158419238534976822621851035120775948246699031292252489) * 10 ^ 70 +
        1831184046088270656795484120644640117135277122067430704652824066009637) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (65 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_65_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_66_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (66 + x) *
        remainder6Coefficient1.coeff (66 - (66 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 66 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (66 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (66 - (66 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_66 :
    recurrence4Scalar1Exceptional.coeff 66 =
      (((7988128671224689352347090747503990095375399357774 * 10 ^ 70 +
        5040723380659045120886644792459666498109415479243205283744608659853160) * 10 ^ 70 +
        0588872766844702296655922072267700909678563726610661904944669579868867) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (66 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_66_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_67_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (67 + x) *
        remainder6Coefficient1.coeff (67 - (67 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 67 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (67 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (67 - (67 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_67 :
    recurrence4Scalar1Exceptional.coeff 67 =
      -(((244086813834735146379254766723637507248271098122470 * 10 ^ 70 +
        8306452311105581307150740934767441958417892312241565878505323307368120) * 10 ^ 70 +
        2343824104977783918585768933945118570926691112937721864661225091467022) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (67 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_67_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_68_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (68 + x) *
        remainder6Coefficient1.coeff (68 - (68 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 68 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (68 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (68 - (68 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_68 :
    recurrence4Scalar1Exceptional.coeff 68 =
      (((7180655114962041963003279094074172043681836957521189 * 10 ^ 70 +
        0775351012662000726832980362056455053980920037047646260227908718087274) * 10 ^ 70 +
        4393609804923277109862712905944397811751389408960221101819706979232100) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (68 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_68_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_69_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (69 + x) *
        remainder6Coefficient1.coeff (69 - (69 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 69 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (69 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (69 - (69 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_69 :
    recurrence4Scalar1Exceptional.coeff 69 =
      -(((203477879090609141636756179511088974132678664898623042 * 10 ^ 70 +
        7331140213217891331435774064623149302183870385175724284697413165463322) * 10 ^ 70 +
        0639199380593541185593297574643809292180743681992552962753025935404286) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (69 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_69_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_70_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (70 + x) *
        remainder6Coefficient1.coeff (70 - (70 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 70 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (70 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (70 - (70 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_70 :
    recurrence4Scalar1Exceptional.coeff 70 =
      (((5556599030535752878098314278416816663535159642222432062 * 10 ^ 70 +
        5033706741511296889828474377438515910855444635086734421472698801582452) * 10 ^ 70 +
        0935507844404099298871549559818847188590870476888303416095353225197402) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (70 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_70_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_71_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (71 + x) *
        remainder6Coefficient1.coeff (71 - (71 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 71 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (71 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (71 - (71 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_71 :
    recurrence4Scalar1Exceptional.coeff 71 =
      -(((146297739903368442501742002493394453696565861765506429204 * 10 ^ 70 +
        5559474443790602935400518959004488066891656106541270936582387083859579) * 10 ^ 70 +
        8276639371911813417094733262158301535341983261108571143584298247857861) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (71 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_71_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_72_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (72 + x) *
        remainder6Coefficient1.coeff (72 - (72 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 72 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (72 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (72 - (72 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_72 :
    recurrence4Scalar1Exceptional.coeff 72 =
      (((3715298142424322496231450866676685571632912765226412851909 * 10 ^ 70 +
        7311482130704891137717827773057722018275218857077651504879218754640890) * 10 ^ 70 +
        6474477421822121816570093073593752962178438550561409076603669839322319) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (72 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_72_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_73_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (73 + x) *
        remainder6Coefficient1.coeff (73 - (73 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 73 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (73 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (73 - (73 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_73 :
    recurrence4Scalar1Exceptional.coeff 73 =
      -(((91046021708284012048940848557779604256925732693523672284661 * 10 ^ 70 +
        4426707625978057607409484662214961453083887645106974283032457179707873) * 10 ^ 70 +
        4656409209672737021056557593257443891136853674991842123836730872239042) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (73 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_73_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_74_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (74 + x) *
        remainder6Coefficient1.coeff (74 - (74 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 74 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (74 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (74 - (74 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_74 :
    recurrence4Scalar1Exceptional.coeff 74 =
      (((2153854489503717871747232638473525668244165669831963216297005 * 10 ^ 70 +
        4740497854975338863096777555190180879168139357008269424415977067104536) * 10 ^ 70 +
        9420256171049947402730872491802000625979069230305883945061463896455690) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (74 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_74_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_75_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (75 + x) *
        remainder6Coefficient1.coeff (75 - (75 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 75 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (75 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (75 - (75 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_75 :
    recurrence4Scalar1Exceptional.coeff 75 =
      -(((49207332985777639094700563350488579862134787692687718248436777 * 10 ^ 70 +
        8342246022011153269016473485833911021411546439803527975678337326031688) * 10 ^ 70 +
        6450202324385656941539249764594685328393517635539940703522977657344640) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (75 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_75_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_76_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (76 + x) *
        remainder6Coefficient1.coeff (76 - (76 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 76 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (76 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (76 - (76 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_76 :
    recurrence4Scalar1Exceptional.coeff 76 =
      (((1086086961053625366866546011747553822951490730098402521940418308 * 10 ^ 70 +
        9410727072290350380486189123777304961200379510026533629334458211020215) * 10 ^ 70 +
        6172581205190180973947804200631159753979029362889502986408452915865361) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (76 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_76_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_77_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (77 + x) *
        remainder6Coefficient1.coeff (77 - (77 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 77 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (77 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (77 - (77 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_77 :
    recurrence4Scalar1Exceptional.coeff 77 =
      -(((23167392415388783588576570524561592584461555039405463010524643260 * 10 ^ 70 +
        9358521665748478453689858758955741634381753148204260577407968293509581) * 10 ^ 70 +
        6274057012870440678787161812691067168108970573528862480084816217408813) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (77 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_77_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_78_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (78 + x) *
        remainder6Coefficient1.coeff (78 - (78 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 78 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (78 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (78 - (78 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_78 :
    recurrence4Scalar1Exceptional.coeff 78 =
      (((477768175063221097022696741601085456064235474754239873393243179865 * 10 ^ 70 +
        6568658883260858351241217411233115988583509813116890428232041703093806) * 10 ^ 70 +
        4655801343587877323504868579417330483457011182063740334650122660511047) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (78 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_78_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_79_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (79 + x) *
        remainder6Coefficient1.coeff (79 - (79 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 79 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (79 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (79 - (79 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_79 :
    recurrence4Scalar1Exceptional.coeff 79 =
      -(((9528569795960183673953377618225501685970210941370692231204840977401 * 10 ^ 70 +
        3298695152234953012230564286499844728177280842206489805619481973759480) * 10 ^ 70 +
        2297536182716813511284044602850452701249907571327800425062895184978354) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (79 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_79_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_80_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (80 + x) *
        remainder6Coefficient1.coeff (80 - (80 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 80 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (80 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (80 - (80 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_80 :
    recurrence4Scalar1Exceptional.coeff 80 =
      (((183841994408059686749042324496164601310979860869174322159613186533816 * 10 ^ 70 +
        8787682183322454592721306354081217200428215765401957350222970634070845) * 10 ^ 70 +
        8875666666999125323849127677764294001425838011444570038185007920148531) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (80 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_80_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_81_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (81 + x) *
        remainder6Coefficient1.coeff (81 - (81 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 81 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (81 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (81 - (81 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_81 :
    recurrence4Scalar1Exceptional.coeff 81 =
      -(((3432395277055997060516660475643114632119583262582325257856270612603423 * 10 ^ 70 +
        1203887318998573064117418295525945340254822428787230370546737957040649) * 10 ^ 70 +
        1305477831056360632500417514426863432480262680019858158736851538681588) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (81 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_81_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_82_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (82 + x) *
        remainder6Coefficient1.coeff (82 - (82 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 82 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (82 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (82 - (82 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_82 :
    recurrence4Scalar1Exceptional.coeff 82 =
      ((((6 * 10 ^ 70 +
        2030794579764171073914816161082662680717885252246268186087557366694274) * 10 ^ 70 +
        0814086477946576582798157894646826972730904255395065991469696217465085) * 10 ^ 70 +
        0480737683973012630029229404170021179914622180983601436703638933477647) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (82 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_82_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_83_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (83 + x) *
        remainder6Coefficient1.coeff (83 - (83 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 83 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (83 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (83 - (83 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_83 :
    recurrence4Scalar1Exceptional.coeff 83 =
      -((((108 * 10 ^ 70 +
        5398927254607172954363749344622796990584068866595269297114196462558609) * 10 ^ 70 +
        1817130291629595962388412663791157281381707018841681967949041753669896) * 10 ^ 70 +
        5311622924832791558865763149893636098591093519987948214798028582173898) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (83 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_83_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_84_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (84 + x) *
        remainder6Coefficient1.coeff (84 - (84 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 84 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (84 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (84 - (84 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_84 :
    recurrence4Scalar1Exceptional.coeff 84 =
      ((((1839 * 10 ^ 70 +
        2902684566220390113084925004078654723618178379665030948767983586928919) * 10 ^ 70 +
        0794048959576880587556124286708230958707805148192568028298369286546868) * 10 ^ 70 +
        4474112249065995473189890736046145738478089525744661851172599574366915) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (84 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_84_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_85_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (85 + x) *
        remainder6Coefficient1.coeff (85 - (85 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 85 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (85 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (85 - (85 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_85 :
    recurrence4Scalar1Exceptional.coeff 85 =
      -((((30191 * 10 ^ 70 +
        7865133678030896068176912712768156903470166044770001850741037073278728) * 10 ^ 70 +
        9406908878654995614928599811346326946935893350196891195004221411382327) * 10 ^ 70 +
        8365338366890770108750065970191949910721727333287645797642541651682441) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (85 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_85_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_86_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (86 + x) *
        remainder6Coefficient1.coeff (86 - (86 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 86 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (86 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (86 - (86 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_86 :
    recurrence4Scalar1Exceptional.coeff 86 =
      ((((480170 * 10 ^ 70 +
        3481052295094473262056068447822338027575663592801386259906714161646974) * 10 ^ 70 +
        6097227386890747739952147019457730317746767274005889684378976051032337) * 10 ^ 70 +
        6922836895964110234801426717163425926227226882419553346046154346652859) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (86 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_86_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_87_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (87 + x) *
        remainder6Coefficient1.coeff (87 - (87 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 87 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (87 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (87 - (87 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_87 :
    recurrence4Scalar1Exceptional.coeff 87 =
      -((((7400331 * 10 ^ 70 +
        1628676763739597905860225570943235097822455209446372440991440554309666) * 10 ^ 70 +
        2167949725947534342433202553394194199808223482895291121910919810411687) * 10 ^ 70 +
        4067763751160760431052259466140753128550549151424608337740686136091643) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (87 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_87_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_88_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (88 + x) *
        remainder6Coefficient1.coeff (88 - (88 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 88 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (88 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (88 - (88 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_88 :
    recurrence4Scalar1Exceptional.coeff 88 =
      ((((110542139 * 10 ^ 70 +
        9458747314597807855713349457735611036180273623656595151019694946729697) * 10 ^ 70 +
        4953298368313389741940707429871337524074444351503822675096258097735517) * 10 ^ 70 +
        9231610169448024995717365469785217928130644646239575704849710396438804) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (88 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_88_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_89_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (89 + x) *
        remainder6Coefficient1.coeff (89 - (89 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 89 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (89 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (89 - (89 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_89 :
    recurrence4Scalar1Exceptional.coeff 89 =
      -((((1600613807 * 10 ^ 70 +
        8612714422173622469751592520485594561213880008145992065317812586999792) * 10 ^ 70 +
        3257082392385331609936180376773788638433097612561963626224368092413948) * 10 ^ 70 +
        6218031772606213434880125424919998038657825565582604520950462599391953) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (89 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_89_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_90_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (90 + x) *
        remainder6Coefficient1.coeff (90 - (90 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 90 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (90 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (90 - (90 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_90 :
    recurrence4Scalar1Exceptional.coeff 90 =
      ((((22468639907 * 10 ^ 70 +
        9302457152183150573542112940590592474486722285261429121648405470768896) * 10 ^ 70 +
        0533780892127830726738901074313072287417101523056111074058519081487774) * 10 ^ 70 +
        0622120415246931327339486484784224040854021803496546471320174870879296) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (90 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_90_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_91_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (91 + x) *
        remainder6Coefficient1.coeff (91 - (91 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 91 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (91 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (91 - (91 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_91 :
    recurrence4Scalar1Exceptional.coeff 91 =
      -((((305798490272 * 10 ^ 70 +
        6780223230346924748038181036431362261331140574288836676876146877772438) * 10 ^ 70 +
        3023982606335513362835904744419608420998676506076527033308463074825811) * 10 ^ 70 +
        0395097115189786275154563458221181385554127248054385404908261358929933) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (91 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_91_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_92_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (92 + x) *
        remainder6Coefficient1.coeff (92 - (92 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 92 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (92 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (92 - (92 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_92 :
    recurrence4Scalar1Exceptional.coeff 92 =
      ((((4035382726181 * 10 ^ 70 +
        2525065657485447281066781316648013504375183672946800122506627583989686) * 10 ^ 70 +
        9780669236330813455287349177459909353459919454358562466688281035926634) * 10 ^ 70 +
        4879741181249288494942716085066201234882541215282351924726455817723038) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (92 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_92_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_93_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (93 + x) *
        remainder6Coefficient1.coeff (93 - (93 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 93 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (93 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (93 - (93 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_93 :
    recurrence4Scalar1Exceptional.coeff 93 =
      -((((51633470091501 * 10 ^ 70 +
        4163864765387126794695537171184162531961681664869128421474430557553431) * 10 ^ 70 +
        4269024178742872114590376974421779616931124457190664838068211940892397) * 10 ^ 70 +
        5946046697012166180596078327839828565496295497139036339951242603015961) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (93 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_93_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_94_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (94 + x) *
        remainder6Coefficient1.coeff (94 - (94 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 94 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (94 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (94 - (94 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_94 :
    recurrence4Scalar1Exceptional.coeff 94 =
      ((((640564575894406 * 10 ^ 70 +
        6782214614895157124788889895103934007425754724925404911583648683803388) * 10 ^ 70 +
        8800426768847563331688128966288600082156821995705504373826764361878666) * 10 ^ 70 +
        3381828924576788995006814983708542528669276655497588840735555747710241) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (94 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_94_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_95_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (95 + x) *
        remainder6Coefficient1.coeff (95 - (95 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 95 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (95 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (95 - (95 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_95 :
    recurrence4Scalar1Exceptional.coeff 95 =
      -((((7704525607672254 * 10 ^ 70 +
        6377102393618298234014239314071264367337675946088623395340862864318624) * 10 ^ 70 +
        1056565325191254074413602576273203339371862287885928904319595979638928) * 10 ^ 70 +
        8560097585526847977097692482399351102747612049698716845541291872679371) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (95 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_95_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_96_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (96 + x) *
        remainder6Coefficient1.coeff (96 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 96 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (96 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (96 - (96 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_96 :
    recurrence4Scalar1Exceptional.coeff 96 =
      ((((89829998194692079 * 10 ^ 70 +
        2591311315394804963183410420304172467102990011217579836241627915702788) * 10 ^ 70 +
        4719473906532899115105222416151396613244984686849526974710575002166091) * 10 ^ 70 +
        5889426320703033993362553262203289084070290452231841823398231100410107) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (96 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_96_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_97_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (97 + x) *
        remainder6Coefficient1.coeff (97 - (97 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 97 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (97 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (97 - (97 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_97 :
    recurrence4Scalar1Exceptional.coeff 97 =
      -((((1015080369158560901 * 10 ^ 70 +
        8398670211405947498335290583550623178285775942778871681954735174585414) * 10 ^ 70 +
        8370480504402095520852105012455125771068120212969428689343947000640209) * 10 ^ 70 +
        6418380542813111056948771106465115486461489716944488544726305797831686) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (97 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_97_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_98_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (98 + x) *
        remainder6Coefficient1.coeff (98 - (98 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 98 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (98 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (98 - (98 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_98 :
    recurrence4Scalar1Exceptional.coeff 98 =
      ((((11113674684217160613 * 10 ^ 70 +
        4355575271353970033061668789767295946151644176029135739846496794785813) * 10 ^ 70 +
        9865091790301026589174378597963164759569501764576307405792570648276225) * 10 ^ 70 +
        2299081521656990254759665261926168731896476278143608566810581166021097) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (98 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_98_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_99_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (99 + x) *
        remainder6Coefficient1.coeff (99 - (99 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 99 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (99 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (99 - (99 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_99 :
    recurrence4Scalar1Exceptional.coeff 99 =
      -((((117848232147266113379 * 10 ^ 70 +
        2440854809096582343282255737825392422107494504245052481273293924134295) * 10 ^ 70 +
        7516133886386408386877273776783265151818058180274193072910128423091185) * 10 ^ 70 +
        8160490391853686335933383334410360010540854424504994833152698836428053) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (99 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_99_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_100_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (100 + x) *
        remainder6Coefficient1.coeff (100 - (100 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 100 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (100 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (100 - (100 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_100 :
    recurrence4Scalar1Exceptional.coeff 100 =
      ((((1209680122194384029297 * 10 ^ 70 +
        8234613592574534168775557079805128950998953216457365439568108611069558) * 10 ^ 70 +
        0349100119824110888824299901760808759230473362275947871953142084991653) * 10 ^ 70 +
        5180579674336050703870882185269467780354253205834146040487633035409553) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (100 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_100_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_101_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (101 + x) *
        remainder6Coefficient1.coeff (101 - (101 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 101 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (101 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (101 - (101 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_101 :
    recurrence4Scalar1Exceptional.coeff 101 =
      -((((12011647485429882340036 * 10 ^ 70 +
        0638960220570374485735411825785162943685517762165377665153403294960185) * 10 ^ 70 +
        2751030910803647313658596649417799814282016378133014856700900510375926) * 10 ^ 70 +
        1047314881242864453017568060410466387602832078918046933365941269490118) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (101 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_101_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_102_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (102 + x) *
        remainder6Coefficient1.coeff (102 - (102 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 102 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (102 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (102 - (102 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_102 :
    recurrence4Scalar1Exceptional.coeff 102 =
      ((((115273220130587653241113 * 10 ^ 70 +
        7473171570592912578743134332908147109815104335454834193296412633286946) * 10 ^ 70 +
        0214547256496933059816382478174330116202972859105394769010896100868424) * 10 ^ 70 +
        7624406750239458958398518011863460511547621325951403852835924287423290) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (102 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_102_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_103_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (103 + x) *
        remainder6Coefficient1.coeff (103 - (103 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 103 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (103 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (103 - (103 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_103 :
    recurrence4Scalar1Exceptional.coeff 103 =
      -((((1067905012703344693207608 * 10 ^ 70 +
        4144688872470461161745191565536012880034684584294468059105304169438195) * 10 ^ 70 +
        3829158253567179698248920657403338127771564159571035080208911334490286) * 10 ^ 70 +
        7392517947002521856018628432757761807420769860950932110678603669459599) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (103 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_103_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_104_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (104 + x) *
        remainder6Coefficient1.coeff (104 - (104 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 104 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (104 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (104 - (104 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_104 :
    recurrence4Scalar1Exceptional.coeff 104 =
      ((((9535160504462443727289298 * 10 ^ 70 +
        8441391677287949275121296604311833021914541271157444526663323353349506) * 10 ^ 70 +
        2815125496028483304675747605710497810069115168265897901314145538449942) * 10 ^ 70 +
        3214393112731360881310554233219670772956565106299382470098218711627752) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (104 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_104_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_105_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (105 + x) *
        remainder6Coefficient1.coeff (105 - (105 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 105 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (105 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (105 - (105 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_105 :
    recurrence4Scalar1Exceptional.coeff 105 =
      -((((81880942058378537660119368 * 10 ^ 70 +
        0956071935748518402670480593392960682169021381560232768498712717070802) * 10 ^ 70 +
        2186647696139776872366490232764487492591222924723087817685508248154712) * 10 ^ 70 +
        8035452595531739674541284207602981303189805804634749074781066231606261) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (105 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_105_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (106 + x) *
        remainder6Coefficient1.coeff (106 - (106 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 106 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (106 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (106 - (106 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_106 :
    recurrence4Scalar1Exceptional.coeff 106 =
      ((((674221405865227575865926461 * 10 ^ 70 +
        8336456766220096500052111440374115826388957378240769675857620205130421) * 10 ^ 70 +
        8809302301639416709515078964525646515263566341111613748671297383775482) * 10 ^ 70 +
        3968767112351334201685407190862961863541488048074837895941525674158321) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (106 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_106_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (107 + x) *
        remainder6Coefficient1.coeff (107 - (107 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 107 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (107 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (107 - (107 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_107 :
    recurrence4Scalar1Exceptional.coeff 107 =
      -((((5300621664329724732787778996 * 10 ^ 70 +
        0650227969946789838464829257142893427408450119955226933736535867113089) * 10 ^ 70 +
        0309163270405282397421458226315996390219106435923242300409626102686558) * 10 ^ 70 +
        2066410711582528266913474818908864581483102266112963987676114874055336) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (107 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_107_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (108 + x) *
        remainder6Coefficient1.coeff (108 - (108 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 108 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (108 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (108 - (108 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_108 :
    recurrence4Scalar1Exceptional.coeff 108 =
      ((((39532626765080854489544424944 * 10 ^ 70 +
        0792211964096500941751391910260792543693566858410776771319540417882323) * 10 ^ 70 +
        1869168748055297586133679048295451427949955211858957911961816223809402) * 10 ^ 70 +
        4359430160550763835109869569696261506413597018336296121860141351529054) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (108 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_108_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (109 + x) *
        remainder6Coefficient1.coeff (109 - (109 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 109 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (109 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (109 - (109 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_109 :
    recurrence4Scalar1Exceptional.coeff 109 =
      -((((276817826864289020140416795234 * 10 ^ 70 +
        0714471430519615267912031102400184519255045073945915929061542901623260) * 10 ^ 70 +
        8944345005340331673739264428377379287623511752825079105912290050730170) * 10 ^ 70 +
        2102664338316139709141479981879411003459148619939248629157214463696456) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (109 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_109_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (110 + x) *
        remainder6Coefficient1.coeff (110 - (110 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 110 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (110 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (110 - (110 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_110 :
    recurrence4Scalar1Exceptional.coeff 110 =
      ((((1786979203003072482411447237824 * 10 ^ 70 +
        6421630966095720676661027242976657982374527727092052361096422477843860) * 10 ^ 70 +
        6769542576156754602675920783478434635827581309139741688175013068733945) * 10 ^ 70 +
        4664620042402571178587095490504994845162796960287403805223025004074258) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (110 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_110_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (111 + x) *
        remainder6Coefficient1.coeff (111 - (111 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 111 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (111 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (111 - (111 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_111 :
    recurrence4Scalar1Exceptional.coeff 111 =
      -((((10246966486277234582142209221248 * 10 ^ 70 +
        4356362576810610377137248527057055677916175916379966182427221832452571) * 10 ^ 70 +
        1264959283484908852903388963232421256492241597110123060356326739020113) * 10 ^ 70 +
        0752229343596510911471536268044484762195420770712584567742018420434147) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (111 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_111_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (112 + x) *
        remainder6Coefficient1.coeff (112 - (112 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 112 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (112 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (112 - (112 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_112 :
    recurrence4Scalar1Exceptional.coeff 112 =
      ((((47333122564242577413966422937362 * 10 ^ 70 +
        1964518068452285394855979374161235437927947837724509637684292571244993) * 10 ^ 70 +
        8448518195806821863749719476372329224142830449221750068795793738810406) * 10 ^ 70 +
        5563127309938445099939071159964282900233224100338635392314047028486220) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (112 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_112_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (113 + x) *
        remainder6Coefficient1.coeff (113 - (113 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 113 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (113 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (113 - (113 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_113 :
    recurrence4Scalar1Exceptional.coeff 113 =
      -((((107856718411983004181854864347430 * 10 ^ 70 +
        3330769162425603521973767115355849157766164215481770289835010305104662) * 10 ^ 70 +
        5222313439893986819531474963846588915591113357192795785725680321409174) * 10 ^ 70 +
        5142214828557794777797927300381340825672704396572903932486264078936302) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (113 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_113_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (114 + x) *
        remainder6Coefficient1.coeff (114 - (114 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 114 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (114 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (114 - (114 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_114 :
    recurrence4Scalar1Exceptional.coeff 114 =
      -((((1067777570635484589522431101960050 * 10 ^ 70 +
        7244105706299688405385701736303436024996826849342451286792524406322552) * 10 ^ 70 +
        5603450214154985166101455117076730061846202379897394487886542944499295) * 10 ^ 70 +
        5692250120667544695513427185593985834955939093365611789449759225780796) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (114 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_114_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (115 + x) *
        remainder6Coefficient1.coeff (115 - (115 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 115 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (115 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (115 - (115 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_115 :
    recurrence4Scalar1Exceptional.coeff 115 =
      ((((20898002292350894116198974203827013 * 10 ^ 70 +
        7866777948953197748156074733224418723596398731107381054134214700403793) * 10 ^ 70 +
        1808606593742024276207931693608936182052081815541525152244431713250718) * 10 ^ 70 +
        9214715686444632030388590872634979408009380093603764049938983371727654) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (115 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_115_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (116 + x) *
        remainder6Coefficient1.coeff (116 - (116 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 116 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (116 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (116 - (116 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_116 :
    recurrence4Scalar1Exceptional.coeff 116 =
      -((((235150222764125919465797846913664935 * 10 ^ 70 +
        1990472038064502508489709116936871415965971518222085020268195758079331) * 10 ^ 70 +
        8872613191888543777425977547135845251926035003459029138010017359403348) * 10 ^ 70 +
        2732143824659662060465479264661390101511795252619812428658747393946032) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (116 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_116_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (117 + x) *
        remainder6Coefficient1.coeff (117 - (117 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 117 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (117 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (117 - (117 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_117 :
    recurrence4Scalar1Exceptional.coeff 117 =
      ((((2161161550003207262791200915249713042 * 10 ^ 70 +
        3222059253333947168615199941448787369944999322654948672459820999128879) * 10 ^ 70 +
        3779086079822877448947321018412514717615824363804095102832669609459961) * 10 ^ 70 +
        7046699182098052932195986716763533571413397421382235383526562430043641) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (117 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_117_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (118 + x) *
        remainder6Coefficient1.coeff (118 - (118 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 118 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (118 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (118 - (118 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_118 :
    recurrence4Scalar1Exceptional.coeff 118 =
      -((((17541454054002358572884799285311030161 * 10 ^ 70 +
        7925723694897435583594479197090665144333516609149609172429527061463487) * 10 ^ 70 +
        4016910695410806408263275508247933043769587099969583322204807806077970) * 10 ^ 70 +
        7256896155210627177170134556900901775472898045199852451646915405341149) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (118 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_118_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (119 + x) *
        remainder6Coefficient1.coeff (119 - (119 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 119 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (119 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (119 - (119 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_119 :
    recurrence4Scalar1Exceptional.coeff 119 =
      ((((129126385249592546040866955575176823733 * 10 ^ 70 +
        1535946579379222404281067944907802496451415725684704210958435760746400) * 10 ^ 70 +
        8842495957928337233470689417778847310850226146695026546470463522126879) * 10 ^ 70 +
        8053059499753212340340136409357934737660945233949610395557156683657916) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (119 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_119_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (120 + x) *
        remainder6Coefficient1.coeff (120 - (120 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 120 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (120 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (120 - (120 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_120 :
    recurrence4Scalar1Exceptional.coeff 120 =
      -((((867911163241317191282360529479740014839 * 10 ^ 70 +
        8188558798908384233216872379551187837882507396973548738307140095545447) * 10 ^ 70 +
        0348359388745015227721761045376966152777842856061569177231996347645594) * 10 ^ 70 +
        5002679273581400044799260932501630107479666053501789047683031682339043) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (120 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_120_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (121 + x) *
        remainder6Coefficient1.coeff (121 - (121 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 121 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (121 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (121 - (121 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_121 :
    recurrence4Scalar1Exceptional.coeff 121 =
      ((((5288890367578804726034163707519280801477 * 10 ^ 70 +
        4708629367438130601786995013380285194991684883961604358754842298512158) * 10 ^ 70 +
        6048525876721666903653171740746769900302073245211690952122011508438543) * 10 ^ 70 +
        9213737850550521511415596816438103432059471169641827109175454447477080) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (121 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_121_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (122 + x) *
        remainder6Coefficient1.coeff (122 - (122 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 122 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (122 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (122 - (122 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_122 :
    recurrence4Scalar1Exceptional.coeff 122 =
      -((((28455073988803942921261003381914764497437 * 10 ^ 70 +
        8346937964187917840336805457429173262094702752246679393080812550294549) * 10 ^ 70 +
        9968475617910707764950704850238896990548843317411281454508497450203457) * 10 ^ 70 +
        4505417124127296025744622085651899476996138711757115132708364814402552) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (122 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_122_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (123 + x) *
        remainder6Coefficient1.coeff (123 - (123 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 123 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (123 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (123 - (123 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_123 :
    recurrence4Scalar1Exceptional.coeff 123 =
      ((((125233159989801360311524535315819888706117 * 10 ^ 70 +
        4486925607486958891998769794808892557118011022478393757597256966613533) * 10 ^ 70 +
        6559378752823958162105375685476001171396769615664858134604207401911816) * 10 ^ 70 +
        9826660369352530203247583711427305282608430126942443280960841839884490) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (123 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_123_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (124 + x) *
        remainder6Coefficient1.coeff (124 - (124 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 124 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (124 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (124 - (124 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_124 :
    recurrence4Scalar1Exceptional.coeff 124 =
      -((((323774597967597042622190421782423803828337 * 10 ^ 70 +
        3157256644669010950467925313200183678603965664495549336431842869624750) * 10 ^ 70 +
        9680061795321743074240918004216078609479100040876245255374163050646425) * 10 ^ 70 +
        1611360596173710738649658994004568968809289367534902701785670171302722) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (124 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_124_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (125 + x) *
        remainder6Coefficient1.coeff (125 - (125 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 125 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (125 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (125 - (125 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_125 :
    recurrence4Scalar1Exceptional.coeff 125 =
      -((((1405750483540573042587149024335874485938804 * 10 ^ 70 +
        8258680645222770864581329246730501154355426334428781732118691203104605) * 10 ^ 70 +
        0188300131687071480339155283822009626049637093616418773787838575612317) * 10 ^ 70 +
        7759496983645175172453928873586937875294152548287812324785807935006758) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (125 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_125_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (126 + x) *
        remainder6Coefficient1.coeff (126 - (126 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 126 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (126 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (126 - (126 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_126 :
    recurrence4Scalar1Exceptional.coeff 126 =
      ((((31474675070847362606542624244583071317480891 * 10 ^ 70 +
        7188789071486398487260818040016738322140122877769850595497996613460446) * 10 ^ 70 +
        1518159525226045044787124076390757925263495660524919130393181944129946) * 10 ^ 70 +
        0105325238459542216236739907244368359765287054643396380029507156818478) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (126 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_126_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (127 + x) *
        remainder6Coefficient1.coeff (127 - (127 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 127 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (127 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (127 - (127 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_127 :
    recurrence4Scalar1Exceptional.coeff 127 =
      -((((329940254562097962094782633444173089712237186 * 10 ^ 70 +
        4271913208836372730664329545068969261166049640536403884319686281283905) * 10 ^ 70 +
        9898163294476456587741763189274222801012146381049204079467285553209353) * 10 ^ 70 +
        7329884698683408300727130000070934457635649408026621134584850689512454) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (127 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_127_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (128 + x) *
        remainder6Coefficient1.coeff (128 - (128 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 128 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (128 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (128 - (128 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_128 :
    recurrence4Scalar1Exceptional.coeff 128 =
      ((((2738903954736575214123290762041559754357769733 * 10 ^ 70 +
        7516434665952593480711278891538232448175493345544213786445591292170040) * 10 ^ 70 +
        1613229348257624180842458440290065058042358393622498300598227207322487) * 10 ^ 70 +
        8664303259876837465445670046855634854004498944176762191311735009535777) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (128 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_128_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (129 + x) *
        remainder6Coefficient1.coeff (129 - (129 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 129 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (129 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (129 - (129 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_129 :
    recurrence4Scalar1Exceptional.coeff 129 =
      -((((19837447320758828254729651819078871184977923616 * 10 ^ 70 +
        9808178725360151965551599553776454791163404353575798867636781975916011) * 10 ^ 70 +
        5265154736997670372675299368331934368869590139331194338750840868892040) * 10 ^ 70 +
        9981356042799416476841124379945495625642389877023449687018461112724334) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (129 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_129_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (130 + x) *
        remainder6Coefficient1.coeff (130 - (130 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 130 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (130 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (130 - (130 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_130 :
    recurrence4Scalar1Exceptional.coeff 130 =
      ((((129365083283932314258500680110581315635407547452 * 10 ^ 70 +
        3254736322553951412288166433562597029745477428298845021229000460009115) * 10 ^ 70 +
        4297099775074555364310502358354388181266543865589931587465617262256766) * 10 ^ 70 +
        8590872520421957723540066282979504491480310867099743492570175117559581) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (130 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_130_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (131 + x) *
        remainder6Coefficient1.coeff (131 - (131 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 131 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (131 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (131 - (131 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_131 :
    recurrence4Scalar1Exceptional.coeff 131 =
      -((((765517272934183490220827158186861204633775767591 * 10 ^ 70 +
        4370465127159473003541127666896640392298079767537151875099321557341294) * 10 ^ 70 +
        9990288329010212591300448381040275031933012728627332976051023202696059) * 10 ^ 70 +
        3440211715360602473180464224543417543548683400669328064999759359616289) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (131 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_131_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (132 + x) *
        remainder6Coefficient1.coeff (132 - (132 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 132 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (132 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (132 - (132 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_132 :
    recurrence4Scalar1Exceptional.coeff 132 =
      ((((4074285290128914342888465742157289292567460270551 * 10 ^ 70 +
        3535955095514796555212470291356444636498940255357042933493586599391130) * 10 ^ 70 +
        5164257206836547147532348885518619373365489777142274004165421628284949) * 10 ^ 70 +
        4084672838889526397040760417301878052263400602734293874185132606219099) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (132 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_132_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (133 + x) *
        remainder6Coefficient1.coeff (133 - (133 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 133 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (133 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (133 - (133 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_133 :
    recurrence4Scalar1Exceptional.coeff 133 =
      -((((18852106120053443483840103196202843586432296975505 * 10 ^ 70 +
        7393475274465377639575010033475782117225553132452740721943781376254493) * 10 ^ 70 +
        4500816507124903396389932594842906507663626399008508549204153313020955) * 10 ^ 70 +
        1074614814243765651677873766115789891040261816858664406516154354205242) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (133 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_133_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (134 + x) *
        remainder6Coefficient1.coeff (134 - (134 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 134 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (134 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (134 - (134 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_134 :
    recurrence4Scalar1Exceptional.coeff 134 =
      ((((68130767809577208811330281938720565923904615829610 * 10 ^ 70 +
        6458820157637689823882571683013284256602795233900517740591136936377680) * 10 ^ 70 +
        6289646526794295759935888507153960770710079514631834521019087551136114) * 10 ^ 70 +
        3381357662308549877353264582065201816200932077069743490354097407527685) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (134 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_134_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (135 + x) *
        remainder6Coefficient1.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 135 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (135 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (135 - (135 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_135 :
    recurrence4Scalar1Exceptional.coeff 135 =
      -((((99979536271787860524422371142372699539872608738317 * 10 ^ 70 +
        1036655315811401215397693848271711824135876191263051699856704979207520) * 10 ^ 70 +
        0435825294070237027247160156502276655629337756839955921719803684348344) * 10 ^ 70 +
        9804391300131829608027429225334197917733604812881614647765874367099966) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (135 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_135_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (136 + x) *
        remainder6Coefficient1.coeff (136 - (136 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 136 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (136 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (136 - (136 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_136 :
    recurrence4Scalar1Exceptional.coeff 136 =
      -((((1282425037190555471623442160596608591352281357485510 * 10 ^ 70 +
        7271367180538222065018407659441017439640034410312090019993909442709344) * 10 ^ 70 +
        3852545393502621809784599138352592536896214442420114977285762970506088) * 10 ^ 70 +
        4798882639861793101610344021211388533088720283734813208560477767514075) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (136 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_136_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (137 + x) *
        remainder6Coefficient1.coeff (137 - (137 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 137 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (137 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (137 - (137 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_137 :
    recurrence4Scalar1Exceptional.coeff 137 =
      ((((17962715843175647551693779215116977891386947900209191 * 10 ^ 70 +
        2617536036689386497116351488412492689516415935651719385209774687536725) * 10 ^ 70 +
        7345328727465827932498071574131796303310847370629294223187257357525129) * 10 ^ 70 +
        9404153584035870136883302426170555444107016011538700306224172471952031) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (137 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_137_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (138 + x) *
        remainder6Coefficient1.coeff (138 - (138 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 138 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (138 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (138 - (138 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_138 :
    recurrence4Scalar1Exceptional.coeff 138 =
      -((((157150852446745688129329538502436187789520924480396507 * 10 ^ 70 +
        0223132870287434110791199288817142914576029674392050273742695019899524) * 10 ^ 70 +
        4923068437196529922287402460519366467661828689260094543732913615479189) * 10 ^ 70 +
        5208075377510486039716987617054723817072062494056003206379735922583918) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (138 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_138_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (139 + x) *
        remainder6Coefficient1.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 139 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (139 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (139 - (139 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_139 :
    recurrence4Scalar1Exceptional.coeff 139 =
      ((((1140634346900688173165459478204920121400751008795392905 * 10 ^ 70 +
        4462795304552584775804451824343793398223921801311455466686414626787545) * 10 ^ 70 +
        0156273590839277967791346571426452057355781745024176606630935481130779) * 10 ^ 70 +
        6292228603397399128605935598564061890761952882815072556517265066941814) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (139 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (140 + x) *
        remainder6Coefficient1.coeff (140 - (140 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 140 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (140 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (140 - (140 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_140 :
    recurrence4Scalar1Exceptional.coeff 140 =
      -((((7371265252994471995777842973365886193524996391831234866 * 10 ^ 70 +
        8245801406569633277543872822642042267522775562905016189764392132276644) * 10 ^ 70 +
        4767234652695766613891279495997691752917640018551608112843116600009811) * 10 ^ 70 +
        6262090385356154464424437297238604212355897153355960207291515996965462) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (140 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (141 + x) *
        remainder6Coefficient1.coeff (141 - (141 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 141 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (141 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (141 - (141 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_141 :
    recurrence4Scalar1Exceptional.coeff 141 =
      ((((43532952463073656352384638670535574393241115390402258320 * 10 ^ 70 +
        4309243801454787443153696780741882080904317478192819734232554292928950) * 10 ^ 70 +
        4648092093885179100960777240329657570473012039963710309274957695621570) * 10 ^ 70 +
        6634714137262753708302233831619766423791621928323157787254540318350456) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (141 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (142 + x) *
        remainder6Coefficient1.coeff (142 - (142 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 142 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (142 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (142 - (142 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_142 :
    recurrence4Scalar1Exceptional.coeff 142 =
      -((((237015504611310398822616910511929745138965237847538274277 * 10 ^ 70 +
        8553455215384547877368720997561345398035944551765174314813603187946508) * 10 ^ 70 +
        2998439413586360566393362244675617855572181108051462381431481606230611) * 10 ^ 70 +
        9441715266081179509707029614757336543785574378485556242565463716855735) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (142 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (143 + x) *
        remainder6Coefficient1.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 143 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (143 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (143 - (143 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_143 :
    recurrence4Scalar1Exceptional.coeff 143 =
      ((((1186722809394812736173823713823188326681431565502476915045 * 10 ^ 70 +
        8583423586768751612372808990240445486255889025149462495005734890267283) * 10 ^ 70 +
        2052452506144004868458727146351580138102004231857757326547722097807305) * 10 ^ 70 +
        2827502174098333495718070588667367440752415855335301479093308199466333) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (143 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (144 + x) *
        remainder6Coefficient1.coeff (144 - (144 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 144 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (144 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (144 - (144 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_144 :
    recurrence4Scalar1Exceptional.coeff 144 =
      -((((5378438054849300415384889403863657070535818441120536672839 * 10 ^ 70 +
        6855995456791194977598153581217506300785303534819485586927978610131206) * 10 ^ 70 +
        3260847334594515058836976636626191663690931555572608122265481419148329) * 10 ^ 70 +
        7379659374534084170081650114726136105982538560899462013812662451776036) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (144 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (145 + x) *
        remainder6Coefficient1.coeff (145 - (145 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 145 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (145 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (145 - (145 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_145 :
    recurrence4Scalar1Exceptional.coeff 145 =
      ((((21119263299428291536139589689462425931293552227053156492639 * 10 ^ 70 +
        7600905463774078236881228845237066871253332700244357120467000169933425) * 10 ^ 70 +
        6940966749350211185401141445870149833206533712367406919419627603789841) * 10 ^ 70 +
        6068160302004028719871120191617022323530734761519488912009480284713352) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (145 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (146 + x) *
        remainder6Coefficient1.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 146 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (146 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (146 - (146 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_146 :
    recurrence4Scalar1Exceptional.coeff 146 =
      -((((62355283065940758021752740717151987475474171012415478656199 * 10 ^ 70 +
        5576293102249682755810007604081678599421541936346602662802732846318554) * 10 ^ 70 +
        3506710330963837081922554171248611573158332900596684811437148443605375) * 10 ^ 70 +
        2422691660111849282062584358141022193413968189273701590373123243861814) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (146 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (147 + x) *
        remainder6Coefficient1.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 147 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (147 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (147 - (147 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_147 :
    recurrence4Scalar1Exceptional.coeff 147 =
      ((((34328365733309064616579188573176520365896319267424100503108 * 10 ^ 70 +
        6528842318192892644395071027262126286506762857535370210054572534364395) * 10 ^ 70 +
        1480605426023201941750384314844255450117879066116698022730327495438646) * 10 ^ 70 +
        1824821195400532672218949065192617665347801958151868701270263437088206) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (147 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (148 + x) *
        remainder6Coefficient1.coeff (148 - (148 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 148 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (148 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (148 - (148 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_148 :
    recurrence4Scalar1Exceptional.coeff 148 =
      ((((1435617824278093101915309091813767825229142323142696773765225 * 10 ^ 70 +
        8893309552541309359372943742058541406009092410241894266961540501059427) * 10 ^ 70 +
        3818421600826203247631783940385191110054877191246661275807694490853147) * 10 ^ 70 +
        8464407589476251380003759965861115477140550005722045877216097305848379) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (148 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (149 + x) *
        remainder6Coefficient1.coeff (149 - (149 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 149 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (149 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (149 - (149 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_149 :
    recurrence4Scalar1Exceptional.coeff 149 =
      -((((15765816224086570205089023553514313062457642994811353076697973 * 10 ^ 70 +
        5407284644937354674252276283536732446389323520103865112849044023799979) * 10 ^ 70 +
        7613154605929046141876503947561134473664697394457713605874277453594466) * 10 ^ 70 +
        5091435669344561277012363257712009122032763954132016661174822703301120) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (149 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (150 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (150 + x) *
        remainder6Coefficient1.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 150 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (150 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (150 - (150 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_150 :
    recurrence4Scalar1Exceptional.coeff 150 =
      ((((121504642005489335709470239956838393360007486648926893634743722 * 10 ^ 70 +
        5587086733942778060843613052267083237627690730860868662026781729568504) * 10 ^ 70 +
        4020953631978592890887094978420488045738373415721291035616320596501532) * 10 ^ 70 +
        6645554543749792201795689673235734735737033247001613349121221847559163) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (150 - x)) = _
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
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (151 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (151 + x) *
        remainder6Coefficient1.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 151 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (151 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (151 - (151 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_151 :
    recurrence4Scalar1Exceptional.coeff 151 =
      -((((804792101141946188129646808439367161205111222929281088659411534 * 10 ^ 70 +
        4256236036872346961378337548456098810671137742794298545435459771514842) * 10 ^ 70 +
        4348086018607836063469928537072344816385224192137528339374449153588481) * 10 ^ 70 +
        5133868191274334846842797242049618730153595068779955578770966459009116) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (151 - x)) = _
  rw [show 152 = 2 +
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
  rw [recurrence4Scalar1Exceptional_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (152 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (152 + x) *
        remainder6Coefficient1.coeff (152 - (152 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 152 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (152 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (152 - (152 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_152 :
    recurrence4Scalar1Exceptional.coeff 152 =
      ((((4865205121591743143098366071791843169060500541202247239203987956 * 10 ^ 70 +
        3399778087508616827821922859574518598231554064388672729603596376706867) * 10 ^ 70 +
        1485558481196690105115637931524326396709623845119914977143986914163744) * 10 ^ 70 +
        8866965722780542304541723666443942166586687707742952152833003599482718) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (152 - x)) = _
  rw [show 153 = 3 +
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
  rw [recurrence4Scalar1Exceptional_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (153 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (153 + x) *
        remainder6Coefficient1.coeff (153 - (153 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 153 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (153 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (153 - (153 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_153 :
    recurrence4Scalar1Exceptional.coeff 153 =
      -((((27562093847918901633552220768171711148090432731796984027204809427 * 10 ^ 70 +
        2210178516996361841206128345879317580066805703679470330368067608204082) * 10 ^ 70 +
        5338629579852955810455620691745743248824821980991519979461065980178959) * 10 ^ 70 +
        6269048105618944326573641435122302182670269367267430495632611454228316) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (153 - x)) = _
  rw [show 154 = 4 +
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
  rw [recurrence4Scalar1Exceptional_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (154 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (154 + x) *
        remainder6Coefficient1.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 154 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (154 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (154 - (154 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_154 :
    recurrence4Scalar1Exceptional.coeff 154 =
      ((((148402894620124370442853597801874759545297241278674404142522457813 * 10 ^ 70 +
        8412018236585500778203132298646026277940876898494517314084653566197883) * 10 ^ 70 +
        9838170621037911290984762786058295151629953184609773353509054593882798) * 10 ^ 70 +
        9323864032011724525492651037859213782371155762014026955350566877776932) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (154 - x)) = _
  rw [show 155 = 5 +
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
  rw [recurrence4Scalar1Exceptional_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (155 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (155 + x) *
        remainder6Coefficient1.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 155 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (155 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (155 - (155 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_155 :
    recurrence4Scalar1Exceptional.coeff 155 =
      -((((765925013099367045002368000620731003601096624218374647631539089455 * 10 ^ 70 +
        4207248865670761920410435201059127929882732834617720688560297305679809) * 10 ^ 70 +
        7327432896660970444065303057191334572255809256382474320992869322758356) * 10 ^ 70 +
        4723080736080561036532265851587278386795471454801275228974643889196231) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (155 - x)) = _
  rw [show 156 = 6 +
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
  rw [recurrence4Scalar1Exceptional_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (156 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (156 + x) *
        remainder6Coefficient1.coeff (156 - (156 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 156 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (156 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (156 - (156 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_156 :
    recurrence4Scalar1Exceptional.coeff 156 =
      ((((3810365210365080466886745278451623624612409039256792258673474942947 * 10 ^ 70 +
        2217809494068921731465146159257953992532470790946032857277739231263823) * 10 ^ 70 +
        3555919980708162316746350987825514113301544362297599225348311220918156) * 10 ^ 70 +
        1723214179585080913172092167948653301620896452939075176525676791802777) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (156 - x)) = _
  rw [show 157 = 7 +
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
  rw [recurrence4Scalar1Exceptional_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (157 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (157 + x) *
        remainder6Coefficient1.coeff (157 - (157 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 157 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (157 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (157 - (157 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_157 :
    recurrence4Scalar1Exceptional.coeff 157 =
      -((((18343102694224978564568467738304985777609778459652345841585964482007 * 10 ^ 70 +
        3562957849595887604608865573666351182175657848535825943417421502938935) * 10 ^ 70 +
        9371871289758654358285908753452330394195012515312719703424588697202600) * 10 ^ 70 +
        2319840275811685049515207249682978478039458914727633976596514829088930) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (157 - x)) = _
  rw [show 158 = 8 +
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
  rw [recurrence4Scalar1Exceptional_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (158 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (158 + x) *
        remainder6Coefficient1.coeff (158 - (158 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 158 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (158 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (158 - (158 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_158 :
    recurrence4Scalar1Exceptional.coeff 158 =
      ((((85691882589311803681469828877748868451897537917943249559795582486703 * 10 ^ 70 +
        2801812362248179755800934574794202111869433610298061817615062970245957) * 10 ^ 70 +
        2906015450149601917526979676525722713326366562886967153191763295399884) * 10 ^ 70 +
        5413158577102656135176915572973622209150461087882393818418894282933837) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (158 - x)) = _
  rw [show 159 = 9 +
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
  rw [recurrence4Scalar1Exceptional_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (159 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (159 + x) *
        remainder6Coefficient1.coeff (159 - (159 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 159 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (159 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (159 - (159 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_159 :
    recurrence4Scalar1Exceptional.coeff 159 =
      -((((389317770599707014603658159197538089667094701019729211358288456470268 * 10 ^ 70 +
        4851445431221776952358781354666889677634855997454761067970172576943343) * 10 ^ 70 +
        1157265052042885091384294274231308006178434400980007302317967254543254) * 10 ^ 70 +
        1630935544456592320109794728522824058355308688994438599893894088587897) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (159 - x)) = _
  rw [show 160 = 10 +
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
  rw [recurrence4Scalar1Exceptional_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (160 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (160 + x) *
        remainder6Coefficient1.coeff (160 - (160 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 160 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (160 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (160 - (160 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_160 :
    recurrence4Scalar1Exceptional.coeff 160 =
      ((((1723055466808578683875011932880412869384909124624580713890137868754521 * 10 ^ 70 +
        9717851091396894447876647084647528098208865013017110651003684244382590) * 10 ^ 70 +
        2974548258554826909583850106701539142428861493058764063366771102462204) * 10 ^ 70 +
        2861359619665126645057575039006180430063864728429764792689133586505819) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (160 - x)) = _
  rw [show 161 = 11 +
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
  rw [recurrence4Scalar1Exceptional_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
